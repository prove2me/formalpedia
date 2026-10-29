-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1509_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:54:56.733282+00:00
-- url     : https://prove2.me/submissions/ff94cada-d6dc-4f4e-9d45-f1d45dd11ffa

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
theorem support_rectangle_w1509_s3_0 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-467985469/2500000000 : ℝ)*x 0 + (271850693/500000000 : ℝ)*x 1 + (5214434831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (467985469/2500000000 : ℝ)^4515 ≤ (11450831146793/100000000000000 : ℝ)^3491 := by
    have hnat : (467985469 : ℕ)^4515*100000000000000^3491 ≤ 11450831146793^3491*2500000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467985469 2500000000 11450831146793 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271850693/500000000 : ℝ)^4515 ≤ (45471036858463/100000000000000 : ℝ)^3491 := by
    have hnat : (271850693 : ℕ)^4515*100000000000000^3491 ≤ 45471036858463^3491*500000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271850693 500000000 45471036858463 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5214434831/10000000000 : ℝ)^4515 ≤ (21539065992153/50000000000000 : ℝ)^3491 := by
    have hnat : (5214434831 : ℕ)^4515*50000000000000^3491 ≤ 21539065992153^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214434831 10000000000 21539065992153 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-467985469/2500000000 : ℝ), (271850693/500000000 : ℝ), (5214434831/10000000000 : ℝ)] ![(11450831146793/100000000000000 : ℝ), (45471036858463/100000000000000 : ℝ), (21539065992153/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-467985469/2500000000 : ℝ)|^4515 ≤ (11450831146793/100000000000000 : ℝ)^3491
        have hw : |(-467985469/2500000000 : ℝ)|=(467985469/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(271850693/500000000 : ℝ)|^4515 ≤ (45471036858463/100000000000000 : ℝ)^3491
        have hw : |(271850693/500000000 : ℝ)|=(271850693/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5214434831/10000000000 : ℝ)|^4515 ≤ (21539065992153/50000000000000 : ℝ)^3491
        have hw : |(5214434831/10000000000 : ℝ)|=(5214434831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s3_1 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676321731/5000000000 : ℝ)*x 0 + (-1986023651/10000000000 : ℝ)*x 1 + (2607217391/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676321731/5000000000 : ℝ)^4515 ≤ (2228026916733/5000000000000 : ℝ)^3491 := by
    have hnat : (2676321731 : ℕ)^4515*5000000000000^3491 ≤ 2228026916733^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676321731 5000000000 2228026916733 5000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1986023651/10000000000 : ℝ)^4515 ≤ (6180665095417/50000000000000 : ℝ)^3491 := by
    have hnat : (1986023651 : ℕ)^4515*50000000000000^3491 ≤ 6180665095417^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1986023651 10000000000 6180665095417 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2607217391/5000000000 : ℝ)^4515 ≤ (43078131460761/100000000000000 : ℝ)^3491 := by
    have hnat : (2607217391 : ℕ)^4515*100000000000000^3491 ≤ 43078131460761^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607217391 5000000000 43078131460761 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676321731/5000000000 : ℝ), (-1986023651/10000000000 : ℝ), (2607217391/5000000000 : ℝ)] ![(2228026916733/5000000000000 : ℝ), (6180665095417/50000000000000 : ℝ), (43078131460761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676321731/5000000000 : ℝ)|^4515 ≤ (2228026916733/5000000000000 : ℝ)^3491
        have hw : |(2676321731/5000000000 : ℝ)|=(2676321731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1986023651/10000000000 : ℝ)|^4515 ≤ (6180665095417/50000000000000 : ℝ)^3491
        have hw : |(-1986023651/10000000000 : ℝ)|=(1986023651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2607217391/5000000000 : ℝ)|^4515 ≤ (43078131460761/100000000000000 : ℝ)^3491
        have hw : |(2607217391/5000000000 : ℝ)|=(2607217391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s3_2 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676321721/5000000000 : ℝ)*x 0 + (521443481/1000000000 : ℝ)*x 1 + (-49650591/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676321721/5000000000 : ℝ)^4515 ≤ (22280269059661/50000000000000 : ℝ)^3491 := by
    have hnat : (2676321721 : ℕ)^4515*50000000000000^3491 ≤ 22280269059661^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676321721 5000000000 22280269059661 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521443481/1000000000 : ℝ)^4515 ≤ (4307813175993/10000000000000 : ℝ)^3491 := by
    have hnat : (521443481 : ℕ)^4515*10000000000000^3491 ≤ 4307813175993^3491*1000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521443481 1000000000 4307813175993 10000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (49650591/250000000 : ℝ)^4515 ≤ (6180665051143/50000000000000 : ℝ)^3491 := by
    have hnat : (49650591 : ℕ)^4515*50000000000000^3491 ≤ 6180665051143^3491*250000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49650591 250000000 6180665051143 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676321721/5000000000 : ℝ), (521443481/1000000000 : ℝ), (-49650591/250000000 : ℝ)] ![(22280269059661/50000000000000 : ℝ), (4307813175993/10000000000000 : ℝ), (6180665051143/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676321721/5000000000 : ℝ)|^4515 ≤ (22280269059661/50000000000000 : ℝ)^3491
        have hw : |(2676321721/5000000000 : ℝ)|=(2676321721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521443481/1000000000 : ℝ)|^4515 ≤ (4307813175993/10000000000000 : ℝ)^3491
        have hw : |(521443481/1000000000 : ℝ)|=(521443481/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-49650591/250000000 : ℝ)|^4515 ≤ (6180665051143/50000000000000 : ℝ)^3491
        have hw : |(-49650591/250000000 : ℝ)|=(49650591/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s3_3 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1067712147/2500000000 : ℝ)*x 0 + (4025341869/10000000000 : ℝ)*x 1 + (452899189/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1067712147/2500000000 : ℝ)^4515 ≤ (6655251688109/20000000000000 : ℝ)^3491 := by
    have hnat : (1067712147 : ℕ)^4515*20000000000000^3491 ≤ 6655251688109^3491*2500000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067712147 2500000000 6655251688109 20000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4025341869/10000000000 : ℝ)^4515 ≤ (15411725779999/50000000000000 : ℝ)^3491 := by
    have hnat : (4025341869 : ℕ)^4515*50000000000000^3491 ≤ 15411725779999^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4025341869 10000000000 15411725779999 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (452899189/1000000000 : ℝ)^4515 ≤ (17950144993807/50000000000000 : ℝ)^3491 := by
    have hnat : (452899189 : ℕ)^4515*50000000000000^3491 ≤ 17950144993807^3491*1000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452899189 1000000000 17950144993807 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1067712147/2500000000 : ℝ), (4025341869/10000000000 : ℝ), (452899189/1000000000 : ℝ)] ![(6655251688109/20000000000000 : ℝ), (15411725779999/50000000000000 : ℝ), (17950144993807/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1067712147/2500000000 : ℝ)|^4515 ≤ (6655251688109/20000000000000 : ℝ)^3491
        have hw : |(1067712147/2500000000 : ℝ)|=(1067712147/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4025341869/10000000000 : ℝ)|^4515 ≤ (15411725779999/50000000000000 : ℝ)^3491
        have hw : |(4025341869/10000000000 : ℝ)|=(4025341869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(452899189/1000000000 : ℝ)|^4515 ≤ (17950144993807/50000000000000 : ℝ)^3491
        have hw : |(452899189/1000000000 : ℝ)|=(452899189/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s3_4 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-467993419/2500000000 : ℝ)*x 0 + (5215613721/10000000000 : ℝ)*x 1 + (5435825999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (467993419/2500000000 : ℝ)^4515 ≤ (2862770682371/25000000000000 : ℝ)^3491 := by
    have hnat : (467993419 : ℕ)^4515*25000000000000^3491 ≤ 2862770682371^3491*2500000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467993419 2500000000 2862770682371 25000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215613721/10000000000 : ℝ)^4515 ≤ (21545364174229/50000000000000 : ℝ)^3491 := by
    have hnat : (5215613721 : ℕ)^4515*50000000000000^3491 ≤ 21545364174229^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215613721 10000000000 21545364174229 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5435825999/10000000000 : ℝ)^4515 ≤ (5682273612847/12500000000000 : ℝ)^3491 := by
    have hnat : (5435825999 : ℕ)^4515*12500000000000^3491 ≤ 5682273612847^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435825999 10000000000 5682273612847 12500000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-467993419/2500000000 : ℝ), (5215613721/10000000000 : ℝ), (5435825999/10000000000 : ℝ)] ![(2862770682371/25000000000000 : ℝ), (21545364174229/50000000000000 : ℝ), (5682273612847/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-467993419/2500000000 : ℝ)|^4515 ≤ (2862770682371/25000000000000 : ℝ)^3491
        have hw : |(-467993419/2500000000 : ℝ)|=(467993419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215613721/10000000000 : ℝ)|^4515 ≤ (21545364174229/50000000000000 : ℝ)^3491
        have hw : |(5215613721/10000000000 : ℝ)|=(5215613721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5435825999/10000000000 : ℝ)|^4515 ≤ (5682273612847/12500000000000 : ℝ)^3491
        have hw : |(5435825999/10000000000 : ℝ)|=(5435825999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s3_5 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294238583/10000000000 : ℝ)*x 0 + (-882316237/5000000000 : ℝ)*x 1 + (5435826073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294238583/10000000000 : ℝ)^4515 ≤ (43932708727683/100000000000000 : ℝ)^3491 := by
    have hnat : (5294238583 : ℕ)^4515*100000000000000^3491 ≤ 43932708727683^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294238583 10000000000 43932708727683 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (882316237/5000000000 : ℝ)^4515 ≤ (5304550778389/50000000000000 : ℝ)^3491 := by
    have hnat : (882316237 : ℕ)^4515*50000000000000^3491 ≤ 5304550778389^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      882316237 5000000000 5304550778389 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5435826073/10000000000 : ℝ)^4515 ≤ (45458189703137/100000000000000 : ℝ)^3491 := by
    have hnat : (5435826073 : ℕ)^4515*100000000000000^3491 ≤ 45458189703137^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435826073 10000000000 45458189703137 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294238583/10000000000 : ℝ), (-882316237/5000000000 : ℝ), (5435826073/10000000000 : ℝ)] ![(43932708727683/100000000000000 : ℝ), (5304550778389/50000000000000 : ℝ), (45458189703137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294238583/10000000000 : ℝ)|^4515 ≤ (43932708727683/100000000000000 : ℝ)^3491
        have hw : |(5294238583/10000000000 : ℝ)|=(5294238583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-882316237/5000000000 : ℝ)|^4515 ≤ (5304550778389/50000000000000 : ℝ)^3491
        have hw : |(-882316237/5000000000 : ℝ)|=(882316237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5435826073/10000000000 : ℝ)|^4515 ≤ (45458189703137/100000000000000 : ℝ)^3491
        have hw : |(5435826073/10000000000 : ℝ)|=(5435826073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s3_6 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058847737/2000000000 : ℝ)*x 0 + (135895649/250000000 : ℝ)*x 1 + (-176463249/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058847737/2000000000 : ℝ)^4515 ≤ (5491588727797/12500000000000 : ℝ)^3491 := by
    have hnat : (1058847737 : ℕ)^4515*12500000000000^3491 ≤ 5491588727797^3491*2000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058847737 2000000000 5491588727797 12500000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135895649/250000000 : ℝ)^4515 ≤ (11364547120241/25000000000000 : ℝ)^3491 := by
    have hnat : (135895649 : ℕ)^4515*25000000000000^3491 ≤ 11364547120241^3491*250000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135895649 250000000 11364547120241 25000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (176463249/1000000000 : ℝ)^4515 ≤ (2652275420297/25000000000000 : ℝ)^3491 := by
    have hnat : (176463249 : ℕ)^4515*25000000000000^3491 ≤ 2652275420297^3491*1000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176463249 1000000000 2652275420297 25000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058847737/2000000000 : ℝ), (135895649/250000000 : ℝ), (-176463249/1000000000 : ℝ)] ![(5491588727797/12500000000000 : ℝ), (11364547120241/25000000000000 : ℝ), (2652275420297/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058847737/2000000000 : ℝ)|^4515 ≤ (5491588727797/12500000000000 : ℝ)^3491
        have hw : |(1058847737/2000000000 : ℝ)|=(1058847737/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(135895649/250000000 : ℝ)|^4515 ≤ (11364547120241/25000000000000 : ℝ)^3491
        have hw : |(135895649/250000000 : ℝ)|=(135895649/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-176463249/1000000000 : ℝ)|^4515 ≤ (2652275420297/25000000000000 : ℝ)^3491
        have hw : |(-176463249/1000000000 : ℝ)|=(176463249/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s3_7 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (170836819/400000000 : ℝ)*x 0 + (4526324363/10000000000 : ℝ)*x 1 + (805605921/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (170836819/400000000 : ℝ)^4515 ≤ (33276982842563/100000000000000 : ℝ)^3491 := by
    have hnat : (170836819 : ℕ)^4515*100000000000000^3491 ≤ 33276982842563^3491*400000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170836819 400000000 33276982842563 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4526324363/10000000000 : ℝ)^4515 ≤ (17936472566427/50000000000000 : ℝ)^3491 := by
    have hnat : (4526324363 : ℕ)^4515*50000000000000^3491 ≤ 17936472566427^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4526324363 10000000000 17936472566427 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (805605921/2000000000 : ℝ)^4515 ≤ (15425036009297/50000000000000 : ℝ)^3491 := by
    have hnat : (805605921 : ℕ)^4515*50000000000000^3491 ≤ 15425036009297^3491*2000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      805605921 2000000000 15425036009297 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(170836819/400000000 : ℝ), (4526324363/10000000000 : ℝ), (805605921/2000000000 : ℝ)] ![(33276982842563/100000000000000 : ℝ), (17936472566427/50000000000000 : ℝ), (15425036009297/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(170836819/400000000 : ℝ)|^4515 ≤ (33276982842563/100000000000000 : ℝ)^3491
        have hw : |(170836819/400000000 : ℝ)|=(170836819/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4526324363/10000000000 : ℝ)|^4515 ≤ (17936472566427/50000000000000 : ℝ)^3491
        have hw : |(4526324363/10000000000 : ℝ)|=(4526324363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(805605921/2000000000 : ℝ)|^4515 ≤ (15425036009297/50000000000000 : ℝ)^3491
        have hw : |(805605921/2000000000 : ℝ)|=(805605921/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1509_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8156981/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2001/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (521/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (10839/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (486/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2001/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (521/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2001/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (521/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2001/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (521/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2001/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (521/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2001/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (521/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2001/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (521/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (521/5000 : ℝ) ^ (4513/1024 : ℝ) ≤ (938751229446059/20000000000000000000 : ℝ) := by
    have hpowers : (521/5000 : ℝ)^4513 ≤ (938751229446059/20000000000000000000 : ℝ)^1024 := by
      have hnat : (521 : ℕ)^4513*20000000000000000000^1024 ≤ 938751229446059^1024*5000^4513 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        521 5000 938751229446059 20000000000000000000 4513 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (521/5000 : ℝ)) (X := (938751229446059/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4513 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2001/12500 : ℝ) ^ (4513/1024 : ℝ) ≤ (249128384560981/800000000000000000 : ℝ) := by
    have hpowers : (2001/12500 : ℝ)^4513 ≤ (249128384560981/800000000000000000 : ℝ)^1024 := by
      have hnat : (2001 : ℕ)^4513*800000000000000000^1024 ≤ 249128384560981^1024*12500^4513 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001 12500 249128384560981 800000000000000000 4513 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2001/12500 : ℝ)) (X := (249128384560981/800000000000000000 : ℝ)) (by norm_num) (by norm_num) 4513 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000938751229446059/10000000000000000000 : ℝ) ≤ (5000106497493737/5000000000000000 : ℝ) ^ (4513/1024 : ℝ) := by
    have hpowers : (10000938751229446059/10000000000000000000 : ℝ)^1024 ≤ (5000106497493737/5000000000000000 : ℝ)^4513 := by
      have hnat : (10000938751229446059 : ℕ)^1024*5000000000000000^4513 ≤ 5000106497493737^4513*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000938751229446059 10000000000000000000 5000106497493737 5000000000000000 1024 4513 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000106497493737/5000000000000000 : ℝ)) (X := (10000938751229446059/10000000000000000000 : ℝ)) (by norm_num) 4513 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2500895870105433823/2500000000000000000 : ℝ) ≤ (10000812979340723/10000000000000000 : ℝ) ^ (4513/1024 : ℝ) := by
    have hpowers : (2500895870105433823/2500000000000000000 : ℝ)^1024 ≤ (10000812979340723/10000000000000000 : ℝ)^4513 := by
      have hnat : (2500895870105433823 : ℕ)^1024*10000000000000000^4513 ≤ 10000812979340723^4513*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500895870105433823 2500000000000000000 10000812979340723 10000000000000000 1024 4513 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000812979340723/10000000000000000 : ℝ)) (X := (2500895870105433823/2500000000000000000 : ℝ)) (by norm_num) 4513 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (400249128384560981/400000000000000000 : ℝ) ≤ (2500353240923493/2500000000000000 : ℝ) ^ (4513/1024 : ℝ) := by
    have hpowers : (400249128384560981/400000000000000000 : ℝ)^1024 ≤ (2500353240923493/2500000000000000 : ℝ)^4513 := by
      have hnat : (400249128384560981 : ℕ)^1024*2500000000000000^4513 ≤ 2500353240923493^4513*400000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        400249128384560981 400000000000000000 2500353240923493 2500000000000000 1024 4513 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500353240923493/2500000000000000 : ℝ)) (X := (400249128384560981/400000000000000000 : ℝ)) (by norm_num) 4513 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(938751229446059/20000000000000000000 : ℝ) ≤ ((436474113609908559/436562500000000000 : ℝ)+2*(599984353249/558800000000000 : ℝ)*(521/5000 : ℝ))^(4513/1024 : ℝ) := by
    rw [show (436474113609908559/436562500000000000 : ℝ)+2*(599984353249/558800000000000 : ℝ)*(521/5000 : ℝ)=(5000106497493737/5000000000000000 : ℝ) by norm_num, show 1+2*(938751229446059/20000000000000000000 : ℝ)=(10000938751229446059/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(249128384560981/800000000000000000 : ℝ)+(938751229446059/20000000000000000000 : ℝ) ≤ ((436474113609908559/436562500000000000 : ℝ)+(599984353249/558800000000000 : ℝ)*((2001/12500 : ℝ)+(521/5000 : ℝ)))^(4513/1024 : ℝ) := by
    rw [show (436474113609908559/436562500000000000 : ℝ)+(599984353249/558800000000000 : ℝ)*((2001/12500 : ℝ)+(521/5000 : ℝ))=(10000812979340723/10000000000000000 : ℝ) by norm_num, show 1+(249128384560981/800000000000000000 : ℝ)+(938751229446059/20000000000000000000 : ℝ)=(2500895870105433823/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(249128384560981/800000000000000000 : ℝ) ≤ ((436474113609908559/436562500000000000 : ℝ)+2*(599984353249/558800000000000 : ℝ)*(2001/12500 : ℝ))^(4513/1024 : ℝ) := by
    rw [show (436474113609908559/436562500000000000 : ℝ)+2*(599984353249/558800000000000 : ℝ)*(2001/12500 : ℝ)=(2500353240923493/2500000000000000 : ℝ) by norm_num, show 1+2*(249128384560981/800000000000000000 : ℝ)=(400249128384560981/400000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (436474113609908559/436562500000000000 : ℝ)*(X 1 0+X 2 0)+(599984353249/558800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4513/1024 : ℝ)) (lo := (521/5000 : ℝ)) (hi := (2001/12500 : ℝ)) (c := (436474113609908559/436562500000000000 : ℝ)) (alpha := (599984353249/558800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (436474113609908559/436562500000000000 : ℝ)*(X 0 1+X 2 1)+(599984353249/558800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4513/1024 : ℝ)) (lo := (521/5000 : ℝ)) (hi := (2001/12500 : ℝ)) (c := (436474113609908559/436562500000000000 : ℝ)) (alpha := (599984353249/558800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (436474113609908559/436562500000000000 : ℝ)*(X 0 2+X 1 2)+(599984353249/558800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4513/1024 : ℝ)) (lo := (521/5000 : ℝ)) (hi := (2001/12500 : ℝ)) (c := (436474113609908559/436562500000000000 : ℝ)) (alpha := (599984353249/558800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-467985469/2500000000 : ℝ)*X 0 0+(271850693/500000000 : ℝ)*X 0 1+(5214434831/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676321731/5000000000 : ℝ)*X 1 0+(-1986023651/10000000000 : ℝ)*X 1 1+(2607217391/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676321721/5000000000 : ℝ)*X 2 0+(521443481/1000000000 : ℝ)*X 2 1+(-49650591/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1067712147/2500000000 : ℝ)*X 0 0+(4025341869/10000000000 : ℝ)*X 0 1+(452899189/1000000000 : ℝ)*X 0 2+(1067712147/2500000000 : ℝ)*X 1 0+(4025341869/10000000000 : ℝ)*X 1 1+(452899189/1000000000 : ℝ)*X 1 2+(1067712147/2500000000 : ℝ)*X 2 0+(4025341869/10000000000 : ℝ)*X 2 1+(452899189/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-467993419/2500000000 : ℝ)*X 0 0+(5215613721/10000000000 : ℝ)*X 0 1+(5435825999/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294238583/10000000000 : ℝ)*X 1 0+(-882316237/5000000000 : ℝ)*X 1 1+(5435826073/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1058847737/2000000000 : ℝ)*X 2 0+(135895649/250000000 : ℝ)*X 2 1+(-176463249/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((170836819/400000000 : ℝ)*X 0 0+(4526324363/10000000000 : ℝ)*X 0 1+(805605921/2000000000 : ℝ)*X 0 2+(170836819/400000000 : ℝ)*X 1 0+(4526324363/10000000000 : ℝ)*X 1 1+(805605921/2000000000 : ℝ)*X 1 2+(170836819/400000000 : ℝ)*X 2 0+(4526324363/10000000000 : ℝ)*X 2 1+(805605921/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (147736614893538310720206777/21828125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (155254653/12500000000000 : ℝ)*(base19) + (8696631/781250000000 : ℝ)*(base23) + (14998261/25000000000000 : ℝ)*(lower2) + (164932779/100000000000000 : ℝ)*(upper3) + (17868179/20000000000000 : ℝ)*(upper5) + (404896647066201/12500000000000 : ℝ)*(major0) + (404896647066201/12500000000000 : ℝ)*(major1) + (404896647066201/12500000000000 : ℝ)*(major2) + (2246402821911269/50000000000000 : ℝ)*(sp0) + (1123205701323141/25000000000000 : ℝ)*(sp1) + (224641146708051/5000000000000 : ℝ)*(sp2) + (397102662084877/20000000000000 : ℝ)*(sp3) + (18403507251/100000000000000 : ℝ)*(sp4) + (137026549/1562500000000 : ℝ)*(sp7) + (1985522080123521/100000000000000 : ℝ)*(f.failure) + (1123206011832447/25000000000000 : ℝ)*(f.sum) + (2896172353831/3492500000000000000000000000 : ℝ)*base66 + (80515048520585561/21828125000000000000000000000000 : ℝ)*base67 + (2006241755149367/2728515625000000000000000000000 : ℝ)*base69 + (70117200134523061/21828125000000000000000000000000 : ℝ)*base71 + (21245243912633/6985000000000000000000000000 : ℝ)*base73 + (26817284889054311/21828125000000000000000000000000 : ℝ)*base75 + (74849226103523061/21828125000000000000000000000000 : ℝ)*base77 + (22320495219461867/2728515625000000000000000000000 : ℝ)*base79 + (29947708997/436562500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1549899/500000000000000000000 : ℝ)*base90 + (1549899/500000000000000000000 : ℝ)*base92 + (1549899/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (32433098125444670942228817/5457031250000000000000000000000 : ℝ) := by norm_num
    linear_combination (452591121/50000000000000 : ℝ)*(base19) + (217259331/20000000000000 : ℝ)*(base23) + (32323727/25000000000000 : ℝ)*(upper3) + (41025701/100000000000000 : ℝ)*(lower4) + (113830751/100000000000000 : ℝ)*(upper5) + (1636979218347233/50000000000000 : ℝ)*(major0) + (1636979218347233/50000000000000 : ℝ)*(major1) + (1636979218347233/50000000000000 : ℝ)*(major2) + (3584715823/25000000000000 : ℝ)*(sp1) + (15801388023/100000000000000 : ℝ)*(sp2) + (2270536104371511/50000000000000 : ℝ)*(sp4) + (4541056964697487/100000000000000 : ℝ)*(sp5) + (2270527660529171/50000000000000 : ℝ)*(sp6) + (2006844466533921/100000000000000 : ℝ)*(sp7) + (2006844466533921/100000000000000 : ℝ)*(f.failure) + (2270536104371511/50000000000000 : ℝ)*(f.sum) + (32208250576107/13970000000000000000000000000 : ℝ)*base65 + (55620774221340387/87312500000000000000000000000000 : ℝ)*base68 + (587819973171715387/87312500000000000000000000000000 : ℝ)*base70 + (403027587237722113/87312500000000000000000000000000 : ℝ)*base71 + (31846961369807/13970000000000000000000000000 : ℝ)*base73 + (246662966325222113/87312500000000000000000000000000 : ℝ)*base75 + (566082143327284613/87312500000000000000000000000000 : ℝ)*base77 + (1528207536970159613/87312500000000000000000000000000 : ℝ)*base79 + (27959034882833/13970000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/50000000000000 : ℝ)*base88 + (547499/500000000000000000000 : ℝ)*base90 + (547499/500000000000000000000 : ℝ)*base92 + (547499/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1509_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8156981/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2001/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (521/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10839/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (486/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1509_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1509_s4_0 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1872395589/10000000000 : ℝ)*x 0 + (5434038127/10000000000 : ℝ)*x 1 + (2608555433/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1872395589/10000000000 : ℝ)^4515 ≤ (11454420772913/100000000000000 : ℝ)^3491 := by
    have hnat : (1872395589 : ℕ)^4515*100000000000000^3491 ≤ 11454420772913^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1872395589 10000000000 11454420772913 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5434038127/10000000000 : ℝ)^4515 ≤ (45438852754863/100000000000000 : ℝ)^3491 := by
    have hnat : (5434038127 : ℕ)^4515*100000000000000^3491 ≤ 45438852754863^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434038127 10000000000 45438852754863 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608555433/5000000000 : ℝ)^4515 ≤ (21553363225347/50000000000000 : ℝ)^3491 := by
    have hnat : (2608555433 : ℕ)^4515*50000000000000^3491 ≤ 21553363225347^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608555433 5000000000 21553363225347 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1872395589/10000000000 : ℝ), (5434038127/10000000000 : ℝ), (2608555433/5000000000 : ℝ)] ![(11454420772913/100000000000000 : ℝ), (45438852754863/100000000000000 : ℝ), (21553363225347/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1872395589/10000000000 : ℝ)|^4515 ≤ (11454420772913/100000000000000 : ℝ)^3491
        have hw : |(-1872395589/10000000000 : ℝ)|=(1872395589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5434038127/10000000000 : ℝ)|^4515 ≤ (45438852754863/100000000000000 : ℝ)^3491
        have hw : |(5434038127/10000000000 : ℝ)|=(5434038127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608555433/5000000000 : ℝ)|^4515 ≤ (21553363225347/50000000000000 : ℝ)^3491
        have hw : |(2608555433/5000000000 : ℝ)|=(2608555433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s4_1 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070373103/2000000000 : ℝ)*x 0 + (-991755811/5000000000 : ℝ)*x 1 + (5217110739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070373103/2000000000 : ℝ)^4515 ≤ (111380406121/250000000000 : ℝ)^3491 := by
    have hnat : (1070373103 : ℕ)^4515*250000000000^3491 ≤ 111380406121^3491*2000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070373103 2000000000 111380406121 250000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (991755811/5000000000 : ℝ)^4515 ≤ (3085278111051/25000000000000 : ℝ)^3491 := by
    have hnat : (991755811 : ℕ)^4515*25000000000000^3491 ≤ 3085278111051^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      991755811 5000000000 3085278111051 25000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217110739/10000000000 : ℝ)^4515 ≤ (10776681273387/25000000000000 : ℝ)^3491 := by
    have hnat : (5217110739 : ℕ)^4515*25000000000000^3491 ≤ 10776681273387^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217110739 10000000000 10776681273387 25000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070373103/2000000000 : ℝ), (-991755811/5000000000 : ℝ), (5217110739/10000000000 : ℝ)] ![(111380406121/250000000000 : ℝ), (3085278111051/25000000000000 : ℝ), (10776681273387/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070373103/2000000000 : ℝ)|^4515 ≤ (111380406121/250000000000 : ℝ)^3491
        have hw : |(1070373103/2000000000 : ℝ)|=(1070373103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-991755811/5000000000 : ℝ)|^4515 ≤ (3085278111051/25000000000000 : ℝ)^3491
        have hw : |(-991755811/5000000000 : ℝ)|=(991755811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217110739/10000000000 : ℝ)|^4515 ≤ (10776681273387/25000000000000 : ℝ)^3491
        have hw : |(5217110739/10000000000 : ℝ)|=(5217110739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s4_2 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (21407461/40000000 : ℝ)*x 0 + (2608555457/5000000000 : ℝ)*x 1 + (-30992371/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21407461/40000000 : ℝ)^4515 ≤ (44552159595297/100000000000000 : ℝ)^3491 := by
    have hnat : (21407461 : ℕ)^4515*100000000000000^3491 ≤ 44552159595297^3491*40000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21407461 40000000 44552159595297 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608555457/5000000000 : ℝ)^4515 ≤ (43106726963631/100000000000000 : ℝ)^3491 := by
    have hnat : (2608555457 : ℕ)^4515*100000000000000^3491 ≤ 43106726963631^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608555457 5000000000 43106726963631 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (30992371/156250000 : ℝ)^4515 ≤ (12341113425923/100000000000000 : ℝ)^3491 := by
    have hnat : (30992371 : ℕ)^4515*100000000000000^3491 ≤ 12341113425923^3491*156250000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30992371 156250000 12341113425923 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21407461/40000000 : ℝ), (2608555457/5000000000 : ℝ), (-30992371/156250000 : ℝ)] ![(44552159595297/100000000000000 : ℝ), (43106726963631/100000000000000 : ℝ), (12341113425923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21407461/40000000 : ℝ)|^4515 ≤ (44552159595297/100000000000000 : ℝ)^3491
        have hw : |(21407461/40000000 : ℝ)|=(21407461/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608555457/5000000000 : ℝ)|^4515 ≤ (43106726963631/100000000000000 : ℝ)^3491
        have hw : |(2608555457/5000000000 : ℝ)|=(2608555457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-30992371/156250000 : ℝ)|^4515 ≤ (12341113425923/100000000000000 : ℝ)^3491
        have hw : |(-30992371/156250000 : ℝ)|=(30992371/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s4_3 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2135565989/5000000000 : ℝ)*x 0 + (161268167/400000000 : ℝ)*x 1 + (2261282257/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2135565989/5000000000 : ℝ)^4515 ≤ (16639557084691/50000000000000 : ℝ)^3491 := by
    have hnat : (2135565989 : ℕ)^4515*50000000000000^3491 ≤ 16639557084691^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135565989 5000000000 16639557084691 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (161268167/400000000 : ℝ)^4515 ≤ (15443237462057/50000000000000 : ℝ)^3491 := by
    have hnat : (161268167 : ℕ)^4515*50000000000000^3491 ≤ 15443237462057^3491*400000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161268167 400000000 15443237462057 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2261282257/5000000000 : ℝ)^4515 ≤ (35834410897359/100000000000000 : ℝ)^3491 := by
    have hnat : (2261282257 : ℕ)^4515*100000000000000^3491 ≤ 35834410897359^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2261282257 5000000000 35834410897359 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2135565989/5000000000 : ℝ), (161268167/400000000 : ℝ), (2261282257/5000000000 : ℝ)] ![(16639557084691/50000000000000 : ℝ), (15443237462057/50000000000000 : ℝ), (35834410897359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2135565989/5000000000 : ℝ)|^4515 ≤ (16639557084691/50000000000000 : ℝ)^3491
        have hw : |(2135565989/5000000000 : ℝ)|=(2135565989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(161268167/400000000 : ℝ)|^4515 ≤ (15443237462057/50000000000000 : ℝ)^3491
        have hw : |(161268167/400000000 : ℝ)|=(161268167/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2261282257/5000000000 : ℝ)|^4515 ≤ (35834410897359/100000000000000 : ℝ)^3491
        have hw : |(2261282257/5000000000 : ℝ)|=(2261282257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s4_4 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1872425331/10000000000 : ℝ)*x 0 + (5218230907/10000000000 : ℝ)*x 1 + (2716454781/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1872425331/10000000000 : ℝ)^4515 ≤ (11454656090621/100000000000000 : ℝ)^3491 := by
    have hnat : (1872425331 : ℕ)^4515*100000000000000^3491 ≤ 11454656090621^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1872425331 10000000000 11454656090621 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218230907/10000000000 : ℝ)^4515 ≤ (43118695798247/100000000000000 : ℝ)^3491 := by
    have hnat : (5218230907 : ℕ)^4515*100000000000000^3491 ≤ 43118695798247^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218230907 10000000000 43118695798247 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2716454781/5000000000 : ℝ)^4515 ≤ (45426648087971/100000000000000 : ℝ)^3491 := by
    have hnat : (2716454781 : ℕ)^4515*100000000000000^3491 ≤ 45426648087971^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716454781 5000000000 45426648087971 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1872425331/10000000000 : ℝ), (5218230907/10000000000 : ℝ), (2716454781/5000000000 : ℝ)] ![(11454656090621/100000000000000 : ℝ), (43118695798247/100000000000000 : ℝ), (45426648087971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1872425331/10000000000 : ℝ)|^4515 ≤ (11454656090621/100000000000000 : ℝ)^3491
        have hw : |(-1872425331/10000000000 : ℝ)|=(1872425331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218230907/10000000000 : ℝ)|^4515 ≤ (43118695798247/100000000000000 : ℝ)^3491
        have hw : |(5218230907/10000000000 : ℝ)|=(5218230907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2716454781/5000000000 : ℝ)|^4515 ≤ (45426648087971/100000000000000 : ℝ)^3491
        have hw : |(2716454781/5000000000 : ℝ)|=(2716454781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s4_5 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (264747251/500000000 : ℝ)*x 0 + (-441928277/2500000000 : ℝ)*x 1 + (2716454779/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264747251/500000000 : ℝ)^4515 ≤ (43940290562433/100000000000000 : ℝ)^3491 := by
    have hnat : (264747251 : ℕ)^4515*100000000000000^3491 ≤ 43940290562433^3491*500000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264747251 500000000 43940290562433 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (441928277/2500000000 : ℝ)^4515 ≤ (5316530686597/50000000000000 : ℝ)^3491 := by
    have hnat : (441928277 : ℕ)^4515*50000000000000^3491 ≤ 5316530686597^3491*2500000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441928277 2500000000 5316530686597 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2716454779/5000000000 : ℝ)^4515 ≤ (9085329608943/20000000000000 : ℝ)^3491 := by
    have hnat : (2716454779 : ℕ)^4515*20000000000000^3491 ≤ 9085329608943^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716454779 5000000000 9085329608943 20000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264747251/500000000 : ℝ), (-441928277/2500000000 : ℝ), (2716454779/5000000000 : ℝ)] ![(43940290562433/100000000000000 : ℝ), (5316530686597/50000000000000 : ℝ), (9085329608943/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264747251/500000000 : ℝ)|^4515 ≤ (43940290562433/100000000000000 : ℝ)^3491
        have hw : |(264747251/500000000 : ℝ)|=(264747251/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-441928277/2500000000 : ℝ)|^4515 ≤ (5316530686597/50000000000000 : ℝ)^3491
        have hw : |(-441928277/2500000000 : ℝ)|=(441928277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2716454779/5000000000 : ℝ)|^4515 ≤ (9085329608943/20000000000000 : ℝ)^3491
        have hw : |(2716454779/5000000000 : ℝ)|=(2716454779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s4_6 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323736251/2500000000 : ℝ)*x 0 + (5432909571/10000000000 : ℝ)*x 1 + (-1767713113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323736251/2500000000 : ℝ)^4515 ≤ (43940290390709/100000000000000 : ℝ)^3491 := by
    have hnat : (1323736251 : ℕ)^4515*100000000000000^3491 ≤ 43940290390709^3491*2500000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323736251 2500000000 43940290390709 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5432909571/10000000000 : ℝ)^4515 ≤ (45426648185297/100000000000000 : ℝ)^3491 := by
    have hnat : (5432909571 : ℕ)^4515*100000000000000^3491 ≤ 45426648185297^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432909571 10000000000 45426648185297 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1767713113/10000000000 : ℝ)^4515 ≤ (2658265353023/25000000000000 : ℝ)^3491 := by
    have hnat : (1767713113 : ℕ)^4515*25000000000000^3491 ≤ 2658265353023^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1767713113 10000000000 2658265353023 25000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323736251/2500000000 : ℝ), (5432909571/10000000000 : ℝ), (-1767713113/10000000000 : ℝ)] ![(43940290390709/100000000000000 : ℝ), (45426648185297/100000000000000 : ℝ), (2658265353023/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323736251/2500000000 : ℝ)|^4515 ≤ (43940290390709/100000000000000 : ℝ)^3491
        have hw : |(1323736251/2500000000 : ℝ)|=(1323736251/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5432909571/10000000000 : ℝ)|^4515 ≤ (45426648185297/100000000000000 : ℝ)^3491
        have hw : |(5432909571/10000000000 : ℝ)|=(5432909571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1767713113/10000000000 : ℝ)|^4515 ≤ (2658265353023/25000000000000 : ℝ)^3491
        have hw : |(-1767713113/10000000000 : ℝ)|=(1767713113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s4_7 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (854239783/2000000000 : ℝ)*x 0 + (4520030121/10000000000 : ℝ)*x 1 + (4034256901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (854239783/2000000000 : ℝ)^4515 ≤ (3327978870349/10000000000000 : ℝ)^3491 := by
    have hnat : (854239783 : ℕ)^4515*10000000000000^3491 ≤ 3327978870349^3491*2000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      854239783 2000000000 3327978870349 10000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4520030121/10000000000 : ℝ)^4515 ≤ (35808441512373/100000000000000 : ℝ)^3491 := by
    have hnat : (4520030121 : ℕ)^4515*100000000000000^3491 ≤ 35808441512373^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4520030121 10000000000 35808441512373 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4034256901/10000000000 : ℝ)^4515 ≤ (15455884887269/50000000000000 : ℝ)^3491 := by
    have hnat : (4034256901 : ℕ)^4515*50000000000000^3491 ≤ 15455884887269^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4034256901 10000000000 15455884887269 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(854239783/2000000000 : ℝ), (4520030121/10000000000 : ℝ), (4034256901/10000000000 : ℝ)] ![(3327978870349/10000000000000 : ℝ), (35808441512373/100000000000000 : ℝ), (15455884887269/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(854239783/2000000000 : ℝ)|^4515 ≤ (3327978870349/10000000000000 : ℝ)^3491
        have hw : |(854239783/2000000000 : ℝ)|=(854239783/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4520030121/10000000000 : ℝ)|^4515 ≤ (35808441512373/100000000000000 : ℝ)^3491
        have hw : |(4520030121/10000000000 : ℝ)|=(4520030121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4034256901/10000000000 : ℝ)|^4515 ≤ (15455884887269/50000000000000 : ℝ)^3491
        have hw : |(4034256901/10000000000 : ℝ)|=(4034256901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1509_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8156981/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (486/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10839/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (681/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (486/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10839/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (486/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10839/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (486/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10839/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (486/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10839/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (486/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10839/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (486/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10839/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10839/100000 : ℝ) ^ (4513/1024 : ℝ) ≤ (2792214932059707/50000000000000000000 : ℝ) := by
    have hpowers : (10839/100000 : ℝ)^4513 ≤ (2792214932059707/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10839 : ℕ)^4513*50000000000000000000^1024 ≤ 2792214932059707^1024*100000^4513 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10839 100000 2792214932059707 50000000000000000000 4513 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10839/100000 : ℝ)) (X := (2792214932059707/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4513 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (486/3125 : ℝ) ^ (4513/1024 : ℝ) ≤ (1713558357574421/6250000000000000000 : ℝ) := by
    have hpowers : (486/3125 : ℝ)^4513 ≤ (1713558357574421/6250000000000000000 : ℝ)^1024 := by
      have hnat : (486 : ℕ)^4513*6250000000000000000^1024 ≤ 1713558357574421^1024*3125^4513 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        486 3125 1713558357574421 6250000000000000000 4513 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (486/3125 : ℝ)) (X := (1713558357574421/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4513 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002792214932059707/25000000000000000000 : ℝ) ≤ (5000126705280589/5000000000000000 : ℝ) ^ (4513/1024 : ℝ) := by
    have hpowers : (25002792214932059707/25000000000000000000 : ℝ)^1024 ≤ (5000126705280589/5000000000000000 : ℝ)^4513 := by
      have hnat : (25002792214932059707 : ℕ)^1024*5000000000000000^4513 ≤ 5000126705280589^4513*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002792214932059707 25000000000000000000 5000126705280589 5000000000000000 1024 4513 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000126705280589/5000000000000000 : ℝ)) (X := (25002792214932059707/25000000000000000000 : ℝ)) (by norm_num) 4513 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2000660027271706203/2000000000000000000 : ℝ) ≤ (156261698525869/156250000000000 : ℝ) ^ (4513/1024 : ℝ) := by
    have hpowers : (2000660027271706203/2000000000000000000 : ℝ)^1024 ≤ (156261698525869/156250000000000 : ℝ)^4513 := by
      have hnat : (2000660027271706203 : ℕ)^1024*156250000000000^4513 ≤ 156261698525869^4513*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000660027271706203 2000000000000000000 156261698525869 156250000000000 1024 4513 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156261698525869/156250000000000 : ℝ)) (X := (2000660027271706203/2000000000000000000 : ℝ)) (by norm_num) 4513 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3126713558357574421/3125000000000000000 : ℝ) ≤ (5000622000375027/5000000000000000 : ℝ) ^ (4513/1024 : ℝ) := by
    have hpowers : (3126713558357574421/3125000000000000000 : ℝ)^1024 ≤ (5000622000375027/5000000000000000 : ℝ)^4513 := by
      have hnat : (3126713558357574421 : ℕ)^1024*5000000000000000^4513 ≤ 5000622000375027^4513*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126713558357574421 3125000000000000000 5000622000375027 5000000000000000 1024 4513 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000622000375027/5000000000000000 : ℝ)) (X := (3126713558357574421/3125000000000000000 : ℝ)) (by norm_num) 4513 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2792214932059707/50000000000000000000 : ℝ) ≤ ((314136382112784033/314200000000000000 : ℝ)+2*(247647547219/235650000000000 : ℝ)*(10839/100000 : ℝ))^(4513/1024 : ℝ) := by
    rw [show (314136382112784033/314200000000000000 : ℝ)+2*(247647547219/235650000000000 : ℝ)*(10839/100000 : ℝ)=(5000126705280589/5000000000000000 : ℝ) by norm_num, show 1+2*(2792214932059707/50000000000000000000 : ℝ)=(25002792214932059707/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1713558357574421/6250000000000000000 : ℝ)+(2792214932059707/50000000000000000000 : ℝ) ≤ ((314136382112784033/314200000000000000 : ℝ)+(247647547219/235650000000000 : ℝ)*((486/3125 : ℝ)+(10839/100000 : ℝ)))^(4513/1024 : ℝ) := by
    rw [show (314136382112784033/314200000000000000 : ℝ)+(247647547219/235650000000000 : ℝ)*((486/3125 : ℝ)+(10839/100000 : ℝ))=(156261698525869/156250000000000 : ℝ) by norm_num, show 1+(1713558357574421/6250000000000000000 : ℝ)+(2792214932059707/50000000000000000000 : ℝ)=(2000660027271706203/2000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1713558357574421/6250000000000000000 : ℝ) ≤ ((314136382112784033/314200000000000000 : ℝ)+2*(247647547219/235650000000000 : ℝ)*(486/3125 : ℝ))^(4513/1024 : ℝ) := by
    rw [show (314136382112784033/314200000000000000 : ℝ)+2*(247647547219/235650000000000 : ℝ)*(486/3125 : ℝ)=(5000622000375027/5000000000000000 : ℝ) by norm_num, show 1+2*(1713558357574421/6250000000000000000 : ℝ)=(3126713558357574421/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (314136382112784033/314200000000000000 : ℝ)*(X 1 0+X 2 0)+(247647547219/235650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4513/1024 : ℝ)) (lo := (10839/100000 : ℝ)) (hi := (486/3125 : ℝ)) (c := (314136382112784033/314200000000000000 : ℝ)) (alpha := (247647547219/235650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (314136382112784033/314200000000000000 : ℝ)*(X 0 1+X 2 1)+(247647547219/235650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4513/1024 : ℝ)) (lo := (10839/100000 : ℝ)) (hi := (486/3125 : ℝ)) (c := (314136382112784033/314200000000000000 : ℝ)) (alpha := (247647547219/235650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (314136382112784033/314200000000000000 : ℝ)*(X 0 2+X 1 2)+(247647547219/235650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4513/1024 : ℝ)) (lo := (10839/100000 : ℝ)) (hi := (486/3125 : ℝ)) (c := (314136382112784033/314200000000000000 : ℝ)) (alpha := (247647547219/235650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1872395589/10000000000 : ℝ)*X 0 0+(5434038127/10000000000 : ℝ)*X 0 1+(2608555433/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070373103/2000000000 : ℝ)*X 1 0+(-991755811/5000000000 : ℝ)*X 1 1+(5217110739/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((21407461/40000000 : ℝ)*X 2 0+(2608555457/5000000000 : ℝ)*X 2 1+(-30992371/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2135565989/5000000000 : ℝ)*X 0 0+(161268167/400000000 : ℝ)*X 0 1+(2261282257/5000000000 : ℝ)*X 0 2+(2135565989/5000000000 : ℝ)*X 1 0+(161268167/400000000 : ℝ)*X 1 1+(2261282257/5000000000 : ℝ)*X 1 2+(2135565989/5000000000 : ℝ)*X 2 0+(161268167/400000000 : ℝ)*X 2 1+(2261282257/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1872425331/10000000000 : ℝ)*X 0 0+(5218230907/10000000000 : ℝ)*X 0 1+(2716454781/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((264747251/500000000 : ℝ)*X 1 0+(-441928277/2500000000 : ℝ)*X 1 1+(2716454779/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1323736251/2500000000 : ℝ)*X 2 0+(5432909571/10000000000 : ℝ)*X 2 1+(-1767713113/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((854239783/2000000000 : ℝ)*X 0 0+(4520030121/10000000000 : ℝ)*X 0 1+(4034256901/10000000000 : ℝ)*X 0 2+(854239783/2000000000 : ℝ)*X 1 0+(4520030121/10000000000 : ℝ)*X 1 1+(4034256901/10000000000 : ℝ)*X 1 2+(854239783/2000000000 : ℝ)*X 2 0+(4520030121/10000000000 : ℝ)*X 2 1+(4034256901/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10323675782114381318447/981875000000000000000000000 : ℝ) := by norm_num
    linear_combination (847226751/50000000000000 : ℝ)*(base19) + (705353639/50000000000000 : ℝ)*(base23) + (4287497/5000000000000 : ℝ)*(lower2) + (194608501/100000000000000 : ℝ)*(upper3) + (11211007/20000000000000 : ℝ)*(lower4) + (1661789789791499/50000000000000 : ℝ)*(major0) + (1661789789791499/50000000000000 : ℝ)*(major1) + (1661789789791499/50000000000000 : ℝ)*(major2) + (4609872152524517/100000000000000 : ℝ)*(sp0) + (921979256465989/20000000000000 : ℝ)*(sp1) + (4609896566076169/100000000000000 : ℝ)*(sp2) + (2037249196586297/100000000000000 : ℝ)*(sp3) + (25824258931/100000000000000 : ℝ)*(sp4) + (2327064273/20000000000000 : ℝ)*(sp7) + (1018630415953831/50000000000000 : ℝ)*(f.failure) + (4609897976783447/100000000000000 : ℝ)*(f.sum) + (59850275935769/23565000000000000000000000000 : ℝ)*base65 + (53582783005949599/47130000000000000000000000000000 : ℝ)*base68 + (118324757405579599/47130000000000000000000000000000 : ℝ)*base70 + (205878943072949599/47130000000000000000000000000000 : ℝ)*base72 + (13273237171313/11782500000000000000000000000 : ℝ)*base74 + (11995375953990401/47130000000000000000000000000000 : ℝ)*base75 + (207598175427300401/47130000000000000000000000000000 : ℝ)*base77 + (198564206773350401/47130000000000000000000000000000 : ℝ)*base79 + (17910749494469/23565000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1344211/250000000000000000000 : ℝ)*base89 + (1344211/250000000000000000000 : ℝ)*base91 + (1344211/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5304704883728365973463467/785500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (34700051/3125000000000 : ℝ)*(base19) + (5962759/500000000000 : ℝ)*(base23) + (17363601/12500000000000 : ℝ)*(upper3) + (8881561/20000000000000 : ℝ)*(lower4) + (140491267/100000000000000 : ℝ)*(upper5) + (167917445960111/5000000000000 : ℝ)*(major0) + (167917445960111/5000000000000 : ℝ)*(major1) + (167917445960111/5000000000000 : ℝ)*(major2) + (16976849663/100000000000000 : ℝ)*(sp1) + (18126471683/100000000000000 : ℝ)*(sp2) + (2329062076911863/50000000000000 : ℝ)*(sp4) + (4658106066572431/100000000000000 : ℝ)*(sp5) + (4658104834800243/100000000000000 : ℝ)*(sp6) + (2058573459471231/100000000000000 : ℝ)*(sp7) + (2058573459471231/100000000000000 : ℝ)*(f.failure) + (2329062076911863/50000000000000 : ℝ)*(f.sum) + (2460283125881/942600000000000000000000000 : ℝ)*base65 + (21583354912370011/4713000000000000000000000000000 : ℝ)*base68 + (25482112100600011/4713000000000000000000000000000 : ℝ)*base70 + (8237463251231011/4713000000000000000000000000000 : ℝ)*base72 + (12139396249649/4713000000000000000000000000 : ℝ)*base74 + (6899499842459011/4713000000000000000000000000000 : ℝ)*base76 + (11186560115672011/4713000000000000000000000000000 : ℝ)*base78 + (42867142886399011/4713000000000000000000000000000 : ℝ)*base80 + (1656778222411/589125000000000000000000000 : ℝ)*base82 + (1313611/500000000000000000000 : ℝ)*base89 + (1313611/500000000000000000000 : ℝ)*base91 + (1313611/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1509_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8156981/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (486/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10839/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (681/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1509_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1509_s5_0 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-37449059/200000000 : ℝ)*x 0 + (2716834511/5000000000 : ℝ)*x 1 + (5217441933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (37449059/200000000 : ℝ)^4515 ≤ (11454874612207/100000000000000 : ℝ)^3491 := by
    have hnat : (37449059 : ℕ)^4515*100000000000000^3491 ≤ 11454874612207^3491*200000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37449059 200000000 11454874612207 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2716834511/5000000000 : ℝ)^4515 ≤ (45434861052197/100000000000000 : ℝ)^3491 := by
    have hnat : (2716834511 : ℕ)^4515*100000000000000^3491 ≤ 45434861052197^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716834511 5000000000 45434861052197 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217441933/10000000000 : ℝ)^4515 ≤ (43110264328419/100000000000000 : ℝ)^3491 := by
    have hnat : (5217441933 : ℕ)^4515*100000000000000^3491 ≤ 43110264328419^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217441933 10000000000 43110264328419 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-37449059/200000000 : ℝ), (2716834511/5000000000 : ℝ), (5217441933/10000000000 : ℝ)] ![(11454874612207/100000000000000 : ℝ), (45434861052197/100000000000000 : ℝ), (43110264328419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-37449059/200000000 : ℝ)|^4515 ≤ (11454874612207/100000000000000 : ℝ)^3491
        have hw : |(-37449059/200000000 : ℝ)|=(37449059/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2716834511/5000000000 : ℝ)|^4515 ≤ (45434861052197/100000000000000 : ℝ)^3491
        have hw : |(2716834511/5000000000 : ℝ)|=(2716834511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217441933/10000000000 : ℝ)|^4515 ≤ (43110264328419/100000000000000 : ℝ)^3491
        have hw : |(5217441933/10000000000 : ℝ)|=(5217441933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s5_1 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351768001/10000000000 : ℝ)*x 0 + (-79328049/400000000 : ℝ)*x 1 + (5217442711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351768001/10000000000 : ℝ)^4515 ≤ (22275556287039/50000000000000 : ℝ)^3491 := by
    have hnat : (5351768001 : ℕ)^4515*50000000000000^3491 ≤ 22275556287039^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351768001 10000000000 22275556287039 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (79328049/400000000 : ℝ)^4515 ≤ (12338614774461/100000000000000 : ℝ)^3491 := by
    have hnat : (79328049 : ℕ)^4515*100000000000000^3491 ≤ 12338614774461^3491*400000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79328049 400000000 12338614774461 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217442711/10000000000 : ℝ)^4515 ≤ (4311027264243/10000000000000 : ℝ)^3491 := by
    have hnat : (5217442711 : ℕ)^4515*10000000000000^3491 ≤ 4311027264243^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217442711 10000000000 4311027264243 10000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351768001/10000000000 : ℝ), (-79328049/400000000 : ℝ), (5217442711/10000000000 : ℝ)] ![(22275556287039/50000000000000 : ℝ), (12338614774461/100000000000000 : ℝ), (4311027264243/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351768001/10000000000 : ℝ)|^4515 ≤ (22275556287039/50000000000000 : ℝ)^3491
        have hw : |(5351768001/10000000000 : ℝ)|=(5351768001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-79328049/400000000 : ℝ)|^4515 ≤ (12338614774461/100000000000000 : ℝ)^3491
        have hw : |(-79328049/400000000 : ℝ)|=(79328049/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217442711/10000000000 : ℝ)|^4515 ≤ (4311027264243/10000000000000 : ℝ)^3491
        have hw : |(5217442711/10000000000 : ℝ)|=(5217442711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s5_2 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351767769/10000000000 : ℝ)*x 0 + (5217443/10000000 : ℝ)*x 1 + (-1983201151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351767769/10000000000 : ℝ)^4515 ≤ (44551110076281/100000000000000 : ℝ)^3491 := by
    have hnat : (5351767769 : ℕ)^4515*100000000000000^3491 ≤ 44551110076281^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351767769 10000000000 44551110076281 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217443/10000000 : ℝ)^4515 ≤ (10777568932699/25000000000000 : ℝ)^3491 := by
    have hnat : (5217443 : ℕ)^4515*25000000000000^3491 ≤ 10777568932699^3491*10000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217443 10000000 10777568932699 25000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1983201151/10000000000 : ℝ)^4515 ≤ (12338614179019/100000000000000 : ℝ)^3491 := by
    have hnat : (1983201151 : ℕ)^4515*100000000000000^3491 ≤ 12338614179019^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1983201151 10000000000 12338614179019 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351767769/10000000000 : ℝ), (5217443/10000000 : ℝ), (-1983201151/10000000000 : ℝ)] ![(44551110076281/100000000000000 : ℝ), (10777568932699/25000000000000 : ℝ), (12338614179019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351767769/10000000000 : ℝ)|^4515 ≤ (44551110076281/100000000000000 : ℝ)^3491
        have hw : |(5351767769/10000000000 : ℝ)|=(5351767769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217443/10000000 : ℝ)|^4515 ≤ (10777568932699/25000000000000 : ℝ)^3491
        have hw : |(5217443/10000000 : ℝ)|=(5217443/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1983201151/10000000000 : ℝ)|^4515 ≤ (12338614179019/100000000000000 : ℝ)^3491
        have hw : |(-1983201151/10000000000 : ℝ)|=(1983201151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s5_3 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4271167471/10000000000 : ℝ)*x 0 + (504061547/1250000000 : ℝ)*x 1 + (70652617/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4271167471/10000000000 : ℝ)^4515 ≤ (33279471837237/100000000000000 : ℝ)^3491 := by
    have hnat : (4271167471 : ℕ)^4515*100000000000000^3491 ≤ 33279471837237^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4271167471 10000000000 33279471837237 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (504061547/1250000000 : ℝ)^4515 ≤ (15447142336103/50000000000000 : ℝ)^3491 := by
    have hnat : (504061547 : ℕ)^4515*50000000000000^3491 ≤ 15447142336103^3491*1250000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504061547 1250000000 15447142336103 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (70652617/156250000 : ℝ)^4515 ≤ (3582624348153/10000000000000 : ℝ)^3491 := by
    have hnat : (70652617 : ℕ)^4515*10000000000000^3491 ≤ 3582624348153^3491*156250000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70652617 156250000 3582624348153 10000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4271167471/10000000000 : ℝ), (504061547/1250000000 : ℝ), (70652617/156250000 : ℝ)] ![(33279471837237/100000000000000 : ℝ), (15447142336103/50000000000000 : ℝ), (3582624348153/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4271167471/10000000000 : ℝ)|^4515 ≤ (33279471837237/100000000000000 : ℝ)^3491
        have hw : |(4271167471/10000000000 : ℝ)|=(4271167471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(504061547/1250000000 : ℝ)|^4515 ≤ (15447142336103/50000000000000 : ℝ)^3491
        have hw : |(504061547/1250000000 : ℝ)|=(504061547/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(70652617/156250000 : ℝ)|^4515 ≤ (3582624348153/10000000000000 : ℝ)^3491
        have hw : |(70652617/156250000 : ℝ)|=(70652617/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s5_4 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-234060239/1250000000 : ℝ)*x 0 + (5218555157/10000000000 : ℝ)*x 1 + (5432547721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (234060239/1250000000 : ℝ)^4515 ≤ (5727551880313/50000000000000 : ℝ)^3491 := by
    have hnat : (234060239 : ℕ)^4515*50000000000000^3491 ≤ 5727551880313^3491*1250000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234060239 1250000000 5727551880313 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218555157/10000000000 : ℝ)^4515 ≤ (21561080522527/50000000000000 : ℝ)^3491 := by
    have hnat : (5218555157 : ℕ)^4515*50000000000000^3491 ≤ 21561080522527^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218555157 10000000000 21561080522527 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5432547721/10000000000 : ℝ)^4515 ≤ (9084547035961/20000000000000 : ℝ)^3491 := by
    have hnat : (5432547721 : ℕ)^4515*20000000000000^3491 ≤ 9084547035961^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432547721 10000000000 9084547035961 20000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-234060239/1250000000 : ℝ), (5218555157/10000000000 : ℝ), (5432547721/10000000000 : ℝ)] ![(5727551880313/50000000000000 : ℝ), (21561080522527/50000000000000 : ℝ), (9084547035961/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-234060239/1250000000 : ℝ)|^4515 ≤ (5727551880313/50000000000000 : ℝ)^3491
        have hw : |(-234060239/1250000000 : ℝ)|=(234060239/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218555157/10000000000 : ℝ)|^4515 ≤ (21561080522527/50000000000000 : ℝ)^3491
        have hw : |(5218555157/10000000000 : ℝ)|=(5218555157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5432547721/10000000000 : ℝ)|^4515 ≤ (9084547035961/20000000000000 : ℝ)^3491
        have hw : |(5432547721/10000000000 : ℝ)|=(5432547721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s5_5 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1059006417/2000000000 : ℝ)*x 0 + (-27626493/156250000 : ℝ)*x 1 + (5432548007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059006417/2000000000 : ℝ)^4515 ≤ (1098530625201/2500000000000 : ℝ)^3491 := by
    have hnat : (1059006417 : ℕ)^4515*2500000000000^3491 ≤ 1098530625201^3491*2000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059006417 2000000000 1098530625201 2500000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27626493/156250000 : ℝ)^4515 ≤ (5318018354797/50000000000000 : ℝ)^3491 := by
    have hnat : (27626493 : ℕ)^4515*50000000000000^3491 ≤ 5318018354797^3491*156250000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27626493 156250000 5318018354797 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5432548007/10000000000 : ℝ)^4515 ≤ (45422738272547/100000000000000 : ℝ)^3491 := by
    have hnat : (5432548007 : ℕ)^4515*100000000000000^3491 ≤ 45422738272547^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432548007 10000000000 45422738272547 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059006417/2000000000 : ℝ), (-27626493/156250000 : ℝ), (5432548007/10000000000 : ℝ)] ![(1098530625201/2500000000000 : ℝ), (5318018354797/50000000000000 : ℝ), (45422738272547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059006417/2000000000 : ℝ)|^4515 ≤ (1098530625201/2500000000000 : ℝ)^3491
        have hw : |(1059006417/2000000000 : ℝ)|=(1059006417/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-27626493/156250000 : ℝ)|^4515 ≤ (5318018354797/50000000000000 : ℝ)^3491
        have hw : |(-27626493/156250000 : ℝ)|=(27626493/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5432548007/10000000000 : ℝ)|^4515 ≤ (45422738272547/100000000000000 : ℝ)^3491
        have hw : |(5432548007/10000000000 : ℝ)|=(5432548007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s5_6 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (41367441/78125000 : ℝ)*x 0 + (5432547957/10000000000 : ℝ)*x 1 + (-22101189/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41367441/78125000 : ℝ)^4515 ≤ (43941228904033/100000000000000 : ℝ)^3491 := by
    have hnat : (41367441 : ℕ)^4515*100000000000000^3491 ≤ 43941228904033^3491*78125000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41367441 78125000 43941228904033 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5432547957/10000000000 : ℝ)^4515 ≤ (22711368865929/50000000000000 : ℝ)^3491 := by
    have hnat : (5432547957 : ℕ)^4515*50000000000000^3491 ≤ 22711368865929^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432547957 10000000000 22711368865929 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (22101189/125000000 : ℝ)^4515 ≤ (1329504168577/12500000000000 : ℝ)^3491 := by
    have hnat : (22101189 : ℕ)^4515*12500000000000^3491 ≤ 1329504168577^3491*125000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22101189 125000000 1329504168577 12500000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41367441/78125000 : ℝ), (5432547957/10000000000 : ℝ), (-22101189/125000000 : ℝ)] ![(43941228904033/100000000000000 : ℝ), (22711368865929/50000000000000 : ℝ), (1329504168577/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41367441/78125000 : ℝ)|^4515 ≤ (43941228904033/100000000000000 : ℝ)^3491
        have hw : |(41367441/78125000 : ℝ)|=(41367441/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5432547957/10000000000 : ℝ)|^4515 ≤ (22711368865929/50000000000000 : ℝ)^3491
        have hw : |(5432547957/10000000000 : ℝ)|=(5432547957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-22101189/125000000 : ℝ)|^4515 ≤ (1329504168577/12500000000000 : ℝ)^3491
        have hw : |(-22101189/125000000 : ℝ)|=(22101189/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s5_7 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2135616761/5000000000 : ℝ)*x 0 + (1129812363/2500000000 : ℝ)*x 1 + (4035028809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2135616761/5000000000 : ℝ)^4515 ≤ (33280137444593/100000000000000 : ℝ)^3491 := by
    have hnat : (2135616761 : ℕ)^4515*100000000000000^3491 ≤ 33280137444593^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135616761 5000000000 33280137444593 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1129812363/2500000000 : ℝ)^4515 ≤ (2237527688987/6250000000000 : ℝ)^3491 := by
    have hnat : (1129812363 : ℕ)^4515*6250000000000^3491 ≤ 2237527688987^3491*2500000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129812363 2500000000 2237527688987 6250000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4035028809/10000000000 : ℝ)^4515 ≤ (6183883900369/20000000000000 : ℝ)^3491 := by
    have hnat : (4035028809 : ℕ)^4515*20000000000000^3491 ≤ 6183883900369^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4035028809 10000000000 6183883900369 20000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2135616761/5000000000 : ℝ), (1129812363/2500000000 : ℝ), (4035028809/10000000000 : ℝ)] ![(33280137444593/100000000000000 : ℝ), (2237527688987/6250000000000 : ℝ), (6183883900369/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2135616761/5000000000 : ℝ)|^4515 ≤ (33280137444593/100000000000000 : ℝ)^3491
        have hw : |(2135616761/5000000000 : ℝ)|=(2135616761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1129812363/2500000000 : ℝ)|^4515 ≤ (2237527688987/6250000000000 : ℝ)^3491
        have hw : |(1129812363/2500000000 : ℝ)|=(1129812363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4035028809/10000000000 : ℝ)|^4515 ≤ (6183883900369/20000000000000 : ℝ)^3491
        have hw : |(4035028809/10000000000 : ℝ)|=(4035028809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1509_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8156981/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (681/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (10903/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7741/50000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (681/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (681/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (681/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (681/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (681/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (681/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (681/6250 : ℝ) ^ (4513/1024 : ℝ) ≤ (5715022790053761/100000000000000000000 : ℝ) := by
    have hpowers : (681/6250 : ℝ)^4513 ≤ (5715022790053761/100000000000000000000 : ℝ)^1024 := by
      have hnat : (681 : ℕ)^4513*100000000000000000000^1024 ≤ 5715022790053761^1024*6250^4513 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        681 6250 5715022790053761 100000000000000000000 4513 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (681/6250 : ℝ)) (X := (5715022790053761/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4513 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4513/1024 : ℝ) ≤ (3367310054404987/12500000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4513 ≤ (3367310054404987/12500000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4513*12500000000000000000^1024 ≤ 3367310054404987^1024*10000^4513 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 3367310054404987 12500000000000000000 4513 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (3367310054404987/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4513 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005715022790053761/50000000000000000000 : ℝ) ≤ (5000129668176123/5000000000000000 : ℝ) ^ (4513/1024 : ℝ) := by
    have hpowers : (50005715022790053761/50000000000000000000 : ℝ)^1024 ≤ (5000129668176123/5000000000000000 : ℝ)^4513 := by
      have hnat : (50005715022790053761 : ℕ)^1024*5000000000000000^4513 ≤ 5000129668176123^4513*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005715022790053761 50000000000000000000 5000129668176123 5000000000000000 1024 4513 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000129668176123/5000000000000000 : ℝ)) (X := (50005715022790053761/50000000000000000000 : ℝ)) (by norm_num) 4513 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100032653503225293657/100000000000000000000 : ℝ) ≤ (1250092601838037/1250000000000000 : ℝ) ^ (4513/1024 : ℝ) := by
    have hpowers : (100032653503225293657/100000000000000000000 : ℝ)^1024 ≤ (1250092601838037/1250000000000000 : ℝ)^4513 := by
      have hnat : (100032653503225293657 : ℕ)^1024*1250000000000000^4513 ≤ 1250092601838037^4513*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100032653503225293657 100000000000000000000 1250092601838037 1250000000000000 1024 4513 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250092601838037/1250000000000000 : ℝ)) (X := (100032653503225293657/100000000000000000000 : ℝ)) (by norm_num) 4513 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253367310054404987/6250000000000000000 : ℝ) ≤ (5000611146528173/5000000000000000 : ℝ) ^ (4513/1024 : ℝ) := by
    have hpowers : (6253367310054404987/6250000000000000000 : ℝ)^1024 ≤ (5000611146528173/5000000000000000 : ℝ)^4513 := by
      have hnat : (6253367310054404987 : ℕ)^1024*5000000000000000^4513 ≤ 5000611146528173^4513*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253367310054404987 6250000000000000000 5000611146528173 5000000000000000 1024 4513 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000611146528173/5000000000000000 : ℝ)) (X := (6253367310054404987/6250000000000000000 : ℝ)) (by norm_num) 4513 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5715022790053761/100000000000000000000 : ℝ) ≤ ((11482674753738586131/11485000000000000000 : ℝ)+2*(9629567041/9188000000000 : ℝ)*(681/6250 : ℝ))^(4513/1024 : ℝ) := by
    rw [show (11482674753738586131/11485000000000000000 : ℝ)+2*(9629567041/9188000000000 : ℝ)*(681/6250 : ℝ)=(5000129668176123/5000000000000000 : ℝ) by norm_num, show 1+2*(5715022790053761/100000000000000000000 : ℝ)=(50005715022790053761/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3367310054404987/12500000000000000000 : ℝ)+(5715022790053761/100000000000000000000 : ℝ) ≤ ((11482674753738586131/11485000000000000000 : ℝ)+(9629567041/9188000000000 : ℝ)*((1549/10000 : ℝ)+(681/6250 : ℝ)))^(4513/1024 : ℝ) := by
    rw [show (11482674753738586131/11485000000000000000 : ℝ)+(9629567041/9188000000000 : ℝ)*((1549/10000 : ℝ)+(681/6250 : ℝ))=(1250092601838037/1250000000000000 : ℝ) by norm_num, show 1+(3367310054404987/12500000000000000000 : ℝ)+(5715022790053761/100000000000000000000 : ℝ)=(100032653503225293657/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3367310054404987/12500000000000000000 : ℝ) ≤ ((11482674753738586131/11485000000000000000 : ℝ)+2*(9629567041/9188000000000 : ℝ)*(1549/10000 : ℝ))^(4513/1024 : ℝ) := by
    rw [show (11482674753738586131/11485000000000000000 : ℝ)+2*(9629567041/9188000000000 : ℝ)*(1549/10000 : ℝ)=(5000611146528173/5000000000000000 : ℝ) by norm_num, show 1+2*(3367310054404987/12500000000000000000 : ℝ)=(6253367310054404987/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11482674753738586131/11485000000000000000 : ℝ)*(X 1 0+X 2 0)+(9629567041/9188000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4513/1024 : ℝ)) (lo := (681/6250 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (11482674753738586131/11485000000000000000 : ℝ)) (alpha := (9629567041/9188000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11482674753738586131/11485000000000000000 : ℝ)*(X 0 1+X 2 1)+(9629567041/9188000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4513/1024 : ℝ)) (lo := (681/6250 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (11482674753738586131/11485000000000000000 : ℝ)) (alpha := (9629567041/9188000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11482674753738586131/11485000000000000000 : ℝ)*(X 0 2+X 1 2)+(9629567041/9188000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4513/1024 : ℝ)) (lo := (681/6250 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (11482674753738586131/11485000000000000000 : ℝ)) (alpha := (9629567041/9188000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-37449059/200000000 : ℝ)*X 0 0+(2716834511/5000000000 : ℝ)*X 0 1+(5217441933/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351768001/10000000000 : ℝ)*X 1 0+(-79328049/400000000 : ℝ)*X 1 1+(5217442711/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351767769/10000000000 : ℝ)*X 2 0+(5217443/10000000 : ℝ)*X 2 1+(-1983201151/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4271167471/10000000000 : ℝ)*X 0 0+(504061547/1250000000 : ℝ)*X 0 1+(70652617/156250000 : ℝ)*X 0 2+(4271167471/10000000000 : ℝ)*X 1 0+(504061547/1250000000 : ℝ)*X 1 1+(70652617/156250000 : ℝ)*X 1 2+(4271167471/10000000000 : ℝ)*X 2 0+(504061547/1250000000 : ℝ)*X 2 1+(70652617/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-234060239/1250000000 : ℝ)*X 0 0+(5218555157/10000000000 : ℝ)*X 0 1+(5432547721/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1059006417/2000000000 : ℝ)*X 1 0+(-27626493/156250000 : ℝ)*X 1 1+(5432548007/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((41367441/78125000 : ℝ)*X 2 0+(5432547957/10000000000 : ℝ)*X 2 1+(-22101189/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2135616761/5000000000 : ℝ)*X 0 0+(1129812363/2500000000 : ℝ)*X 0 1+(4035028809/10000000000 : ℝ)*X 0 2+(2135616761/5000000000 : ℝ)*X 1 0+(1129812363/2500000000 : ℝ)*X 1 1+(4035028809/10000000000 : ℝ)*X 1 2+(2135616761/5000000000 : ℝ)*X 2 0+(1129812363/2500000000 : ℝ)*X 2 1+(4035028809/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (133307973531397098717635559/11485000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (228308897/12500000000000 : ℝ)*(base19) + (1445715517/100000000000000 : ℝ)*(base23) + (231780307/50000000000000 : ℝ)*(upper3) + (96475329/100000000000000 : ℝ)*(upper4) + (375068841/100000000000000 : ℝ)*(upper5) + (66687052972337/2000000000000 : ℝ)*(major0) + (66687052972337/2000000000000 : ℝ)*(major1) + (66687052972337/2000000000000 : ℝ)*(major2) + (4624804704260317/100000000000000 : ℝ)*(sp0) + (4624838663543081/100000000000000 : ℝ)*(sp1) + (4624839044298741/100000000000000 : ℝ)*(sp2) + (2043851615736061/100000000000000 : ℝ)*(sp3) + (35785753941/100000000000000 : ℝ)*(sp4) + (12804578789/100000000000000 : ℝ)*(sp7) + (40877288406297/2000000000000 : ℝ)*(f.failure) + (4624840490014257/100000000000000 : ℝ)*(f.sum) + (2174121055109/2297000000000000000000000000 : ℝ)*base66 + (148369820641853/22970000000000000000000000000000 : ℝ)*base68 + (99195961011838147/22970000000000000000000000000000 : ℝ)*base69 + (76495183676208147/22970000000000000000000000000000 : ℝ)*base71 + (3296565535567/2297000000000000000000000000 : ℝ)*base73 + (299311947765908147/22970000000000000000000000000000 : ℝ)*base75 + (132769044695351853/22970000000000000000000000000000 : ℝ)*base78 + (360622141711028147/22970000000000000000000000000000 : ℝ)*base79 + (1676886224173/287125000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (90643/10000000000000000000 : ℝ)*base90 + (90643/10000000000000000000 : ℝ)*base92 + (90643/10000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (53890970471499012673005459/28712500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (80457549/10000000000000 : ℝ)*(base19) + (1346677041/100000000000000 : ℝ)*(base23) + (315505267/100000000000000 : ℝ)*(lower1) + (52383843/100000000000000 : ℝ)*(upper2) + (1485039/800000000000 : ℝ)*(upper3) + (1642021/781250000000 : ℝ)*(upper5) + (336910768013037/10000000000000 : ℝ)*(major0) + (336910768013037/10000000000000 : ℝ)*(major1) + (336910768013037/10000000000000 : ℝ)*(major2) + (11461838821/100000000000000 : ℝ)*(sp2) + (4673047020284901/100000000000000 : ℝ)*(sp4) + (4673046215709411/100000000000000 : ℝ)*(sp5) + (2336517105884519/50000000000000 : ℝ)*(sp6) + (206516827741193/10000000000000 : ℝ)*(sp7) + (206516827741193/10000000000000 : ℝ)*(f.failure) + (4673047020284901/100000000000000 : ℝ)*(f.sum) + (2282819337847/1148500000000000000000000000 : ℝ)*base65 + (1143333588519189847/114850000000000000000000000000000 : ℝ)*base67 + (4636493255714710153/114850000000000000000000000000000 : ℝ)*base70 + (1275201765435889847/114850000000000000000000000000000 : ℝ)*base71 + (2388922660457/1148500000000000000000000000 : ℝ)*base73 + (747567559833689847/114850000000000000000000000000000 : ℝ)*base75 + (917897278081589847/114850000000000000000000000000000 : ℝ)*base77 + (1973162290070539847/114850000000000000000000000000000 : ℝ)*base79 + (18087851012333/2297000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (781667/50000000000000000000 : ℝ)*base90 + (781667/50000000000000000000 : ℝ)*base92 + (781667/50000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1509_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8156981/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (681/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10903/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1509_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1509_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8156981/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2001/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (521/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10903/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1509_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1509_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1509_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8156981/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2001/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (521/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10903/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1509_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

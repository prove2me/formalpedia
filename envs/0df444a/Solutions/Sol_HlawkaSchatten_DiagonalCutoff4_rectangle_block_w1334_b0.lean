-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1334_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:02:40.387102+00:00
-- url     : https://prove2.me/submissions/5b00fb84-c1c9-446c-8310-1a39ae2f716f

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
theorem support_rectangle_w1334_s0_0 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-22673563/125000000 : ℝ)*x 0 + (6000379103/10000000000 : ℝ)*x 1 + (961799349/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (22673563/125000000 : ℝ)^2147 ≤ (425112142277/4000000000000 : ℝ)^1635 := by
    have hnat : (22673563 : ℕ)^2147*4000000000000^1635 ≤ 425112142277^1635*125000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22673563 125000000 425112142277 4000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6000379103/10000000000 : ℝ)^2147 ≤ (51134660935663/100000000000000 : ℝ)^1635 := by
    have hnat : (6000379103 : ℕ)^2147*100000000000000^1635 ≤ 51134660935663^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6000379103 10000000000 51134660935663 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (961799349/2000000000 : ℝ)^2147 ≤ (38237535493673/100000000000000 : ℝ)^1635 := by
    have hnat : (961799349 : ℕ)^2147*100000000000000^1635 ≤ 38237535493673^1635*2000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      961799349 2000000000 38237535493673 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-22673563/125000000 : ℝ), (6000379103/10000000000 : ℝ), (961799349/2000000000 : ℝ)] ![(425112142277/4000000000000 : ℝ), (51134660935663/100000000000000 : ℝ), (38237535493673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-22673563/125000000 : ℝ)|^2147 ≤ (425112142277/4000000000000 : ℝ)^1635
        have hw : |(-22673563/125000000 : ℝ)|=(22673563/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6000379103/10000000000 : ℝ)|^2147 ≤ (51134660935663/100000000000000 : ℝ)^1635
        have hw : |(6000379103/10000000000 : ℝ)|=(6000379103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(961799349/2000000000 : ℝ)|^2147 ≤ (38237535493673/100000000000000 : ℝ)^1635
        have hw : |(961799349/2000000000 : ℝ)|=(961799349/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_s0_1 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5502708781/10000000000 : ℝ)*x 0 + (-2491455969/10000000000 : ℝ)*x 1 + (4808997107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5502708781/10000000000 : ℝ)^2147 ≤ (45639209036341/100000000000000 : ℝ)^1635 := by
    have hnat : (5502708781 : ℕ)^2147*100000000000000^1635 ≤ 45639209036341^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5502708781 10000000000 45639209036341 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2491455969/10000000000 : ℝ)^2147 ≤ (1612325168379/10000000000000 : ℝ)^1635 := by
    have hnat : (2491455969 : ℕ)^2147*10000000000000^1635 ≤ 1612325168379^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2491455969 10000000000 1612325168379 10000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4808997107/10000000000 : ℝ)^2147 ≤ (38237539273381/100000000000000 : ℝ)^1635 := by
    have hnat : (4808997107 : ℕ)^2147*100000000000000^1635 ≤ 38237539273381^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4808997107 10000000000 38237539273381 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5502708781/10000000000 : ℝ), (-2491455969/10000000000 : ℝ), (4808997107/10000000000 : ℝ)] ![(45639209036341/100000000000000 : ℝ), (1612325168379/10000000000000 : ℝ), (38237539273381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5502708781/10000000000 : ℝ)|^2147 ≤ (45639209036341/100000000000000 : ℝ)^1635
        have hw : |(5502708781/10000000000 : ℝ)|=(5502708781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2491455969/10000000000 : ℝ)|^2147 ≤ (1612325168379/10000000000000 : ℝ)^1635
        have hw : |(-2491455969/10000000000 : ℝ)|=(2491455969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4808997107/10000000000 : ℝ)|^2147 ≤ (38237539273381/100000000000000 : ℝ)^1635
        have hw : |(4808997107/10000000000 : ℝ)|=(4808997107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_s0_2 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1375677083/2500000000 : ℝ)*x 0 + (601124637/1250000000 : ℝ)*x 1 + (-622864139/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1375677083/2500000000 : ℝ)^2147 ≤ (4563920414619/10000000000000 : ℝ)^1635 := by
    have hnat : (1375677083 : ℕ)^2147*10000000000000^1635 ≤ 4563920414619^1635*2500000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1375677083 2500000000 4563920414619 10000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (601124637/1250000000 : ℝ)^2147 ≤ (74682693669/195312500000 : ℝ)^1635 := by
    have hnat : (601124637 : ℕ)^2147*195312500000^1635 ≤ 74682693669^1635*1250000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      601124637 1250000000 74682693669 195312500000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (622864139/2500000000 : ℝ)^2147 ≤ (16123256672081/100000000000000 : ℝ)^1635 := by
    have hnat : (622864139 : ℕ)^2147*100000000000000^1635 ≤ 16123256672081^1635*2500000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      622864139 2500000000 16123256672081 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1375677083/2500000000 : ℝ), (601124637/1250000000 : ℝ), (-622864139/2500000000 : ℝ)] ![(4563920414619/10000000000000 : ℝ), (74682693669/195312500000 : ℝ), (16123256672081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1375677083/2500000000 : ℝ)|^2147 ≤ (4563920414619/10000000000000 : ℝ)^1635
        have hw : |(1375677083/2500000000 : ℝ)|=(1375677083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(601124637/1250000000 : ℝ)|^2147 ≤ (74682693669/195312500000 : ℝ)^1635
        have hw : |(601124637/1250000000 : ℝ)|=(601124637/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-622864139/2500000000 : ℝ)|^2147 ≤ (16123256672081/100000000000000 : ℝ)^1635
        have hw : |(-622864139/2500000000 : ℝ)|=(622864139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_s0_3 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2089973387/5000000000 : ℝ)*x 0 + (1553486047/5000000000 : ℝ)*x 1 + (87420289/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2089973387/5000000000 : ℝ)^2147 ≤ (15904148962699/50000000000000 : ℝ)^1635 := by
    have hnat : (2089973387 : ℕ)^2147*50000000000000^1635 ≤ 15904148962699^1635*5000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089973387 5000000000 15904148962699 50000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1553486047/5000000000 : ℝ)^2147 ≤ (1346613268859/6250000000000 : ℝ)^1635 := by
    have hnat : (1553486047 : ℕ)^2147*6250000000000^1635 ≤ 1346613268859^1635*5000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1553486047 5000000000 1346613268859 6250000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (87420289/156250000 : ℝ)^2147 ≤ (46645889760719/100000000000000 : ℝ)^1635 := by
    have hnat : (87420289 : ℕ)^2147*100000000000000^1635 ≤ 46645889760719^1635*156250000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87420289 156250000 46645889760719 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2089973387/5000000000 : ℝ), (1553486047/5000000000 : ℝ), (87420289/156250000 : ℝ)] ![(15904148962699/50000000000000 : ℝ), (1346613268859/6250000000000 : ℝ), (46645889760719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2089973387/5000000000 : ℝ)|^2147 ≤ (15904148962699/50000000000000 : ℝ)^1635
        have hw : |(2089973387/5000000000 : ℝ)|=(2089973387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1553486047/5000000000 : ℝ)|^2147 ≤ (1346613268859/6250000000000 : ℝ)^1635
        have hw : |(1553486047/5000000000 : ℝ)|=(1553486047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(87420289/156250000 : ℝ)|^2147 ≤ (46645889760719/100000000000000 : ℝ)^1635
        have hw : |(87420289/156250000 : ℝ)|=(87420289/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_s0_4 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-454595933/2500000000 : ℝ)*x 0 + (4839674551/10000000000 : ℝ)*x 1 + (5968606437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (454595933/2500000000 : ℝ)^2147 ≤ (10662429597027/100000000000000 : ℝ)^1635 := by
    have hnat : (454595933 : ℕ)^2147*100000000000000^1635 ≤ 10662429597027^1635*2500000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      454595933 2500000000 10662429597027 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4839674551/10000000000 : ℝ)^2147 ≤ (38558167544781/100000000000000 : ℝ)^1635 := by
    have hnat : (4839674551 : ℕ)^2147*100000000000000^1635 ≤ 38558167544781^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4839674551 10000000000 38558167544781 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5968606437/10000000000 : ℝ)^2147 ≤ (25389701420263/50000000000000 : ℝ)^1635 := by
    have hnat : (5968606437 : ℕ)^2147*50000000000000^1635 ≤ 25389701420263^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5968606437 10000000000 25389701420263 50000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-454595933/2500000000 : ℝ), (4839674551/10000000000 : ℝ), (5968606437/10000000000 : ℝ)] ![(10662429597027/100000000000000 : ℝ), (38558167544781/100000000000000 : ℝ), (25389701420263/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-454595933/2500000000 : ℝ)|^2147 ≤ (10662429597027/100000000000000 : ℝ)^1635
        have hw : |(-454595933/2500000000 : ℝ)|=(454595933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4839674551/10000000000 : ℝ)|^2147 ≤ (38558167544781/100000000000000 : ℝ)^1635
        have hw : |(4839674551/10000000000 : ℝ)|=(4839674551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5968606437/10000000000 : ℝ)|^2147 ≤ (25389701420263/50000000000000 : ℝ)^1635
        have hw : |(5968606437/10000000000 : ℝ)|=(5968606437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_s0_5 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (161814687/312500000 : ℝ)*x 0 + (-332961887/2500000000 : ℝ)*x 1 + (5968606273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (161814687/312500000 : ℝ)^2147 ≤ (42136614833669/100000000000000 : ℝ)^1635 := by
    have hnat : (161814687 : ℕ)^2147*100000000000000^1635 ≤ 42136614833669^1635*312500000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161814687 312500000 42136614833669 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (332961887/2500000000 : ℝ)^2147 ≤ (3541992075617/50000000000000 : ℝ)^1635 := by
    have hnat : (332961887 : ℕ)^2147*50000000000000^1635 ≤ 3541992075617^1635*2500000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332961887 2500000000 3541992075617 50000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5968606273/10000000000 : ℝ)^2147 ≤ (50779401008327/100000000000000 : ℝ)^1635 := by
    have hnat : (5968606273 : ℕ)^2147*100000000000000^1635 ≤ 50779401008327^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5968606273 10000000000 50779401008327 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(161814687/312500000 : ℝ), (-332961887/2500000000 : ℝ), (5968606273/10000000000 : ℝ)] ![(42136614833669/100000000000000 : ℝ), (3541992075617/50000000000000 : ℝ), (50779401008327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(161814687/312500000 : ℝ)|^2147 ≤ (42136614833669/100000000000000 : ℝ)^1635
        have hw : |(161814687/312500000 : ℝ)|=(161814687/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-332961887/2500000000 : ℝ)|^2147 ≤ (3541992075617/50000000000000 : ℝ)^1635
        have hw : |(-332961887/2500000000 : ℝ)|=(332961887/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5968606273/10000000000 : ℝ)|^2147 ≤ (50779401008327/100000000000000 : ℝ)^1635
        have hw : |(5968606273/10000000000 : ℝ)|=(5968606273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_s0_6 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (647258749/1250000000 : ℝ)*x 0 + (298430321/500000000 : ℝ)*x 1 + (-665923649/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (647258749/1250000000 : ℝ)^2147 ≤ (10534153729789/25000000000000 : ℝ)^1635 := by
    have hnat : (647258749 : ℕ)^2147*25000000000000^1635 ≤ 10534153729789^1635*1250000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647258749 1250000000 10534153729789 25000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (298430321/500000000 : ℝ)^2147 ≤ (50779402650603/100000000000000 : ℝ)^1635 := by
    have hnat : (298430321 : ℕ)^2147*100000000000000^1635 ≤ 50779402650603^1635*500000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      298430321 500000000 50779402650603 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (665923649/5000000000 : ℝ)^2147 ≤ (70839824051/1000000000000 : ℝ)^1635 := by
    have hnat : (665923649 : ℕ)^2147*1000000000000^1635 ≤ 70839824051^1635*5000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      665923649 5000000000 70839824051 1000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(647258749/1250000000 : ℝ), (298430321/500000000 : ℝ), (-665923649/5000000000 : ℝ)] ![(10534153729789/25000000000000 : ℝ), (50779402650603/100000000000000 : ℝ), (70839824051/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(647258749/1250000000 : ℝ)|^2147 ≤ (10534153729789/25000000000000 : ℝ)^1635
        have hw : |(647258749/1250000000 : ℝ)|=(647258749/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(298430321/500000000 : ℝ)|^2147 ≤ (50779402650603/100000000000000 : ℝ)^1635
        have hw : |(298430321/500000000 : ℝ)|=(298430321/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-665923649/5000000000 : ℝ)|^2147 ≤ (70839824051/1000000000000 : ℝ)^1635
        have hw : |(-665923649/5000000000 : ℝ)|=(665923649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_s0_7 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4189339873/10000000000 : ℝ)*x 0 + (1106167159/2000000000 : ℝ)*x 1 + (3173321293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4189339873/10000000000 : ℝ)^2147 ≤ (15951096798001/50000000000000 : ℝ)^1635 := by
    have hnat : (4189339873 : ℕ)^2147*50000000000000^1635 ≤ 15951096798001^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4189339873 10000000000 15951096798001 50000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1106167159/2000000000 : ℝ)^2147 ≤ (45945790950273/100000000000000 : ℝ)^1635 := by
    have hnat : (1106167159 : ℕ)^2147*100000000000000^1635 ≤ 45945790950273^1635*2000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106167159 2000000000 45945790950273 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3173321293/10000000000 : ℝ)^2147 ≤ (11076007722283/50000000000000 : ℝ)^1635 := by
    have hnat : (3173321293 : ℕ)^2147*50000000000000^1635 ≤ 11076007722283^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3173321293 10000000000 11076007722283 50000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4189339873/10000000000 : ℝ), (1106167159/2000000000 : ℝ), (3173321293/10000000000 : ℝ)] ![(15951096798001/50000000000000 : ℝ), (45945790950273/100000000000000 : ℝ), (11076007722283/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4189339873/10000000000 : ℝ)|^2147 ≤ (15951096798001/50000000000000 : ℝ)^1635
        have hw : |(4189339873/10000000000 : ℝ)|=(4189339873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1106167159/2000000000 : ℝ)|^2147 ≤ (45945790950273/100000000000000 : ℝ)^1635
        have hw : |(1106167159/2000000000 : ℝ)|=(1106167159/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3173321293/10000000000 : ℝ)|^2147 ≤ (11076007722283/50000000000000 : ℝ)^1635
        have hw : |(3173321293/10000000000 : ℝ)|=(3173321293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1334_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154413479/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (677/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26929/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4293/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4293 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4293*1^1024 ≤ 0^1024*1^4293 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4293 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4293 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4293/1024 : ℝ) ≤ (2146264030503396421/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4293 ≤ (2146264030503396421/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4293*100000000000000000000^1024 ≤ 2146264030503396421^1024*5^4293 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2146264030503396421 100000000000000000000 4293 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2146264030503396421/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4293 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4293/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4293 := by
      have hnat : (1 : ℕ)^1024*1^4293 ≤ 1^4293*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4293 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4293 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102146264030503396421/100000000000000000000 : ℝ) ≤ (1256347653311079/1250000000000000 : ℝ) ^ (4293/1024 : ℝ) := by
    have hpowers : (102146264030503396421/100000000000000000000 : ℝ)^1024 ≤ (1256347653311079/1250000000000000 : ℝ)^4293 := by
      have hnat : (102146264030503396421 : ℕ)^1024*1250000000000000^4293 ≤ 1256347653311079^4293*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102146264030503396421 100000000000000000000 1256347653311079 1250000000000000 1024 4293 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1256347653311079/1250000000000000 : ℝ)) (X := (102146264030503396421/100000000000000000000 : ℝ)) (by norm_num) 4293 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52146264030503396421/50000000000000000000 : ℝ) ≤ (631347653311079/625000000000000 : ℝ) ^ (4293/1024 : ℝ) := by
    have hpowers : (52146264030503396421/50000000000000000000 : ℝ)^1024 ≤ (631347653311079/625000000000000 : ℝ)^4293 := by
      have hnat : (52146264030503396421 : ℕ)^1024*625000000000000^4293 ≤ 631347653311079^4293*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52146264030503396421 50000000000000000000 631347653311079 625000000000000 1024 4293 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (631347653311079/625000000000000 : ℝ)) (X := (52146264030503396421/50000000000000000000 : ℝ)) (by norm_num) 4293 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(6347653311079/500000000000000 : ℝ)*(0 : ℝ))^(4293/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(6347653311079/500000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2146264030503396421/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(6347653311079/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4293/1024 : ℝ) := by
    rw [show (1 : ℝ)+(6347653311079/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1256347653311079/1250000000000000 : ℝ) by norm_num, show 1+(2146264030503396421/100000000000000000000 : ℝ)+(0 : ℝ)=(102146264030503396421/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2146264030503396421/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(6347653311079/500000000000000 : ℝ)*(2/5 : ℝ))^(4293/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(6347653311079/500000000000000 : ℝ)*(2/5 : ℝ)=(631347653311079/625000000000000 : ℝ) by norm_num, show 1+2*(2146264030503396421/100000000000000000000 : ℝ)=(52146264030503396421/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(6347653311079/500000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4293/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6347653311079/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(6347653311079/500000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4293/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6347653311079/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(6347653311079/500000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4293/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6347653311079/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-22673563/125000000 : ℝ)*X 0 0+(6000379103/10000000000 : ℝ)*X 0 1+(961799349/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5502708781/10000000000 : ℝ)*X 1 0+(-2491455969/10000000000 : ℝ)*X 1 1+(4808997107/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1375677083/2500000000 : ℝ)*X 2 0+(601124637/1250000000 : ℝ)*X 2 1+(-622864139/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2089973387/5000000000 : ℝ)*X 0 0+(1553486047/5000000000 : ℝ)*X 0 1+(87420289/156250000 : ℝ)*X 0 2+(2089973387/5000000000 : ℝ)*X 1 0+(1553486047/5000000000 : ℝ)*X 1 1+(87420289/156250000 : ℝ)*X 1 2+(2089973387/5000000000 : ℝ)*X 2 0+(1553486047/5000000000 : ℝ)*X 2 1+(87420289/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-454595933/2500000000 : ℝ)*X 0 0+(4839674551/10000000000 : ℝ)*X 0 1+(5968606437/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((161814687/312500000 : ℝ)*X 1 0+(-332961887/2500000000 : ℝ)*X 1 1+(5968606273/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((647258749/1250000000 : ℝ)*X 2 0+(298430321/500000000 : ℝ)*X 2 1+(-665923649/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4189339873/10000000000 : ℝ)*X 0 0+(1106167159/2000000000 : ℝ)*X 0 1+(3173321293/10000000000 : ℝ)*X 0 2+(4189339873/10000000000 : ℝ)*X 1 0+(1106167159/2000000000 : ℝ)*X 1 1+(3173321293/10000000000 : ℝ)*X 1 2+(4189339873/10000000000 : ℝ)*X 2 0+(1106167159/2000000000 : ℝ)*X 2 1+(3173321293/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2429265125080018509/500000000000000000000000 : ℝ) := by norm_num
    linear_combination (85198243/100000000000000 : ℝ)*(base1) + (595540523/50000000000000 : ℝ)*(base19) + (1122591847/100000000000000 : ℝ)*(base23) + (207825807/100000000000000 : ℝ)*(upper3) + (36474581/100000000000000 : ℝ)*(upper5) + (620656890696337/100000000000000 : ℝ)*(major0) + (620656890696337/100000000000000 : ℝ)*(major1) + (620656890696337/100000000000000 : ℝ)*(major2) + (20984137355827/2500000000000 : ℝ)*(sp0) + (419683833169341/50000000000000 : ℝ)*(sp1) + (20984193370697/2500000000000 : ℝ)*(sp2) + (40194264939651/10000000000000 : ℝ)*(sp3) + (3448384891/100000000000000 : ℝ)*(sp4) + (101371359/5000000000000 : ℝ)*(sp7) + (401944762021933/100000000000000 : ℝ)*(f.failure) + (52460553588733/6250000000000 : ℝ)*(f.sum) + (44418225117623/25000000000000000000000000000 : ℝ)*base65 + (33443824232377/50000000000000000000000000000 : ℝ)*base68 + (453205046532377/50000000000000000000000000000 : ℝ)*base70 + (67485689282377/50000000000000000000000000000 : ℝ)*base72 + (56387807267623/25000000000000000000000000000 : ℝ)*base73 + (320841296882377/50000000000000000000000000000 : ℝ)*base76 + (17487834817623/50000000000000000000000000000 : ℝ)*base77 + (281011160817623/50000000000000000000000000000 : ℝ)*base79 + (105702298682377/25000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (48834907/10000000000000000000000 : ℝ)*base89 + (48834907/10000000000000000000000 : ℝ)*base91 + (48834907/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18056908760704235757111/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (819940267/50000000000000 : ℝ)*(base19) + (16603941/1000000000000 : ℝ)*(base23) + (3651081/20000000000000 : ℝ)*(base32) + (5536683/2500000000000 : ℝ)*(upper3) + (90187507/50000000000000 : ℝ)*(upper5) + (65498432569797/10000000000000 : ℝ)*(major0) + (65498432569797/10000000000000 : ℝ)*(major1) + (65498432569797/10000000000000 : ℝ)*(major2) + (916485701/25000000000000 : ℝ)*(sp1) + (3971316553/100000000000000 : ℝ)*(sp2) + (442896397330657/50000000000000 : ℝ)*(sp4) + (110723436104747/12500000000000 : ℝ)*(sp5) + (44289358147533/5000000000000 : ℝ)*(sp6) + (26510974857527/6250000000000 : ℝ)*(sp7) + (424175615975837/100000000000000 : ℝ)*(f.failure) + (442896397330657/50000000000000 : ℝ)*(f.sum) + (3100782339037/2500000000000000000000000000 : ℝ)*base66 + (27849403610963/5000000000000000000000000000 : ℝ)*base67 + (1031636910963/5000000000000000000000000000 : ℝ)*base69 + (4222523660963/5000000000000000000000000000 : ℝ)*base71 + (9128862090963/2500000000000000000000000000 : ℝ)*base73 + (8580429379037/5000000000000000000000000000 : ℝ)*base76 + (28493823620963/5000000000000000000000000000 : ℝ)*base77 + (47534667240963/5000000000000000000000000000 : ℝ)*base79 + (5896355189037/2500000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (28893077/10000000000000000000000 : ℝ)*base90 + (28893077/10000000000000000000000 : ℝ)*base92 + (28893077/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1334_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154413479/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (677/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26929/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1334_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1334_s1_0 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-399970601/2000000000 : ℝ)*x 0 + (1411436587/2500000000 : ℝ)*x 1 + (201781669/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (399970601/2000000000 : ℝ)^2147 ≤ (12081079131431/100000000000000 : ℝ)^1635 := by
    have hnat : (399970601 : ℕ)^2147*100000000000000^1635 ≤ 12081079131431^1635*2000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399970601 2000000000 12081079131431 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1411436587/2500000000 : ℝ)^2147 ≤ (590042042689/1250000000000 : ℝ)^1635 := by
    have hnat : (1411436587 : ℕ)^2147*1250000000000^1635 ≤ 590042042689^1635*2500000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1411436587 2500000000 590042042689 1250000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (201781669/400000000 : ℝ)^2147 ≤ (20357778722467/50000000000000 : ℝ)^1635 := by
    have hnat : (201781669 : ℕ)^2147*50000000000000^1635 ≤ 20357778722467^1635*400000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201781669 400000000 20357778722467 50000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-399970601/2000000000 : ℝ), (1411436587/2500000000 : ℝ), (201781669/400000000 : ℝ)] ![(12081079131431/100000000000000 : ℝ), (590042042689/1250000000000 : ℝ), (20357778722467/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-399970601/2000000000 : ℝ)|^2147 ≤ (12081079131431/100000000000000 : ℝ)^1635
        have hw : |(-399970601/2000000000 : ℝ)|=(399970601/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1411436587/2500000000 : ℝ)|^2147 ≤ (590042042689/1250000000000 : ℝ)^1635
        have hw : |(1411436587/2500000000 : ℝ)|=(1411436587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(201781669/400000000 : ℝ)|^2147 ≤ (20357778722467/50000000000000 : ℝ)^1635
        have hw : |(201781669/400000000 : ℝ)|=(201781669/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_s1_1 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (337909673/625000000 : ℝ)*x 0 + (-232089177/1000000000 : ℝ)*x 1 + (78820957/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (337909673/625000000 : ℝ)^2147 ≤ (11148713221069/25000000000000 : ℝ)^1635 := by
    have hnat : (337909673 : ℕ)^2147*25000000000000^1635 ≤ 11148713221069^1635*625000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337909673 625000000 11148713221069 25000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (232089177/1000000000 : ℝ)^2147 ≤ (1468959471607/10000000000000 : ℝ)^1635 := by
    have hnat : (232089177 : ℕ)^2147*10000000000000^1635 ≤ 1468959471607^1635*1000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      232089177 1000000000 1468959471607 10000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (78820957/156250000 : ℝ)^2147 ≤ (814311047787/2000000000000 : ℝ)^1635 := by
    have hnat : (78820957 : ℕ)^2147*2000000000000^1635 ≤ 814311047787^1635*156250000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78820957 156250000 814311047787 2000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(337909673/625000000 : ℝ), (-232089177/1000000000 : ℝ), (78820957/156250000 : ℝ)] ![(11148713221069/25000000000000 : ℝ), (1468959471607/10000000000000 : ℝ), (814311047787/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(337909673/625000000 : ℝ)|^2147 ≤ (11148713221069/25000000000000 : ℝ)^1635
        have hw : |(337909673/625000000 : ℝ)|=(337909673/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-232089177/1000000000 : ℝ)|^2147 ≤ (1468959471607/10000000000000 : ℝ)^1635
        have hw : |(-232089177/1000000000 : ℝ)|=(232089177/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(78820957/156250000 : ℝ)|^2147 ≤ (814311047787/2000000000000 : ℝ)^1635
        have hw : |(78820957/156250000 : ℝ)|=(78820957/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_s1_2 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2703277309/5000000000 : ℝ)*x 0 + (1261135239/2500000000 : ℝ)*x 1 + (-2320892337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2703277309/5000000000 : ℝ)^2147 ≤ (44594851259589/100000000000000 : ℝ)^1635 := by
    have hnat : (2703277309 : ℕ)^2147*100000000000000^1635 ≤ 44594851259589^1635*5000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703277309 5000000000 44594851259589 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1261135239/2500000000 : ℝ)^2147 ≤ (40715549294527/100000000000000 : ℝ)^1635 := by
    have hnat : (1261135239 : ℕ)^2147*100000000000000^1635 ≤ 40715549294527^1635*2500000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1261135239 2500000000 40715549294527 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2320892337/10000000000 : ℝ)^2147 ≤ (734479971429/5000000000000 : ℝ)^1635 := by
    have hnat : (2320892337 : ℕ)^2147*5000000000000^1635 ≤ 734479971429^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2320892337 10000000000 734479971429 5000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2703277309/5000000000 : ℝ), (1261135239/2500000000 : ℝ), (-2320892337/10000000000 : ℝ)] ![(44594851259589/100000000000000 : ℝ), (40715549294527/100000000000000 : ℝ), (734479971429/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2703277309/5000000000 : ℝ)|^2147 ≤ (44594851259589/100000000000000 : ℝ)^1635
        have hw : |(2703277309/5000000000 : ℝ)|=(2703277309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1261135239/2500000000 : ℝ)|^2147 ≤ (40715549294527/100000000000000 : ℝ)^1635
        have hw : |(1261135239/2500000000 : ℝ)|=(1261135239/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2320892337/10000000000 : ℝ)|^2147 ≤ (734479971429/5000000000000 : ℝ)^1635
        have hw : |(-2320892337/10000000000 : ℝ)|=(2320892337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_s1_3 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (214686497/500000000 : ℝ)*x 0 + (3708665401/10000000000 : ℝ)*x 1 + (4964143789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214686497/500000000 : ℝ)^2147 ≤ (32950118121799/100000000000000 : ℝ)^1635 := by
    have hnat : (214686497 : ℕ)^2147*100000000000000^1635 ≤ 32950118121799^1635*500000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214686497 500000000 32950118121799 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3708665401/10000000000 : ℝ)^2147 ≤ (13592152257927/50000000000000 : ℝ)^1635 := by
    have hnat : (3708665401 : ℕ)^2147*50000000000000^1635 ≤ 13592152257927^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3708665401 10000000000 13592152257927 50000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4964143789/10000000000 : ℝ)^2147 ≤ (4983197168517/12500000000000 : ℝ)^1635 := by
    have hnat : (4964143789 : ℕ)^2147*12500000000000^1635 ≤ 4983197168517^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4964143789 10000000000 4983197168517 12500000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214686497/500000000 : ℝ), (3708665401/10000000000 : ℝ), (4964143789/10000000000 : ℝ)] ![(32950118121799/100000000000000 : ℝ), (13592152257927/50000000000000 : ℝ), (4983197168517/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214686497/500000000 : ℝ)|^2147 ≤ (32950118121799/100000000000000 : ℝ)^1635
        have hw : |(214686497/500000000 : ℝ)|=(214686497/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3708665401/10000000000 : ℝ)|^2147 ≤ (13592152257927/50000000000000 : ℝ)^1635
        have hw : |(3708665401/10000000000 : ℝ)|=(3708665401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4964143789/10000000000 : ℝ)|^2147 ≤ (4983197168517/12500000000000 : ℝ)^1635
        have hw : |(4964143789/10000000000 : ℝ)|=(4964143789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_s1_4 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2000404839/10000000000 : ℝ)*x 0 + (1263032723/2500000000 : ℝ)*x 1 + (5638017991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2000404839/10000000000 : ℝ)^2147 ≤ (6042728431653/50000000000000 : ℝ)^1635 := by
    have hnat : (2000404839 : ℕ)^2147*50000000000000^1635 ≤ 6042728431653^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2000404839 10000000000 6042728431653 50000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1263032723/2500000000 : ℝ)^2147 ≤ (2039800587771/5000000000000 : ℝ)^1635 := by
    have hnat : (1263032723 : ℕ)^2147*5000000000000^1635 ≤ 2039800587771^1635*2500000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1263032723 2500000000 2039800587771 5000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5638017991/10000000000 : ℝ)^2147 ≤ (4711853137277/10000000000000 : ℝ)^1635 := by
    have hnat : (5638017991 : ℕ)^2147*10000000000000^1635 ≤ 4711853137277^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5638017991 10000000000 4711853137277 10000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2000404839/10000000000 : ℝ), (1263032723/2500000000 : ℝ), (5638017991/10000000000 : ℝ)] ![(6042728431653/50000000000000 : ℝ), (2039800587771/5000000000000 : ℝ), (4711853137277/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2000404839/10000000000 : ℝ)|^2147 ≤ (6042728431653/50000000000000 : ℝ)^1635
        have hw : |(-2000404839/10000000000 : ℝ)|=(2000404839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1263032723/2500000000 : ℝ)|^2147 ≤ (2039800587771/5000000000000 : ℝ)^1635
        have hw : |(1263032723/2500000000 : ℝ)|=(1263032723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5638017991/10000000000 : ℝ)|^2147 ≤ (4711853137277/10000000000000 : ℝ)^1635
        have hw : |(5638017991/10000000000 : ℝ)|=(5638017991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_s1_5 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (525065541/1000000000 : ℝ)*x 0 + (-431853799/2500000000 : ℝ)*x 1 + (2819008689/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525065541/1000000000 : ℝ)^2147 ≤ (214569716513/500000000000 : ℝ)^1635 := by
    have hnat : (525065541 : ℕ)^2147*500000000000^1635 ≤ 214569716513^1635*1000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525065541 1000000000 214569716513 500000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (431853799/2500000000 : ℝ)^2147 ≤ (311485376111/3125000000000 : ℝ)^1635 := by
    have hnat : (431853799 : ℕ)^2147*3125000000000^1635 ≤ 311485376111^1635*2500000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431853799 2500000000 311485376111 3125000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2819008689/5000000000 : ℝ)^2147 ≤ (47118524645481/100000000000000 : ℝ)^1635 := by
    have hnat : (2819008689 : ℕ)^2147*100000000000000^1635 ≤ 47118524645481^1635*5000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2819008689 5000000000 47118524645481 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525065541/1000000000 : ℝ), (-431853799/2500000000 : ℝ), (2819008689/5000000000 : ℝ)] ![(214569716513/500000000000 : ℝ), (311485376111/3125000000000 : ℝ), (47118524645481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525065541/1000000000 : ℝ)|^2147 ≤ (214569716513/500000000000 : ℝ)^1635
        have hw : |(525065541/1000000000 : ℝ)|=(525065541/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-431853799/2500000000 : ℝ)|^2147 ≤ (311485376111/3125000000000 : ℝ)^1635
        have hw : |(-431853799/2500000000 : ℝ)|=(431853799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2819008689/5000000000 : ℝ)|^2147 ≤ (47118524645481/100000000000000 : ℝ)^1635
        have hw : |(2819008689/5000000000 : ℝ)|=(2819008689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_s1_6 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (131266373/250000000 : ℝ)*x 0 + (2819008597/5000000000 : ℝ)*x 1 + (-431854039/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131266373/250000000 : ℝ)^2147 ≤ (2682121127731/6250000000000 : ℝ)^1635 := by
    have hnat : (131266373 : ℕ)^2147*6250000000000^1635 ≤ 2682121127731^1635*250000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131266373 250000000 2682121127731 6250000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2819008597/5000000000 : ℝ)^2147 ≤ (47118522626197/100000000000000 : ℝ)^1635 := by
    have hnat : (2819008597 : ℕ)^2147*100000000000000^1635 ≤ 47118522626197^1635*5000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2819008597 5000000000 47118522626197 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (431854039/2500000000 : ℝ)^2147 ≤ (1993507861921/20000000000000 : ℝ)^1635 := by
    have hnat : (431854039 : ℕ)^2147*20000000000000^1635 ≤ 1993507861921^1635*2500000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431854039 2500000000 1993507861921 20000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(131266373/250000000 : ℝ), (2819008597/5000000000 : ℝ), (-431854039/2500000000 : ℝ)] ![(2682121127731/6250000000000 : ℝ), (47118522626197/100000000000000 : ℝ), (1993507861921/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(131266373/250000000 : ℝ)|^2147 ≤ (2682121127731/6250000000000 : ℝ)^1635
        have hw : |(131266373/250000000 : ℝ)|=(131266373/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2819008597/5000000000 : ℝ)|^2147 ≤ (47118522626197/100000000000000 : ℝ)^1635
        have hw : |(2819008597/5000000000 : ℝ)|=(2819008597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-431854039/2500000000 : ℝ)|^2147 ≤ (1993507861921/20000000000000 : ℝ)^1635
        have hw : |(-431854039/2500000000 : ℝ)|=(431854039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_s1_7 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4294881059/10000000000 : ℝ)*x 0 + (4948293757/10000000000 : ℝ)*x 1 + (1862402931/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4294881059/10000000000 : ℝ)^2147 ≤ (8240429643967/25000000000000 : ℝ)^1635 := by
    have hnat : (4294881059 : ℕ)^2147*25000000000000^1635 ≤ 8240429643967^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4294881059 10000000000 8240429643967 25000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4948293757/10000000000 : ℝ)^2147 ≤ (39698514143917/100000000000000 : ℝ)^1635 := by
    have hnat : (4948293757 : ℕ)^2147*100000000000000^1635 ≤ 39698514143917^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4948293757 10000000000 39698514143917 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1862402931/5000000000 : ℝ)^2147 ≤ (27339767264473/100000000000000 : ℝ)^1635 := by
    have hnat : (1862402931 : ℕ)^2147*100000000000000^1635 ≤ 27339767264473^1635*5000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1862402931 5000000000 27339767264473 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4294881059/10000000000 : ℝ), (4948293757/10000000000 : ℝ), (1862402931/5000000000 : ℝ)] ![(8240429643967/25000000000000 : ℝ), (39698514143917/100000000000000 : ℝ), (27339767264473/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4294881059/10000000000 : ℝ)|^2147 ≤ (8240429643967/25000000000000 : ℝ)^1635
        have hw : |(4294881059/10000000000 : ℝ)|=(4294881059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4948293757/10000000000 : ℝ)|^2147 ≤ (39698514143917/100000000000000 : ℝ)^1635
        have hw : |(4948293757/10000000000 : ℝ)|=(4948293757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1862402931/5000000000 : ℝ)|^2147 ≤ (27339767264473/100000000000000 : ℝ)^1635
        have hw : |(1862402931/5000000000 : ℝ)|=(1862402931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1334_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154413479/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26929/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (677/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1363/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9761/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26929/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (677/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26929/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (677/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26929/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (677/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26929/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (677/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26929/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (677/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26929/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (677/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
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
  have hpowlo : (677/50000 : ℝ) ^ (4293/1024 : ℝ) ≤ (734514215813/50000000000000000000 : ℝ) := by
    have hpowers : (677/50000 : ℝ)^4293 ≤ (734514215813/50000000000000000000 : ℝ)^1024 := by
      have hnat : (677 : ℕ)^4293*50000000000000000000^1024 ≤ 734514215813^1024*50000^4293 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        677 50000 734514215813 50000000000000000000 4293 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (677/50000 : ℝ)) (X := (734514215813/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4293 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (26929/100000 : ℝ) ^ (4293/1024 : ℝ) ≤ (408568678523742121/100000000000000000000 : ℝ) := by
    have hpowers : (26929/100000 : ℝ)^4293 ≤ (408568678523742121/100000000000000000000 : ℝ)^1024 := by
      have hnat : (26929 : ℕ)^4293*100000000000000000000^1024 ≤ 408568678523742121^1024*100000^4293 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26929 100000 408568678523742121 100000000000000000000 4293 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26929/100000 : ℝ)) (X := (408568678523742121/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4293 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000734514215813/25000000000000000000 : ℝ) ≤ (5000000035040417/5000000000000000 : ℝ) ^ (4293/1024 : ℝ) := by
    have hpowers : (25000000734514215813/25000000000000000000 : ℝ)^1024 ≤ (5000000035040417/5000000000000000 : ℝ)^4293 := by
      have hnat : (25000000734514215813 : ℕ)^1024*5000000000000000^4293 ≤ 5000000035040417^4293*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000734514215813 25000000000000000000 5000000035040417 5000000000000000 1024 4293 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000035040417/5000000000000000 : ℝ)) (X := (25000000734514215813/25000000000000000000 : ℝ)) (by norm_num) 4293 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100408570147552173747/100000000000000000000 : ℝ) ≤ (10009730411679973/10000000000000000 : ℝ) ^ (4293/1024 : ℝ) := by
    have hpowers : (100408570147552173747/100000000000000000000 : ℝ)^1024 ≤ (10009730411679973/10000000000000000 : ℝ)^4293 := by
      have hnat : (100408570147552173747 : ℕ)^1024*10000000000000000^4293 ≤ 10009730411679973^4293*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100408570147552173747 100000000000000000000 10009730411679973 10000000000000000 1024 4293 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10009730411679973/10000000000000000 : ℝ)) (X := (100408570147552173747/100000000000000000000 : ℝ)) (by norm_num) 4293 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50408568678523742121/50000000000000000000 : ℝ) ≤ (1252432594159889/1250000000000000 : ℝ) ^ (4293/1024 : ℝ) := by
    have hpowers : (50408568678523742121/50000000000000000000 : ℝ)^1024 ≤ (1252432594159889/1250000000000000 : ℝ)^4293 := by
      have hnat : (50408568678523742121 : ℕ)^1024*1250000000000000^4293 ≤ 1252432594159889^4293*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50408568678523742121 50000000000000000000 1252432594159889 1250000000000000 1024 4293 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1252432594159889/1250000000000000 : ℝ)) (X := (50408568678523742121/50000000000000000000 : ℝ)) (by norm_num) 4293 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(734514215813/50000000000000000000 : ℝ) ≤ ((1374858344232617533/1375000000000000000 : ℝ)+2*(104627329023/27500000000000 : ℝ)*(677/50000 : ℝ))^(4293/1024 : ℝ) := by
    rw [show (1374858344232617533/1375000000000000000 : ℝ)+2*(104627329023/27500000000000 : ℝ)*(677/50000 : ℝ)=(5000000035040417/5000000000000000 : ℝ) by norm_num, show 1+2*(734514215813/50000000000000000000 : ℝ)=(25000000734514215813/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(408568678523742121/100000000000000000000 : ℝ)+(734514215813/50000000000000000000 : ℝ) ≤ ((1374858344232617533/1375000000000000000 : ℝ)+(104627329023/27500000000000 : ℝ)*((26929/100000 : ℝ)+(677/50000 : ℝ)))^(4293/1024 : ℝ) := by
    rw [show (1374858344232617533/1375000000000000000 : ℝ)+(104627329023/27500000000000 : ℝ)*((26929/100000 : ℝ)+(677/50000 : ℝ))=(10009730411679973/10000000000000000 : ℝ) by norm_num, show 1+(408568678523742121/100000000000000000000 : ℝ)+(734514215813/50000000000000000000 : ℝ)=(100408570147552173747/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(408568678523742121/100000000000000000000 : ℝ) ≤ ((1374858344232617533/1375000000000000000 : ℝ)+2*(104627329023/27500000000000 : ℝ)*(26929/100000 : ℝ))^(4293/1024 : ℝ) := by
    rw [show (1374858344232617533/1375000000000000000 : ℝ)+2*(104627329023/27500000000000 : ℝ)*(26929/100000 : ℝ)=(1252432594159889/1250000000000000 : ℝ) by norm_num, show 1+2*(408568678523742121/100000000000000000000 : ℝ)=(50408568678523742121/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1374858344232617533/1375000000000000000 : ℝ)*(X 1 0+X 2 0)+(104627329023/27500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4293/1024 : ℝ)) (lo := (677/50000 : ℝ)) (hi := (26929/100000 : ℝ)) (c := (1374858344232617533/1375000000000000000 : ℝ)) (alpha := (104627329023/27500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1374858344232617533/1375000000000000000 : ℝ)*(X 0 1+X 2 1)+(104627329023/27500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4293/1024 : ℝ)) (lo := (677/50000 : ℝ)) (hi := (26929/100000 : ℝ)) (c := (1374858344232617533/1375000000000000000 : ℝ)) (alpha := (104627329023/27500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1374858344232617533/1375000000000000000 : ℝ)*(X 0 2+X 1 2)+(104627329023/27500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4293/1024 : ℝ)) (lo := (677/50000 : ℝ)) (hi := (26929/100000 : ℝ)) (c := (1374858344232617533/1375000000000000000 : ℝ)) (alpha := (104627329023/27500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-399970601/2000000000 : ℝ)*X 0 0+(1411436587/2500000000 : ℝ)*X 0 1+(201781669/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((337909673/625000000 : ℝ)*X 1 0+(-232089177/1000000000 : ℝ)*X 1 1+(78820957/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2703277309/5000000000 : ℝ)*X 2 0+(1261135239/2500000000 : ℝ)*X 2 1+(-2320892337/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((214686497/500000000 : ℝ)*X 0 0+(3708665401/10000000000 : ℝ)*X 0 1+(4964143789/10000000000 : ℝ)*X 0 2+(214686497/500000000 : ℝ)*X 1 0+(3708665401/10000000000 : ℝ)*X 1 1+(4964143789/10000000000 : ℝ)*X 1 2+(214686497/500000000 : ℝ)*X 2 0+(3708665401/10000000000 : ℝ)*X 2 1+(4964143789/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2000404839/10000000000 : ℝ)*X 0 0+(1263032723/2500000000 : ℝ)*X 0 1+(5638017991/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((525065541/1000000000 : ℝ)*X 1 0+(-431853799/2500000000 : ℝ)*X 1 1+(2819008689/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((131266373/250000000 : ℝ)*X 2 0+(2819008597/5000000000 : ℝ)*X 2 1+(-431854039/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4294881059/10000000000 : ℝ)*X 0 0+(4948293757/10000000000 : ℝ)*X 0 1+(1862402931/5000000000 : ℝ)*X 0 2+(4294881059/10000000000 : ℝ)*X 1 0+(4948293757/10000000000 : ℝ)*X 1 1+(1862402931/5000000000 : ℝ)*X 1 2+(4294881059/10000000000 : ℝ)*X 2 0+(4948293757/10000000000 : ℝ)*X 2 1+(1862402931/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (127824779881976444490365031/17187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (143526063/100000000000000 : ℝ)*(base1) + (6737319/50000000000000 : ℝ)*(base16) + (359657823/50000000000000 : ℝ)*(base19) + (685199117/100000000000000 : ℝ)*(base23) + (197913429/100000000000000 : ℝ)*(upper3) + (614960163481869/50000000000000 : ℝ)*(major0) + (614960163481869/50000000000000 : ℝ)*(major1) + (614960163481869/50000000000000 : ℝ)*(major2) + (1663329561696213/100000000000000 : ℝ)*(sp0) + (831664342689933/50000000000000 : ℝ)*(sp1) + (1663328682907181/100000000000000 : ℝ)*(sp2) + (199127384242977/25000000000000 : ℝ)*(sp3) + (12515963/25000000000000 : ℝ)*(sp6) + (1307356747/100000000000000 : ℝ)*(sp7) + (398255493927359/50000000000000 : ℝ)*(f.failure) + (33266588363403/2000000000000 : ℝ)*(f.sum) + (196244495987/687500000000000000000000000 : ℝ)*base65 + (80793490874890823/68750000000000000000000000000000 : ℝ)*base68 + (14309081124890823/68750000000000000000000000000000 : ℝ)*base70 + (81345273687609177/68750000000000000000000000000000 : ℝ)*base71 + (484582586651/1375000000000000000000000000 : ℝ)*base74 + (724683948456140823/68750000000000000000000000000000 : ℝ)*base76 + (22148405749890823/68750000000000000000000000000000 : ℝ)*base78 + (413866354624890823/68750000000000000000000000000000 : ℝ)*base80 + (3176238519599/1375000000000000000000000000 : ℝ)*base81 + (23528039/5000000000000000000000 : ℝ)*base90 + (23528039/5000000000000000000000 : ℝ)*base92 + (23528039/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (285680606408138403071651697/34375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1297370437/100000000000000 : ℝ)*(base19) + (517445777/50000000000000 : ℝ)*(base23) + (5835751/100000000000000 : ℝ)*(upper2) + (8416761/10000000000000 : ℝ)*(upper3) + (221441053/100000000000000 : ℝ)*(upper5) + (631037288763701/50000000000000 : ℝ)*(major0) + (631037288763701/50000000000000 : ℝ)*(major1) + (631037288763701/50000000000000 : ℝ)*(major2) + (317717409/5000000000000 : ℝ)*(sp1) + (100175609/4000000000000 : ℝ)*(sp2) + (1706814416233709/100000000000000 : ℝ)*(sp4) + (1706806764515091/100000000000000 : ℝ)*(sp5) + (170681087695193/10000000000000 : ℝ)*(sp6) + (25541701931171/3125000000000 : ℝ)*(sp7) + (25541701931171/3125000000000 : ℝ)*(f.failure) + (1706814416233709/100000000000000 : ℝ)*(f.sum) + (3281850517371/1375000000000000000000000000 : ℝ)*base65 + (170007625872280367/68750000000000000000000000000000 : ℝ)*base68 + (757931415003530367/68750000000000000000000000000000 : ℝ)*base70 + (25225396659780367/68750000000000000000000000000000 : ℝ)*base72 + (2117764347373/687500000000000000000000000 : ℝ)*base73 + (150341012559780367/68750000000000000000000000000000 : ℝ)*base76 + (259586591034780367/68750000000000000000000000000000 : ℝ)*base78 + (303341450947280367/68750000000000000000000000000000 : ℝ)*base80 + (3368239305379/1375000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1403909/312500000000000000000 : ℝ)*base89 + (1403909/312500000000000000000 : ℝ)*base91 + (1403909/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1334_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154413479/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26929/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (677/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1363/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9761/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1334_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1334_s2_0 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-510177663/2500000000 : ℝ)*x 0 + (342622463/625000000 : ℝ)*x 1 + (323885553/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (510177663/2500000000 : ℝ)^2147 ≤ (12406223254161/100000000000000 : ℝ)^1635 := by
    have hnat : (510177663 : ℕ)^2147*100000000000000^1635 ≤ 12406223254161^1635*2500000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      510177663 2500000000 12406223254161 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (342622463/625000000 : ℝ)^2147 ≤ (4541335693401/10000000000000 : ℝ)^1635 := by
    have hnat : (342622463 : ℕ)^2147*10000000000000^1635 ≤ 4541335693401^1635*625000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342622463 625000000 4541335693401 10000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323885553/625000000 : ℝ)^2147 ≤ (8436083959717/20000000000000 : ℝ)^1635 := by
    have hnat : (323885553 : ℕ)^2147*20000000000000^1635 ≤ 8436083959717^1635*625000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323885553 625000000 8436083959717 20000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-510177663/2500000000 : ℝ), (342622463/625000000 : ℝ), (323885553/625000000 : ℝ)] ![(12406223254161/100000000000000 : ℝ), (4541335693401/10000000000000 : ℝ), (8436083959717/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-510177663/2500000000 : ℝ)|^2147 ≤ (12406223254161/100000000000000 : ℝ)^1635
        have hw : |(-510177663/2500000000 : ℝ)|=(510177663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(342622463/625000000 : ℝ)|^2147 ≤ (4541335693401/10000000000000 : ℝ)^1635
        have hw : |(342622463/625000000 : ℝ)|=(342622463/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(323885553/625000000 : ℝ)|^2147 ≤ (8436083959717/20000000000000 : ℝ)^1635
        have hw : |(323885553/625000000 : ℝ)|=(323885553/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_s2_1 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2683259831/5000000000 : ℝ)*x 0 + (-2195684291/10000000000 : ℝ)*x 1 + (647771051/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2683259831/5000000000 : ℝ)^2147 ≤ (44161726422447/100000000000000 : ℝ)^1635 := by
    have hnat : (2683259831 : ℕ)^2147*100000000000000^1635 ≤ 44161726422447^1635*5000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2683259831 5000000000 44161726422447 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2195684291/10000000000 : ℝ)^2147 ≤ (13657858467857/100000000000000 : ℝ)^1635 := by
    have hnat : (2195684291 : ℕ)^2147*100000000000000^1635 ≤ 13657858467857^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2195684291 10000000000 13657858467857 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (647771051/1250000000 : ℝ)^2147 ≤ (42180415095679/100000000000000 : ℝ)^1635 := by
    have hnat : (647771051 : ℕ)^2147*100000000000000^1635 ≤ 42180415095679^1635*1250000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647771051 1250000000 42180415095679 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2683259831/5000000000 : ℝ), (-2195684291/10000000000 : ℝ), (647771051/1250000000 : ℝ)] ![(44161726422447/100000000000000 : ℝ), (13657858467857/100000000000000 : ℝ), (42180415095679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2683259831/5000000000 : ℝ)|^2147 ≤ (44161726422447/100000000000000 : ℝ)^1635
        have hw : |(2683259831/5000000000 : ℝ)|=(2683259831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2195684291/10000000000 : ℝ)|^2147 ≤ (13657858467857/100000000000000 : ℝ)^1635
        have hw : |(-2195684291/10000000000 : ℝ)|=(2195684291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(647771051/1250000000 : ℝ)|^2147 ≤ (42180415095679/100000000000000 : ℝ)^1635
        have hw : |(647771051/1250000000 : ℝ)|=(647771051/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_s2_2 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (536651913/1000000000 : ℝ)*x 0 + (5182168923/10000000000 : ℝ)*x 1 + (-2195684321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536651913/1000000000 : ℝ)^2147 ≤ (2208086033681/5000000000000 : ℝ)^1635 := by
    have hnat : (536651913 : ℕ)^2147*5000000000000^1635 ≤ 2208086033681^1635*1000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536651913 1000000000 2208086033681 5000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5182168923/10000000000 : ℝ)^2147 ≤ (42180420600217/100000000000000 : ℝ)^1635 := by
    have hnat : (5182168923 : ℕ)^2147*100000000000000^1635 ≤ 42180420600217^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182168923 10000000000 42180420600217 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2195684321/10000000000 : ℝ)^2147 ≤ (13657858712903/100000000000000 : ℝ)^1635 := by
    have hnat : (2195684321 : ℕ)^2147*100000000000000^1635 ≤ 13657858712903^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2195684321 10000000000 13657858712903 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536651913/1000000000 : ℝ), (5182168923/10000000000 : ℝ), (-2195684321/10000000000 : ℝ)] ![(2208086033681/5000000000000 : ℝ), (42180420600217/100000000000000 : ℝ), (13657858712903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536651913/1000000000 : ℝ)|^2147 ≤ (2208086033681/5000000000000 : ℝ)^1635
        have hw : |(536651913/1000000000 : ℝ)|=(536651913/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5182168923/10000000000 : ℝ)|^2147 ≤ (42180420600217/100000000000000 : ℝ)^1635
        have hw : |(5182168923/10000000000 : ℝ)|=(5182168923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2195684321/10000000000 : ℝ)|^2147 ≤ (13657858712903/100000000000000 : ℝ)^1635
        have hw : |(-2195684321/10000000000 : ℝ)|=(2195684321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_s2_3 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4322276737/10000000000 : ℝ)*x 0 + (4019848793/10000000000 : ℝ)*x 1 + (232295117/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4322276737/10000000000 : ℝ)^2147 ≤ (6647617339497/20000000000000 : ℝ)^1635 := by
    have hnat : (4322276737 : ℕ)^2147*20000000000000^1635 ≤ 6647617339497^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4322276737 10000000000 6647617339497 20000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4019848793/10000000000 : ℝ)^2147 ≤ (15109081199897/50000000000000 : ℝ)^1635 := by
    have hnat : (4019848793 : ℕ)^2147*50000000000000^1635 ≤ 15109081199897^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4019848793 10000000000 15109081199897 50000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (232295117/500000000 : ℝ)^2147 ≤ (7308750177487/20000000000000 : ℝ)^1635 := by
    have hnat : (232295117 : ℕ)^2147*20000000000000^1635 ≤ 7308750177487^1635*500000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      232295117 500000000 7308750177487 20000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4322276737/10000000000 : ℝ), (4019848793/10000000000 : ℝ), (232295117/500000000 : ℝ)] ![(6647617339497/20000000000000 : ℝ), (15109081199897/50000000000000 : ℝ), (7308750177487/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4322276737/10000000000 : ℝ)|^2147 ≤ (6647617339497/20000000000000 : ℝ)^1635
        have hw : |(4322276737/10000000000 : ℝ)|=(4322276737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4019848793/10000000000 : ℝ)|^2147 ≤ (15109081199897/50000000000000 : ℝ)^1635
        have hw : |(4019848793/10000000000 : ℝ)|=(4019848793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(232295117/500000000 : ℝ)|^2147 ≤ (7308750177487/20000000000000 : ℝ)^1635
        have hw : |(232295117/500000000 : ℝ)|=(232295117/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_s2_4 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2040778591/10000000000 : ℝ)*x 0 + (5184065029/10000000000 : ℝ)*x 1 + (5480046259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2040778591/10000000000 : ℝ)^2147 ≤ (3101691405479/25000000000000 : ℝ)^1635 := by
    have hnat : (2040778591 : ℕ)^2147*25000000000000^1635 ≤ 3101691405479^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2040778591 10000000000 3101691405479 25000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184065029/10000000000 : ℝ)^2147 ≤ (42200688143911/100000000000000 : ℝ)^1635 := by
    have hnat : (5184065029 : ℕ)^2147*100000000000000^1635 ≤ 42200688143911^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184065029 10000000000 42200688143911 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5480046259/10000000000 : ℝ)^2147 ≤ (45392546212413/100000000000000 : ℝ)^1635 := by
    have hnat : (5480046259 : ℕ)^2147*100000000000000^1635 ≤ 45392546212413^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5480046259 10000000000 45392546212413 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2040778591/10000000000 : ℝ), (5184065029/10000000000 : ℝ), (5480046259/10000000000 : ℝ)] ![(3101691405479/25000000000000 : ℝ), (42200688143911/100000000000000 : ℝ), (45392546212413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2040778591/10000000000 : ℝ)|^2147 ≤ (3101691405479/25000000000000 : ℝ)^1635
        have hw : |(-2040778591/10000000000 : ℝ)|=(2040778591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184065029/10000000000 : ℝ)|^2147 ≤ (42200688143911/100000000000000 : ℝ)^1635
        have hw : |(5184065029/10000000000 : ℝ)|=(5184065029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5480046259/10000000000 : ℝ)|^2147 ≤ (45392546212413/100000000000000 : ℝ)^1635
        have hw : |(5480046259/10000000000 : ℝ)|=(5480046259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_s2_5 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1057863153/2000000000 : ℝ)*x 0 + (-948902873/5000000000 : ℝ)*x 1 + (2740023141/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057863153/2000000000 : ℝ)^2147 ≤ (1354041921061/3125000000000 : ℝ)^1635 := by
    have hnat : (1057863153 : ℕ)^2147*3125000000000^1635 ≤ 1354041921061^1635*2000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057863153 2000000000 1354041921061 3125000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (948902873/5000000000 : ℝ)^2147 ≤ (11278112057399/100000000000000 : ℝ)^1635 := by
    have hnat : (948902873 : ℕ)^2147*100000000000000^1635 ≤ 11278112057399^1635*5000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      948902873 5000000000 11278112057399 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2740023141/5000000000 : ℝ)^2147 ≤ (11348136615647/25000000000000 : ℝ)^1635 := by
    have hnat : (2740023141 : ℕ)^2147*25000000000000^1635 ≤ 11348136615647^1635*5000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2740023141 5000000000 11348136615647 25000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057863153/2000000000 : ℝ), (-948902873/5000000000 : ℝ), (2740023141/5000000000 : ℝ)] ![(1354041921061/3125000000000 : ℝ), (11278112057399/100000000000000 : ℝ), (11348136615647/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057863153/2000000000 : ℝ)|^2147 ≤ (1354041921061/3125000000000 : ℝ)^1635
        have hw : |(1057863153/2000000000 : ℝ)|=(1057863153/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-948902873/5000000000 : ℝ)|^2147 ≤ (11278112057399/100000000000000 : ℝ)^1635
        have hw : |(-948902873/5000000000 : ℝ)|=(948902873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2740023141/5000000000 : ℝ)|^2147 ≤ (11348136615647/25000000000000 : ℝ)^1635
        have hw : |(2740023141/5000000000 : ℝ)|=(2740023141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_s2_6 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5289315807/10000000000 : ℝ)*x 0 + (5480046267/10000000000 : ℝ)*x 1 + (-1897805709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289315807/10000000000 : ℝ)^2147 ≤ (5416167740719/12500000000000 : ℝ)^1635 := by
    have hnat : (5289315807 : ℕ)^2147*12500000000000^1635 ≤ 5416167740719^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289315807 10000000000 5416167740719 12500000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5480046267/10000000000 : ℝ)^2147 ≤ (45392546299431/100000000000000 : ℝ)^1635 := by
    have hnat : (5480046267 : ℕ)^2147*100000000000000^1635 ≤ 45392546299431^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5480046267 10000000000 45392546299431 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1897805709/10000000000 : ℝ)^2147 ≤ (11278111768663/100000000000000 : ℝ)^1635 := by
    have hnat : (1897805709 : ℕ)^2147*100000000000000^1635 ≤ 11278111768663^1635*10000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1897805709 10000000000 11278111768663 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289315807/10000000000 : ℝ), (5480046267/10000000000 : ℝ), (-1897805709/10000000000 : ℝ)] ![(5416167740719/12500000000000 : ℝ), (45392546299431/100000000000000 : ℝ), (11278111768663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289315807/10000000000 : ℝ)|^2147 ≤ (5416167740719/12500000000000 : ℝ)^1635
        have hw : |(5289315807/10000000000 : ℝ)|=(5289315807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5480046267/10000000000 : ℝ)|^2147 ≤ (45392546299431/100000000000000 : ℝ)^1635
        have hw : |(5480046267/10000000000 : ℝ)|=(5480046267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1897805709/10000000000 : ℝ)|^2147 ≤ (11278111768663/100000000000000 : ℝ)^1635
        have hw : |(-1897805709/10000000000 : ℝ)|=(1897805709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1334_s2_7 (p : ℝ) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ)) (x : Fin 3 → ℝ) :
    (864483323/2000000000 : ℝ)*x 0 + (2320969949/5000000000 : ℝ)*x 1 + (2011925349/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (864483323/2000000000 : ℝ)^2147 ≤ (33239499200387/100000000000000 : ℝ)^1635 := by
    have hnat : (864483323 : ℕ)^2147*100000000000000^1635 ≤ 33239499200387^1635*2000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864483323 2000000000 33239499200387 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2320969949/5000000000 : ℝ)^2147 ≤ (36502828379677/100000000000000 : ℝ)^1635 := by
    have hnat : (2320969949 : ℕ)^2147*100000000000000^1635 ≤ 36502828379677^1635*5000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2320969949 5000000000 36502828379677 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2011925349/5000000000 : ℝ)^2147 ≤ (30257672403569/100000000000000 : ℝ)^1635 := by
    have hnat : (2011925349 : ℕ)^2147*100000000000000^1635 ≤ 30257672403569^1635*5000000000^2147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011925349 5000000000 30257672403569 100000000000000 2147 1635 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2147/512 : ℝ)) 2147 1635 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(864483323/2000000000 : ℝ), (2320969949/5000000000 : ℝ), (2011925349/5000000000 : ℝ)] ![(33239499200387/100000000000000 : ℝ), (36502828379677/100000000000000 : ℝ), (30257672403569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(864483323/2000000000 : ℝ)|^2147 ≤ (33239499200387/100000000000000 : ℝ)^1635
        have hw : |(864483323/2000000000 : ℝ)|=(864483323/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2320969949/5000000000 : ℝ)|^2147 ≤ (36502828379677/100000000000000 : ℝ)^1635
        have hw : |(2320969949/5000000000 : ℝ)|=(2320969949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2011925349/5000000000 : ℝ)|^2147 ≤ (30257672403569/100000000000000 : ℝ)^1635
        have hw : |(2011925349/5000000000 : ℝ)|=(2011925349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1334_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154413479/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9761/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1363/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (9799/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2017/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9761/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1363/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9761/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1363/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9761/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1363/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9761/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1363/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9761/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1363/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9761/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1363/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1363/20000 : ℝ) ^ (4293/1024 : ℝ) ≤ (160824546337579/12500000000000000000 : ℝ) := by
    have hpowers : (1363/20000 : ℝ)^4293 ≤ (160824546337579/12500000000000000000 : ℝ)^1024 := by
      have hnat : (1363 : ℕ)^4293*12500000000000000000^1024 ≤ 160824546337579^1024*20000^4293 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1363 20000 160824546337579 12500000000000000000 4293 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1363/20000 : ℝ)) (X := (160824546337579/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4293 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9761/50000 : ℝ) ^ (4293/1024 : ℝ) ≤ (53036677427994633/50000000000000000000 : ℝ) := by
    have hpowers : (9761/50000 : ℝ)^4293 ≤ (53036677427994633/50000000000000000000 : ℝ)^1024 := by
      have hnat : (9761 : ℕ)^4293*50000000000000000000^1024 ≤ 53036677427994633^1024*50000^4293 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9761 50000 53036677427994633 50000000000000000000 4293 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9761/50000 : ℝ)) (X := (53036677427994633/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4293 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250160824546337579/6250000000000000000 : ℝ) ≤ (1250007672151039/1250000000000000 : ℝ) ^ (4293/1024 : ℝ) := by
    have hpowers : (6250160824546337579/6250000000000000000 : ℝ)^1024 ≤ (1250007672151039/1250000000000000 : ℝ)^4293 := by
      have hnat : (6250160824546337579 : ℕ)^1024*1250000000000000^4293 ≤ 1250007672151039^4293*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250160824546337579 6250000000000000000 1250007672151039 1250000000000000 1024 4293 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250007672151039/1250000000000000 : ℝ)) (X := (6250160824546337579/6250000000000000000 : ℝ)) (by norm_num) 4293 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50053679975613344949/50000000000000000000 : ℝ) ≤ (625159986723873/625000000000000 : ℝ) ^ (4293/1024 : ℝ) := by
    have hpowers : (50053679975613344949/50000000000000000000 : ℝ)^1024 ≤ (625159986723873/625000000000000 : ℝ)^4293 := by
      have hnat : (50053679975613344949 : ℕ)^1024*625000000000000^4293 ≤ 625159986723873^4293*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50053679975613344949 50000000000000000000 625159986723873 625000000000000 1024 4293 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625159986723873/625000000000000 : ℝ)) (X := (50053679975613344949/50000000000000000000 : ℝ)) (by norm_num) 4293 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25053036677427994633/25000000000000000000 : ℝ) ≤ (1250632274744453/1250000000000000 : ℝ) ^ (4293/1024 : ℝ) := by
    have hpowers : (25053036677427994633/25000000000000000000 : ℝ)^1024 ≤ (1250632274744453/1250000000000000 : ℝ)^4293 := by
      have hnat : (25053036677427994633 : ℕ)^1024*1250000000000000^4293 ≤ 1250632274744453^4293*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25053036677427994633 25000000000000000000 1250632274744453 1250000000000000 1024 4293 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250632274744453/1250000000000000 : ℝ)) (X := (25053036677427994633/25000000000000000000 : ℝ)) (by norm_num) 4293 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(160824546337579/12500000000000000000 : ℝ) ≤ ((15879590823349136163/15883750000000000000 : ℝ)+2*(312301296707/158837500000000 : ℝ)*(1363/20000 : ℝ))^(4293/1024 : ℝ) := by
    rw [show (15879590823349136163/15883750000000000000 : ℝ)+2*(312301296707/158837500000000 : ℝ)*(1363/20000 : ℝ)=(1250007672151039/1250000000000000 : ℝ) by norm_num, show 1+2*(160824546337579/12500000000000000000 : ℝ)=(6250160824546337579/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(53036677427994633/50000000000000000000 : ℝ)+(160824546337579/12500000000000000000 : ℝ) ≤ ((15879590823349136163/15883750000000000000 : ℝ)+(312301296707/158837500000000 : ℝ)*((9761/50000 : ℝ)+(1363/20000 : ℝ)))^(4293/1024 : ℝ) := by
    rw [show (15879590823349136163/15883750000000000000 : ℝ)+(312301296707/158837500000000 : ℝ)*((9761/50000 : ℝ)+(1363/20000 : ℝ))=(625159986723873/625000000000000 : ℝ) by norm_num, show 1+(53036677427994633/50000000000000000000 : ℝ)+(160824546337579/12500000000000000000 : ℝ)=(50053679975613344949/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(53036677427994633/50000000000000000000 : ℝ) ≤ ((15879590823349136163/15883750000000000000 : ℝ)+2*(312301296707/158837500000000 : ℝ)*(9761/50000 : ℝ))^(4293/1024 : ℝ) := by
    rw [show (15879590823349136163/15883750000000000000 : ℝ)+2*(312301296707/158837500000000 : ℝ)*(9761/50000 : ℝ)=(1250632274744453/1250000000000000 : ℝ) by norm_num, show 1+2*(53036677427994633/50000000000000000000 : ℝ)=(25053036677427994633/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15879590823349136163/15883750000000000000 : ℝ)*(X 1 0+X 2 0)+(312301296707/158837500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4293/1024 : ℝ)) (lo := (1363/20000 : ℝ)) (hi := (9761/50000 : ℝ)) (c := (15879590823349136163/15883750000000000000 : ℝ)) (alpha := (312301296707/158837500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15879590823349136163/15883750000000000000 : ℝ)*(X 0 1+X 2 1)+(312301296707/158837500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4293/1024 : ℝ)) (lo := (1363/20000 : ℝ)) (hi := (9761/50000 : ℝ)) (c := (15879590823349136163/15883750000000000000 : ℝ)) (alpha := (312301296707/158837500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15879590823349136163/15883750000000000000 : ℝ)*(X 0 2+X 1 2)+(312301296707/158837500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4293/1024 : ℝ)) (lo := (1363/20000 : ℝ)) (hi := (9761/50000 : ℝ)) (c := (15879590823349136163/15883750000000000000 : ℝ)) (alpha := (312301296707/158837500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-510177663/2500000000 : ℝ)*X 0 0+(342622463/625000000 : ℝ)*X 0 1+(323885553/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2683259831/5000000000 : ℝ)*X 1 0+(-2195684291/10000000000 : ℝ)*X 1 1+(647771051/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((536651913/1000000000 : ℝ)*X 2 0+(5182168923/10000000000 : ℝ)*X 2 1+(-2195684321/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4322276737/10000000000 : ℝ)*X 0 0+(4019848793/10000000000 : ℝ)*X 0 1+(232295117/500000000 : ℝ)*X 0 2+(4322276737/10000000000 : ℝ)*X 1 0+(4019848793/10000000000 : ℝ)*X 1 1+(232295117/500000000 : ℝ)*X 1 2+(4322276737/10000000000 : ℝ)*X 2 0+(4019848793/10000000000 : ℝ)*X 2 1+(232295117/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2040778591/10000000000 : ℝ)*X 0 0+(5184065029/10000000000 : ℝ)*X 0 1+(5480046259/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1057863153/2000000000 : ℝ)*X 1 0+(-948902873/5000000000 : ℝ)*X 1 1+(2740023141/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5289315807/10000000000 : ℝ)*X 2 0+(5480046267/10000000000 : ℝ)*X 2 1+(-1897805709/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((864483323/2000000000 : ℝ)*X 0 0+(2320969949/5000000000 : ℝ)*X 0 1+(2011925349/5000000000 : ℝ)*X 0 2+(864483323/2000000000 : ℝ)*X 1 0+(2320969949/5000000000 : ℝ)*X 1 1+(2011925349/5000000000 : ℝ)*X 1 2+(864483323/2000000000 : ℝ)*X 2 0+(2320969949/5000000000 : ℝ)*X 2 1+(2011925349/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1334_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7362108791923301792967201/3176750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (637328049/50000000000000 : ℝ)*(base19) + (477013167/50000000000000 : ℝ)*(base23) + (44762009/25000000000000 : ℝ)*(lower2) + (46733857/10000000000000 : ℝ)*(upper3) + (92219393/50000000000000 : ℝ)*(lower4) + (194241209/50000000000000 : ℝ)*(upper5) + (9866000007459/400000000000 : ℝ)*(major0) + (9866000007459/400000000000 : ℝ)*(major1) + (9866000007459/400000000000 : ℝ)*(major2) + (1667832639040479/50000000000000 : ℝ)*(sp0) + (166783200171243/5000000000000 : ℝ)*(sp1) + (104239510126707/3125000000000 : ℝ)*(sp2) + (798660489426597/50000000000000 : ℝ)*(sp3) + (13669545441/100000000000000 : ℝ)*(sp7) + (319466929679727/20000000000000 : ℝ)*(f.failure) + (1667832639040479/50000000000000 : ℝ)*(f.sum) + (169892009178261/12707000000000000000000000000 : ℝ)*base65 + (47168149473994183/6353500000000000000000000000000 : ℝ)*base68 + (34714561604327183/6353500000000000000000000000000 : ℝ)*base70 + (48330706784094317/6353500000000000000000000000000 : ℝ)*base71 + (12229761497/6353500000000000000000000 : ℝ)*base74 + (6277734646663183/6353500000000000000000000000000 : ℝ)*base76 + (30016587705205683/6353500000000000000000000000000 : ℝ)*base78 + (16662306777397817/6353500000000000000000000000000 : ℝ)*base79 + (27104358877459/6353500000000000000000000000 : ℝ)*base82 + (1840233/2000000000000000000000 : ℝ)*base89 + (1840233/2000000000000000000000 : ℝ)*base91 + (1840233/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (316367755698903478217049/63535000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1045970863/100000000000000 : ℝ)*(base19) + (38710797/3125000000000 : ℝ)*(base23) + (17556527/12500000000000 : ℝ)*(upper3) + (31396157/50000000000000 : ℝ)*(lower4) + (29274957/50000000000000 : ℝ)*(upper5) + (312280032597171/12500000000000 : ℝ)*(major0) + (312280032597171/12500000000000 : ℝ)*(major1) + (312280032597171/12500000000000 : ℝ)*(major2) + (11417180021/100000000000000 : ℝ)*(sp1) + (14653162611/100000000000000 : ℝ)*(sp2) + (13514361356539/400000000000 : ℝ)*(sp4) + (675715575196773/20000000000000 : ℝ)*(sp5) + (1689287223613317/50000000000000 : ℝ)*(sp6) + (1617890016439153/100000000000000 : ℝ)*(sp7) + (1617890016439153/100000000000000 : ℝ)*(f.failure) + (13514361356539/400000000000 : ℝ)*(f.sum) + (244686032584667/63535000000000000000000000000 : ℝ)*base66 + (785033799269044873/198546875000000000000000000000000 : ℝ)*base67 + (1889332030329392627/198546875000000000000000000000000 : ℝ)*base70 + (339823112819173877/198546875000000000000000000000000 : ℝ)*base72 + (49392186082153/63535000000000000000000000000 : ℝ)*base73 + (246518703194017627/198546875000000000000000000000000 : ℝ)*base76 + (50559971067766539/6204589843750000000000000000000 : ℝ)*base77 + (99585259813686499/99273437500000000000000000000000 : ℝ)*base79 + (449002731362587/63535000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (6543287/10000000000000000000000 : ℝ)*base89 + (6543287/10000000000000000000000 : ℝ)*base91 + (6543287/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1334_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154413479/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9761/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1363/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9799/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2017/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1334_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1334_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154413479/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9799/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2017/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1334_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1334_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1334_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4293/1024 : ℝ) ≤ p) (hpb : p ≤ (2147/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154413479/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9799/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2017/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1334_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

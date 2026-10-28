-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1112_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:05:40.769018+00:00
-- url     : https://prove2.me/submissions/0f4664b8-ffa5-4c92-a364-846c3471a3db

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
theorem support_rectangle_w1112_s0_0 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1901342099/10000000000 : ℝ)*x 0 + (1212258001/2000000000 : ℝ)*x 1 + (4776666417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1901342099/10000000000 : ℝ)^8305 ≤ (2208599743787/20000000000000 : ℝ)^6257 := by
    have hnat : (1901342099 : ℕ)^8305*20000000000000^6257 ≤ 2208599743787^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1901342099 10000000000 2208599743787 20000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1212258001/2000000000 : ℝ)^8305 ≤ (6431402738451/12500000000000 : ℝ)^6257 := by
    have hnat : (1212258001 : ℕ)^8305*12500000000000^6257 ≤ 6431402738451^6257*2000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1212258001 2000000000 6431402738451 12500000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4776666417/10000000000 : ℝ)^8305 ≤ (37505779357639/100000000000000 : ℝ)^6257 := by
    have hnat : (4776666417 : ℕ)^8305*100000000000000^6257 ≤ 37505779357639^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4776666417 10000000000 37505779357639 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1901342099/10000000000 : ℝ), (1212258001/2000000000 : ℝ), (4776666417/10000000000 : ℝ)] ![(2208599743787/20000000000000 : ℝ), (6431402738451/12500000000000 : ℝ), (37505779357639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1901342099/10000000000 : ℝ)|^8305 ≤ (2208599743787/20000000000000 : ℝ)^6257
        have hw : |(-1901342099/10000000000 : ℝ)|=(1901342099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1212258001/2000000000 : ℝ)|^8305 ≤ (6431402738451/12500000000000 : ℝ)^6257
        have hw : |(1212258001/2000000000 : ℝ)|=(1212258001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4776666417/10000000000 : ℝ)|^8305 ≤ (37505779357639/100000000000000 : ℝ)^6257
        have hw : |(4776666417/10000000000 : ℝ)|=(4776666417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_s0_1 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2759241663/5000000000 : ℝ)*x 0 + (-659858201/2500000000 : ℝ)*x 1 + (477666649/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2759241663/5000000000 : ℝ)^8305 ≤ (11356745161103/25000000000000 : ℝ)^6257 := by
    have hnat : (2759241663 : ℕ)^8305*25000000000000^6257 ≤ 11356745161103^6257*5000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2759241663 5000000000 11356745161103 25000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (659858201/2500000000 : ℝ)^8305 ≤ (4266809804457/25000000000000 : ℝ)^6257 := by
    have hnat : (659858201 : ℕ)^8305*25000000000000^6257 ≤ 4266809804457^6257*2500000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659858201 2500000000 4266809804457 25000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (477666649/1000000000 : ℝ)^8305 ≤ (37505780118437/100000000000000 : ℝ)^6257 := by
    have hnat : (477666649 : ℕ)^8305*100000000000000^6257 ≤ 37505780118437^6257*1000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      477666649 1000000000 37505780118437 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2759241663/5000000000 : ℝ), (-659858201/2500000000 : ℝ), (477666649/1000000000 : ℝ)] ![(11356745161103/25000000000000 : ℝ), (4266809804457/25000000000000 : ℝ), (37505780118437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2759241663/5000000000 : ℝ)|^8305 ≤ (11356745161103/25000000000000 : ℝ)^6257
        have hw : |(2759241663/5000000000 : ℝ)|=(2759241663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-659858201/2500000000 : ℝ)|^8305 ≤ (4266809804457/25000000000000 : ℝ)^6257
        have hw : |(-659858201/2500000000 : ℝ)|=(659858201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(477666649/1000000000 : ℝ)|^8305 ≤ (37505780118437/100000000000000 : ℝ)^6257
        have hw : |(477666649/1000000000 : ℝ)|=(477666649/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_s0_2 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2759241759/5000000000 : ℝ)*x 0 + (4776666303/10000000000 : ℝ)*x 1 + (-659858197/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2759241759/5000000000 : ℝ)^8305 ≤ (9085396548447/20000000000000 : ℝ)^6257 := by
    have hnat : (2759241759 : ℕ)^8305*20000000000000^6257 ≤ 9085396548447^6257*5000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2759241759 5000000000 9085396548447 20000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4776666303/10000000000 : ℝ)^8305 ≤ (18752889084771/50000000000000 : ℝ)^6257 := by
    have hnat : (4776666303 : ℕ)^8305*50000000000000^6257 ≤ 18752889084771^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4776666303 10000000000 18752889084771 50000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (659858197/2500000000 : ℝ)^8305 ≤ (2133404885063/12500000000000 : ℝ)^6257 := by
    have hnat : (659858197 : ℕ)^8305*12500000000000^6257 ≤ 2133404885063^6257*2500000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659858197 2500000000 2133404885063 12500000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2759241759/5000000000 : ℝ), (4776666303/10000000000 : ℝ), (-659858197/2500000000 : ℝ)] ![(9085396548447/20000000000000 : ℝ), (18752889084771/50000000000000 : ℝ), (2133404885063/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2759241759/5000000000 : ℝ)|^8305 ≤ (9085396548447/20000000000000 : ℝ)^6257
        have hw : |(2759241759/5000000000 : ℝ)|=(2759241759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4776666303/10000000000 : ℝ)|^8305 ≤ (18752889084771/50000000000000 : ℝ)^6257
        have hw : |(4776666303/10000000000 : ℝ)|=(4776666303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-659858197/2500000000 : ℝ)|^8305 ≤ (2133404885063/12500000000000 : ℝ)^6257
        have hw : |(-659858197/2500000000 : ℝ)|=(659858197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_s0_3 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4203428261/10000000000 : ℝ)*x 0 + (1561254651/5000000000 : ℝ)*x 1 + (2831602473/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4203428261/10000000000 : ℝ)^8305 ≤ (31652211864657/100000000000000 : ℝ)^6257 := by
    have hnat : (4203428261 : ℕ)^8305*100000000000000^6257 ≤ 31652211864657^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4203428261 10000000000 31652211864657 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1561254651/5000000000 : ℝ)^8305 ≤ (5333202151857/25000000000000 : ℝ)^6257 := by
    have hnat : (1561254651 : ℕ)^8305*25000000000000^6257 ≤ 5333202151857^6257*5000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1561254651 5000000000 5333202151857 25000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2831602473/5000000000 : ℝ)^8305 ≤ (11753744878891/25000000000000 : ℝ)^6257 := by
    have hnat : (2831602473 : ℕ)^8305*25000000000000^6257 ≤ 11753744878891^6257*5000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2831602473 5000000000 11753744878891 25000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4203428261/10000000000 : ℝ), (1561254651/5000000000 : ℝ), (2831602473/5000000000 : ℝ)] ![(31652211864657/100000000000000 : ℝ), (5333202151857/25000000000000 : ℝ), (11753744878891/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4203428261/10000000000 : ℝ)|^8305 ≤ (31652211864657/100000000000000 : ℝ)^6257
        have hw : |(4203428261/10000000000 : ℝ)|=(4203428261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1561254651/5000000000 : ℝ)|^8305 ≤ (5333202151857/25000000000000 : ℝ)^6257
        have hw : |(1561254651/5000000000 : ℝ)|=(1561254651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2831602473/5000000000 : ℝ)|^8305 ≤ (11753744878891/25000000000000 : ℝ)^6257
        have hw : |(2831602473/5000000000 : ℝ)|=(2831602473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_s0_4 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1906577679/10000000000 : ℝ)*x 0 + (2404910207/5000000000 : ℝ)*x 1 + (6026971967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1906577679/10000000000 : ℝ)^8305 ≤ (1108337818657/10000000000000 : ℝ)^6257 := by
    have hnat : (1906577679 : ℕ)^8305*10000000000000^6257 ≤ 1108337818657^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1906577679 10000000000 1108337818657 10000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2404910207/5000000000 : ℝ)^8305 ≤ (37851698768661/100000000000000 : ℝ)^6257 := by
    have hnat : (2404910207 : ℕ)^8305*100000000000000^6257 ≤ 37851698768661^6257*5000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2404910207 5000000000 37851698768661 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6026971967/10000000000 : ℝ)^8305 ≤ (10212984605887/20000000000000 : ℝ)^6257 := by
    have hnat : (6026971967 : ℕ)^8305*20000000000000^6257 ≤ 10212984605887^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6026971967 10000000000 10212984605887 20000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1906577679/10000000000 : ℝ), (2404910207/5000000000 : ℝ), (6026971967/10000000000 : ℝ)] ![(1108337818657/10000000000000 : ℝ), (37851698768661/100000000000000 : ℝ), (10212984605887/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1906577679/10000000000 : ℝ)|^8305 ≤ (1108337818657/10000000000000 : ℝ)^6257
        have hw : |(-1906577679/10000000000 : ℝ)|=(1906577679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2404910207/5000000000 : ℝ)|^8305 ≤ (37851698768661/100000000000000 : ℝ)^6257
        have hw : |(2404910207/5000000000 : ℝ)|=(2404910207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6026971967/10000000000 : ℝ)|^8305 ≤ (10212984605887/20000000000000 : ℝ)^6257
        have hw : |(6026971967/10000000000 : ℝ)|=(6026971967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_s0_5 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2584785631/5000000000 : ℝ)*x 0 + (-21705127/156250000 : ℝ)*x 1 + (6026974287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2584785631/5000000000 : ℝ)^8305 ≤ (41654732574063/100000000000000 : ℝ)^6257 := by
    have hnat : (2584785631 : ℕ)^8305*100000000000000^6257 ≤ 41654732574063^6257*5000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2584785631 5000000000 41654732574063 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21705127/156250000 : ℝ)^8305 ≤ (1456063658347/20000000000000 : ℝ)^6257 := by
    have hnat : (21705127 : ℕ)^8305*20000000000000^6257 ≤ 1456063658347^6257*156250000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21705127 156250000 1456063658347 20000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6026974287/10000000000 : ℝ)^8305 ≤ (12766237280023/25000000000000 : ℝ)^6257 := by
    have hnat : (6026974287 : ℕ)^8305*25000000000000^6257 ≤ 12766237280023^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6026974287 10000000000 12766237280023 25000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2584785631/5000000000 : ℝ), (-21705127/156250000 : ℝ), (6026974287/10000000000 : ℝ)] ![(41654732574063/100000000000000 : ℝ), (1456063658347/20000000000000 : ℝ), (12766237280023/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2584785631/5000000000 : ℝ)|^8305 ≤ (41654732574063/100000000000000 : ℝ)^6257
        have hw : |(2584785631/5000000000 : ℝ)|=(2584785631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-21705127/156250000 : ℝ)|^8305 ≤ (1456063658347/20000000000000 : ℝ)^6257
        have hw : |(-21705127/156250000 : ℝ)|=(21705127/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6026974287/10000000000 : ℝ)|^8305 ≤ (12766237280023/25000000000000 : ℝ)^6257
        have hw : |(6026974287/10000000000 : ℝ)|=(6026974287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_s0_6 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1292393569/2500000000 : ℝ)*x 0 + (1506743117/2500000000 : ℝ)*x 1 + (-277825287/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1292393569/2500000000 : ℝ)^8305 ≤ (41654764808983/100000000000000 : ℝ)^6257 := by
    have hnat : (1292393569 : ℕ)^8305*100000000000000^6257 ≤ 41654764808983^6257*2500000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292393569 2500000000 41654764808983 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1506743117/2500000000 : ℝ)^8305 ≤ (51064928663667/100000000000000 : ℝ)^6257 := by
    have hnat : (1506743117 : ℕ)^8305*100000000000000^6257 ≤ 51064928663667^6257*2500000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1506743117 2500000000 51064928663667 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (277825287/2000000000 : ℝ)^8305 ≤ (3640153257317/50000000000000 : ℝ)^6257 := by
    have hnat : (277825287 : ℕ)^8305*50000000000000^6257 ≤ 3640153257317^6257*2000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277825287 2000000000 3640153257317 50000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1292393569/2500000000 : ℝ), (1506743117/2500000000 : ℝ), (-277825287/2000000000 : ℝ)] ![(41654764808983/100000000000000 : ℝ), (51064928663667/100000000000000 : ℝ), (3640153257317/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1292393569/2500000000 : ℝ)|^8305 ≤ (41654764808983/100000000000000 : ℝ)^6257
        have hw : |(1292393569/2500000000 : ℝ)|=(1292393569/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1506743117/2500000000 : ℝ)|^8305 ≤ (51064928663667/100000000000000 : ℝ)^6257
        have hw : |(1506743117/2500000000 : ℝ)|=(1506743117/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-277825287/2000000000 : ℝ)|^8305 ≤ (3640153257317/50000000000000 : ℝ)^6257
        have hw : |(-277825287/2000000000 : ℝ)|=(277825287/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_s0_7 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2106889817/5000000000 : ℝ)*x 0 + (1399409109/2500000000 : ℝ)*x 1 + (638075889/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2106889817/5000000000 : ℝ)^8305 ≤ (31755713392907/100000000000000 : ℝ)^6257 := by
    have hnat : (2106889817 : ℕ)^8305*100000000000000^6257 ≤ 31755713392907^6257*5000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106889817 5000000000 31755713392907 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1399409109/2500000000 : ℝ)^8305 ≤ (46293843925179/100000000000000 : ℝ)^6257 := by
    have hnat : (1399409109 : ℕ)^8305*100000000000000^6257 ≤ 46293843925179^6257*2500000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1399409109 2500000000 46293843925179 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (638075889/2000000000 : ℝ)^8305 ≤ (10975221335389/50000000000000 : ℝ)^6257 := by
    have hnat : (638075889 : ℕ)^8305*50000000000000^6257 ≤ 10975221335389^6257*2000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      638075889 2000000000 10975221335389 50000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2106889817/5000000000 : ℝ), (1399409109/2500000000 : ℝ), (638075889/2000000000 : ℝ)] ![(31755713392907/100000000000000 : ℝ), (46293843925179/100000000000000 : ℝ), (10975221335389/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2106889817/5000000000 : ℝ)|^8305 ≤ (31755713392907/100000000000000 : ℝ)^6257
        have hw : |(2106889817/5000000000 : ℝ)|=(2106889817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1399409109/2500000000 : ℝ)|^8305 ≤ (46293843925179/100000000000000 : ℝ)^6257
        have hw : |(1399409109/2500000000 : ℝ)|=(1399409109/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(638075889/2000000000 : ℝ)|^8305 ≤ (10975221335389/50000000000000 : ℝ)^6257
        have hw : |(638075889/2000000000 : ℝ)|=(638075889/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1112_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148888709/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (289/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27931/100000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
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
  have hpowlo : (0 : ℝ) ^ (519/128 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^519 ≤ (0 : ℝ)^128 := by
      have hnat : (0 : ℕ)^519*1^128 ≤ 0^128*1^519 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 519 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 519 128 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (519/128 : ℝ) ≤ (97395213156736899/4000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^519 ≤ (97395213156736899/4000000000000000000 : ℝ)^128 := by
      have hnat : (2 : ℕ)^519*4000000000000000000^128 ≤ 97395213156736899^128*5^519 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 97395213156736899 4000000000000000000 519 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (97395213156736899/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 519 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (519/128 : ℝ) := by
    have hpowers : (1 : ℝ)^128 ≤ (1 : ℝ)^519 := by
      have hnat : (1 : ℕ)^128*1^519 ≤ 1^519*1^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 128 519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 519 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (4097395213156736899/4000000000000000000 : ℝ) ≤ (10059507928655297/10000000000000000 : ℝ) ^ (519/128 : ℝ) := by
    have hpowers : (4097395213156736899/4000000000000000000 : ℝ)^128 ≤ (10059507928655297/10000000000000000 : ℝ)^519 := by
      have hnat : (4097395213156736899 : ℕ)^128*10000000000000000^519 ≤ 10059507928655297^519*4000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4097395213156736899 4000000000000000000 10059507928655297 10000000000000000 128 519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10059507928655297/10000000000000000 : ℝ)) (X := (4097395213156736899/4000000000000000000 : ℝ)) (by norm_num) 519 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (2097395213156736899/2000000000000000000 : ℝ) ≤ (5059507928655297/5000000000000000 : ℝ) ^ (519/128 : ℝ) := by
    have hpowers : (2097395213156736899/2000000000000000000 : ℝ)^128 ≤ (5059507928655297/5000000000000000 : ℝ)^519 := by
      have hnat : (2097395213156736899 : ℕ)^128*5000000000000000^519 ≤ 5059507928655297^519*2000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2097395213156736899 2000000000000000000 5059507928655297 5000000000000000 128 519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5059507928655297/5000000000000000 : ℝ)) (X := (2097395213156736899/2000000000000000000 : ℝ)) (by norm_num) 519 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(59507928655297/4000000000000000 : ℝ)*(0 : ℝ))^(519/128 : ℝ) := by
    rw [show (1 : ℝ)+2*(59507928655297/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(97395213156736899/4000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(59507928655297/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(519/128 : ℝ) := by
    rw [show (1 : ℝ)+(59507928655297/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10059507928655297/10000000000000000 : ℝ) by norm_num, show 1+(97395213156736899/4000000000000000000 : ℝ)+(0 : ℝ)=(4097395213156736899/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(97395213156736899/4000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(59507928655297/4000000000000000 : ℝ)*(2/5 : ℝ))^(519/128 : ℝ) := by
    rw [show (1 : ℝ)+2*(59507928655297/4000000000000000 : ℝ)*(2/5 : ℝ)=(5059507928655297/5000000000000000 : ℝ) by norm_num, show 1+2*(97395213156736899/4000000000000000000 : ℝ)=(2097395213156736899/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(59507928655297/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (519/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (59507928655297/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(59507928655297/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (519/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (59507928655297/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(59507928655297/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (519/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (59507928655297/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1901342099/10000000000 : ℝ)*X 0 0+(1212258001/2000000000 : ℝ)*X 0 1+(4776666417/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2759241663/5000000000 : ℝ)*X 1 0+(-659858201/2500000000 : ℝ)*X 1 1+(477666649/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2759241759/5000000000 : ℝ)*X 2 0+(4776666303/10000000000 : ℝ)*X 2 1+(-659858197/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4203428261/10000000000 : ℝ)*X 0 0+(1561254651/5000000000 : ℝ)*X 0 1+(2831602473/5000000000 : ℝ)*X 0 2+(4203428261/10000000000 : ℝ)*X 1 0+(1561254651/5000000000 : ℝ)*X 1 1+(2831602473/5000000000 : ℝ)*X 1 2+(4203428261/10000000000 : ℝ)*X 2 0+(1561254651/5000000000 : ℝ)*X 2 1+(2831602473/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1906577679/10000000000 : ℝ)*X 0 0+(2404910207/5000000000 : ℝ)*X 0 1+(6026971967/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2584785631/5000000000 : ℝ)*X 1 0+(-21705127/156250000 : ℝ)*X 1 1+(6026974287/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1292393569/2500000000 : ℝ)*X 2 0+(1506743117/2500000000 : ℝ)*X 2 1+(-277825287/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2106889817/5000000000 : ℝ)*X 0 0+(1399409109/2500000000 : ℝ)*X 0 1+(638075889/2000000000 : ℝ)*X 0 2+(2106889817/5000000000 : ℝ)*X 1 0+(1399409109/2500000000 : ℝ)*X 1 1+(638075889/2000000000 : ℝ)*X 1 2+(2106889817/5000000000 : ℝ)*X 2 0+(1399409109/2500000000 : ℝ)*X 2 1+(638075889/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (672066107179870886708709/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9092247/12500000000000 : ℝ)*(base1) + (833321469/50000000000000 : ℝ)*(base19) + (1573760603/100000000000000 : ℝ)*(base23) + (1874471/1562500000000 : ℝ)*(base24) + (48322571/12500000000000 : ℝ)*(upper3) + (586022597013533/100000000000000 : ℝ)*(major0) + (586022597013533/100000000000000 : ℝ)*(major1) + (586022597013533/100000000000000 : ℝ)*(major2) + (778443662226891/100000000000000 : ℝ)*(sp0) + (778445561162889/100000000000000 : ℝ)*(sp1) + (19461138351977/2500000000000 : ℝ)*(sp2) + (196797355899363/50000000000000 : ℝ)*(sp3) + (3638316911/100000000000000 : ℝ)*(sp4) + (92426953/3125000000000 : ℝ)*(sp7) + (196798871099599/50000000000000 : ℝ)*(f.failure) + (778447227805827/100000000000000 : ℝ)*(f.sum) + (676172833265699/200000000000000000000000000000 : ℝ)*base66 + (284174845665699/400000000000000000000000000000 : ℝ)*base68 + (196873998865699/400000000000000000000000000000 : ℝ)*base70 + (3221091504465699/400000000000000000000000000000 : ℝ)*base72 + (108063749265699/200000000000000000000000000000 : ℝ)*base74 + (2590808449265699/400000000000000000000000000000 : ℝ)*base76 + (889937354865699/400000000000000000000000000000 : ℝ)*base78 + (3477573098065699/400000000000000000000000000000 : ℝ)*base80 + (211178894065699/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (55527691/5000000000000000000000 : ℝ)*base89 + (55527691/5000000000000000000000 : ℝ)*base91 + (55527691/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (868138038383434077230409/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1355901397/100000000000000 : ℝ)*(base19) + (288287269/12500000000000 : ℝ)*(base23) + (104955397/25000000000000 : ℝ)*(base39) + (446841141/100000000000000 : ℝ)*(base45) + (282469507/100000000000000 : ℝ)*(upper3) + (335926141/100000000000000 : ℝ)*(upper5) + (309248444680701/50000000000000 : ℝ)*(major0) + (309248444680701/50000000000000 : ℝ)*(major1) + (309248234769907/50000000000000 : ℝ)*(major2) + (943092821/100000000000000 : ℝ)*(sp2) + (410792104547423/50000000000000 : ℝ)*(sp4) + (821582853193449/100000000000000 : ℝ)*(sp5) + (41079068976273/5000000000000 : ℝ)*(sp6) + (20770443021351/5000000000000 : ℝ)*(sp7) + (20770443021351/5000000000000 : ℝ)*(f.failure) + (821584628916433/100000000000000 : ℝ)*(f.sum) + (14413782491911/12500000000000000000000000000 : ℝ)*base65 + (321954681052621/200000000000000000000000000000 : ℝ)*base68 + (847205739076803/200000000000000000000000000000 : ℝ)*base70 + (696451951852621/200000000000000000000000000000 : ℝ)*base72 + (41940044966911/12500000000000000000000000000 : ℝ)*base73 + (781938495276803/200000000000000000000000000000 : ℝ)*base76 + (314848926276803/200000000000000000000000000000 : ℝ)*base78 + (182582104723197/200000000000000000000000000000 : ℝ)*base79 + (674726072123197/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (174141/500000000000000000000 : ℝ)*base90 + (174141/500000000000000000000 : ℝ)*base92 + (174141/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1112_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148888709/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (289/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27931/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1112_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1112_s1_0 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-421633351/2000000000 : ℝ)*x 0 + (2854809243/5000000000 : ℝ)*x 1 + (499591523/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (421633351/2000000000 : ℝ)^8305 ≤ (2533027961209/20000000000000 : ℝ)^6257 := by
    have hnat : (421633351 : ℕ)^8305*20000000000000^6257 ≤ 2533027961209^6257*2000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421633351 2000000000 2533027961209 20000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2854809243/5000000000 : ℝ)^8305 ≤ (23763550619641/50000000000000 : ℝ)^6257 := by
    have hnat : (2854809243 : ℕ)^8305*50000000000000^6257 ≤ 23763550619641^6257*5000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2854809243 5000000000 23763550619641 50000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (499591523/1000000000 : ℝ)^8305 ≤ (39807758945073/100000000000000 : ℝ)^6257 := by
    have hnat : (499591523 : ℕ)^8305*100000000000000^6257 ≤ 39807758945073^6257*1000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499591523 1000000000 39807758945073 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-421633351/2000000000 : ℝ), (2854809243/5000000000 : ℝ), (499591523/1000000000 : ℝ)] ![(2533027961209/20000000000000 : ℝ), (23763550619641/50000000000000 : ℝ), (39807758945073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-421633351/2000000000 : ℝ)|^8305 ≤ (2533027961209/20000000000000 : ℝ)^6257
        have hw : |(-421633351/2000000000 : ℝ)|=(421633351/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2854809243/5000000000 : ℝ)|^8305 ≤ (23763550619641/50000000000000 : ℝ)^6257
        have hw : |(2854809243/5000000000 : ℝ)|=(2854809243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(499591523/1000000000 : ℝ)|^8305 ≤ (39807758945073/100000000000000 : ℝ)^6257
        have hw : |(499591523/1000000000 : ℝ)|=(499591523/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_s1_1 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5420776417/10000000000 : ℝ)*x 0 + (-1246957977/5000000000 : ℝ)*x 1 + (499591517/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5420776417/10000000000 : ℝ)^8305 ≤ (44362524913717/100000000000000 : ℝ)^6257 := by
    have hnat : (5420776417 : ℕ)^8305*100000000000000^6257 ≤ 44362524913717^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420776417 10000000000 44362524913717 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1246957977/5000000000 : ℝ)^8305 ≤ (1582971674931/10000000000000 : ℝ)^6257 := by
    have hnat : (1246957977 : ℕ)^8305*10000000000000^6257 ≤ 1582971674931^6257*5000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1246957977 5000000000 1582971674931 10000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (499591517/1000000000 : ℝ)^8305 ≤ (19903879155253/50000000000000 : ℝ)^6257 := by
    have hnat : (499591517 : ℕ)^8305*50000000000000^6257 ≤ 19903879155253^6257*1000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499591517 1000000000 19903879155253 50000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5420776417/10000000000 : ℝ), (-1246957977/5000000000 : ℝ), (499591517/1000000000 : ℝ)] ![(44362524913717/100000000000000 : ℝ), (1582971674931/10000000000000 : ℝ), (19903879155253/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5420776417/10000000000 : ℝ)|^8305 ≤ (44362524913717/100000000000000 : ℝ)^6257
        have hw : |(5420776417/10000000000 : ℝ)|=(5420776417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1246957977/5000000000 : ℝ)|^8305 ≤ (1582971674931/10000000000000 : ℝ)^6257
        have hw : |(-1246957977/5000000000 : ℝ)|=(1246957977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(499591517/1000000000 : ℝ)|^8305 ≤ (19903879155253/50000000000000 : ℝ)^6257
        have hw : |(499591517/1000000000 : ℝ)|=(499591517/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_s1_2 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1084155549/2000000000 : ℝ)*x 0 + (15612231/31250000 : ℝ)*x 1 + (-623478953/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1084155549/2000000000 : ℝ)^8305 ≤ (22181269669533/50000000000000 : ℝ)^6257 := by
    have hnat : (1084155549 : ℕ)^8305*50000000000000^6257 ≤ 22181269669533^6257*2000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084155549 2000000000 22181269669533 50000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (15612231/31250000 : ℝ)^8305 ≤ (39807745090363/100000000000000 : ℝ)^6257 := by
    have hnat : (15612231 : ℕ)^8305*100000000000000^6257 ≤ 39807745090363^6257*31250000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15612231 31250000 39807745090363 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (623478953/2500000000 : ℝ)^8305 ≤ (7914857776487/50000000000000 : ℝ)^6257 := by
    have hnat : (623478953 : ℕ)^8305*50000000000000^6257 ≤ 7914857776487^6257*2500000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      623478953 2500000000 7914857776487 50000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1084155549/2000000000 : ℝ), (15612231/31250000 : ℝ), (-623478953/2500000000 : ℝ)] ![(22181269669533/50000000000000 : ℝ), (39807745090363/100000000000000 : ℝ), (7914857776487/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1084155549/2000000000 : ℝ)|^8305 ≤ (22181269669533/50000000000000 : ℝ)^6257
        have hw : |(1084155549/2000000000 : ℝ)|=(1084155549/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(15612231/31250000 : ℝ)|^8305 ≤ (39807745090363/100000000000000 : ℝ)^6257
        have hw : |(15612231/31250000 : ℝ)|=(15612231/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-623478953/2500000000 : ℝ)|^8305 ≤ (7914857776487/50000000000000 : ℝ)^6257
        have hw : |(-623478953/2500000000 : ℝ)|=(623478953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_s1_3 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4319964187/10000000000 : ℝ)*x 0 + (3671343249/10000000000 : ℝ)*x 1 + (5082885479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4319964187/10000000000 : ℝ)^8305 ≤ (32822216859681/100000000000000 : ℝ)^6257 := by
    have hnat : (4319964187 : ℕ)^8305*100000000000000^6257 ≤ 32822216859681^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4319964187 10000000000 32822216859681 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3671343249/10000000000 : ℝ)^8305 ≤ (26447606490459/100000000000000 : ℝ)^6257 := by
    have hnat : (3671343249 : ℕ)^8305*100000000000000^6257 ≤ 26447606490459^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3671343249 10000000000 26447606490459 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5082885479/10000000000 : ℝ)^8305 ≤ (4073017662697/10000000000000 : ℝ)^6257 := by
    have hnat : (5082885479 : ℕ)^8305*10000000000000^6257 ≤ 4073017662697^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5082885479 10000000000 4073017662697 10000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4319964187/10000000000 : ℝ), (3671343249/10000000000 : ℝ), (5082885479/10000000000 : ℝ)] ![(32822216859681/100000000000000 : ℝ), (26447606490459/100000000000000 : ℝ), (4073017662697/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4319964187/10000000000 : ℝ)|^8305 ≤ (32822216859681/100000000000000 : ℝ)^6257
        have hw : |(4319964187/10000000000 : ℝ)|=(4319964187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3671343249/10000000000 : ℝ)|^8305 ≤ (26447606490459/100000000000000 : ℝ)^6257
        have hw : |(3671343249/10000000000 : ℝ)|=(3671343249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5082885479/10000000000 : ℝ)|^8305 ≤ (4073017662697/10000000000000 : ℝ)^6257
        have hw : |(5082885479/10000000000 : ℝ)|=(5082885479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_s1_4 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1054507899/5000000000 : ℝ)*x 0 + (5005772901/10000000000 : ℝ)*x 1 + (5699563621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054507899/5000000000 : ℝ)^8305 ≤ (12671910556641/100000000000000 : ℝ)^6257 := by
    have hnat : (1054507899 : ℕ)^8305*100000000000000^6257 ≤ 12671910556641^6257*5000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054507899 5000000000 12671910556641 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5005772901/10000000000 : ℝ)^8305 ≤ (1596481938199/4000000000000 : ℝ)^6257 := by
    have hnat : (5005772901 : ℕ)^8305*4000000000000^6257 ≤ 1596481938199^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5005772901 10000000000 1596481938199 4000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5699563621/10000000000 : ℝ)^8305 ≤ (47416040968277/100000000000000 : ℝ)^6257 := by
    have hnat : (5699563621 : ℕ)^8305*100000000000000^6257 ≤ 47416040968277^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5699563621 10000000000 47416040968277 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1054507899/5000000000 : ℝ), (5005772901/10000000000 : ℝ), (5699563621/10000000000 : ℝ)] ![(12671910556641/100000000000000 : ℝ), (1596481938199/4000000000000 : ℝ), (47416040968277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1054507899/5000000000 : ℝ)|^8305 ≤ (12671910556641/100000000000000 : ℝ)^6257
        have hw : |(-1054507899/5000000000 : ℝ)|=(1054507899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5005772901/10000000000 : ℝ)|^8305 ≤ (1596481938199/4000000000000 : ℝ)^6257
        have hw : |(5005772901/10000000000 : ℝ)|=(5005772901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5699563621/10000000000 : ℝ)|^8305 ≤ (47416040968277/100000000000000 : ℝ)^6257
        have hw : |(5699563621/10000000000 : ℝ)|=(5699563621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_s1_5 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2619036503/5000000000 : ℝ)*x 0 + (-1790267143/10000000000 : ℝ)*x 1 + (2849781711/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2619036503/5000000000 : ℝ)^8305 ≤ (42388947065241/100000000000000 : ℝ)^6257 := by
    have hnat : (2619036503 : ℕ)^8305*100000000000000^6257 ≤ 42388947065241^6257*5000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619036503 5000000000 42388947065241 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1790267143/10000000000 : ℝ)^8305 ≤ (10195014149161/100000000000000 : ℝ)^6257 := by
    have hnat : (1790267143 : ℕ)^8305*100000000000000^6257 ≤ 10195014149161^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1790267143 10000000000 10195014149161 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2849781711/5000000000 : ℝ)^8305 ≤ (47416038770871/100000000000000 : ℝ)^6257 := by
    have hnat : (2849781711 : ℕ)^8305*100000000000000^6257 ≤ 47416038770871^6257*5000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2849781711 5000000000 47416038770871 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2619036503/5000000000 : ℝ), (-1790267143/10000000000 : ℝ), (2849781711/5000000000 : ℝ)] ![(42388947065241/100000000000000 : ℝ), (10195014149161/100000000000000 : ℝ), (47416038770871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2619036503/5000000000 : ℝ)|^8305 ≤ (42388947065241/100000000000000 : ℝ)^6257
        have hw : |(2619036503/5000000000 : ℝ)|=(2619036503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1790267143/10000000000 : ℝ)|^8305 ≤ (10195014149161/100000000000000 : ℝ)^6257
        have hw : |(-1790267143/10000000000 : ℝ)|=(1790267143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2849781711/5000000000 : ℝ)|^8305 ≤ (47416038770871/100000000000000 : ℝ)^6257
        have hw : |(2849781711/5000000000 : ℝ)|=(2849781711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_s1_6 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2619036517/5000000000 : ℝ)*x 0 + (2849781783/5000000000 : ℝ)*x 1 + (-447566723/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2619036517/5000000000 : ℝ)^8305 ≤ (10597236841499/25000000000000 : ℝ)^6257 := by
    have hnat : (2619036517 : ℕ)^8305*25000000000000^6257 ≤ 10597236841499^6257*5000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619036517 5000000000 10597236841499 25000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2849781783/5000000000 : ℝ)^8305 ≤ (23708020180477/50000000000000 : ℝ)^6257 := by
    have hnat : (2849781783 : ℕ)^8305*50000000000000^6257 ≤ 23708020180477^6257*5000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2849781783 5000000000 23708020180477 50000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (447566723/2500000000 : ℝ)^8305 ≤ (10195012251943/100000000000000 : ℝ)^6257 := by
    have hnat : (447566723 : ℕ)^8305*100000000000000^6257 ≤ 10195012251943^6257*2500000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447566723 2500000000 10195012251943 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2619036517/5000000000 : ℝ), (2849781783/5000000000 : ℝ), (-447566723/2500000000 : ℝ)] ![(10597236841499/25000000000000 : ℝ), (23708020180477/50000000000000 : ℝ), (10195012251943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2619036517/5000000000 : ℝ)|^8305 ≤ (10597236841499/25000000000000 : ℝ)^6257
        have hw : |(2619036517/5000000000 : ℝ)|=(2619036517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2849781783/5000000000 : ℝ)|^8305 ≤ (23708020180477/50000000000000 : ℝ)^6257
        have hw : |(2849781783/5000000000 : ℝ)|=(2849781783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-447566723/2500000000 : ℝ)|^8305 ≤ (10195012251943/100000000000000 : ℝ)^6257
        have hw : |(-447566723/2500000000 : ℝ)|=(447566723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_s1_7 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4321641701/10000000000 : ℝ)*x 0 + (506338997/1000000000 : ℝ)*x 1 + (3691228629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4321641701/10000000000 : ℝ)^8305 ≤ (32839135092441/100000000000000 : ℝ)^6257 := by
    have hnat : (4321641701 : ℕ)^8305*100000000000000^6257 ≤ 32839135092441^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4321641701 10000000000 32839135092441 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (506338997/1000000000 : ℝ)^8305 ≤ (5065369016021/12500000000000 : ℝ)^6257 := by
    have hnat : (506338997 : ℕ)^8305*12500000000000^6257 ≤ 5065369016021^6257*1000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506338997 1000000000 5065369016021 12500000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3691228629/10000000000 : ℝ)^8305 ≤ (13318956379529/50000000000000 : ℝ)^6257 := by
    have hnat : (3691228629 : ℕ)^8305*50000000000000^6257 ≤ 13318956379529^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3691228629 10000000000 13318956379529 50000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4321641701/10000000000 : ℝ), (506338997/1000000000 : ℝ), (3691228629/10000000000 : ℝ)] ![(32839135092441/100000000000000 : ℝ), (5065369016021/12500000000000 : ℝ), (13318956379529/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4321641701/10000000000 : ℝ)|^8305 ≤ (32839135092441/100000000000000 : ℝ)^6257
        have hw : |(4321641701/10000000000 : ℝ)|=(4321641701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(506338997/1000000000 : ℝ)|^8305 ≤ (5065369016021/12500000000000 : ℝ)^6257
        have hw : |(506338997/1000000000 : ℝ)|=(506338997/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3691228629/10000000000 : ℝ)|^8305 ≤ (13318956379529/50000000000000 : ℝ)^6257
        have hw : |(3691228629/10000000000 : ℝ)|=(3691228629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1112_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148888709/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27931/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (289/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (137/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (823/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27931/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (289/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27931/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (289/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27931/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (289/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27931/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (289/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27931/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (289/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27931/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (289/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (289/100000 : ℝ) ^ (519/128 : ℝ) ≤ (2533402683/50000000000000000000 : ℝ) := by
    have hpowers : (289/100000 : ℝ)^519 ≤ (2533402683/50000000000000000000 : ℝ)^128 := by
      have hnat : (289 : ℕ)^519*50000000000000000000^128 ≤ 2533402683^128*100000^519 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        289 100000 2533402683 50000000000000000000 519 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (289/100000 : ℝ)) (X := (2533402683/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 519 128 (by norm_num) hpowers
    exact h
  have hpowhi : (27931/100000 : ℝ) ^ (519/128 : ℝ) ≤ (283807454341172183/50000000000000000000 : ℝ) := by
    have hpowers : (27931/100000 : ℝ)^519 ≤ (283807454341172183/50000000000000000000 : ℝ)^128 := by
      have hnat : (27931 : ℕ)^519*50000000000000000000^128 ≤ 283807454341172183^128*100000^519 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27931 100000 283807454341172183 50000000000000000000 519 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27931/100000 : ℝ)) (X := (283807454341172183/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 519 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000002533402683/25000000000000000000 : ℝ) ≤ (2500000000062481/2500000000000000 : ℝ) ^ (519/128 : ℝ) := by
    have hpowers : (25000000002533402683/25000000000000000000 : ℝ)^128 ≤ (2500000000062481/2500000000000000 : ℝ)^519 := by
      have hnat : (25000000002533402683 : ℕ)^128*2500000000000000^519 ≤ 2500000000062481^519*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000002533402683 25000000000000000000 2500000000062481 2500000000000000 128 519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000000062481/2500000000000000 : ℝ)) (X := (25000000002533402683/25000000000000000000 : ℝ)) (by norm_num) 519 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (25141903728437287433/25000000000000000000 : ℝ) ≤ (80111753182917/80000000000000 : ℝ) ^ (519/128 : ℝ) := by
    have hpowers : (25141903728437287433/25000000000000000000 : ℝ)^128 ≤ (80111753182917/80000000000000 : ℝ)^519 := by
      have hnat : (25141903728437287433 : ℕ)^128*80000000000000^519 ≤ 80111753182917^519*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25141903728437287433 25000000000000000000 80111753182917 80000000000000 128 519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80111753182917/80000000000000 : ℝ)) (X := (25141903728437287433/25000000000000000000 : ℝ)) (by norm_num) 519 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (25283807454341172183/25000000000000000000 : ℝ) ≤ (5013969147739663/5000000000000000 : ℝ) ^ (519/128 : ℝ) := by
    have hpowers : (25283807454341172183/25000000000000000000 : ℝ)^128 ≤ (5013969147739663/5000000000000000 : ℝ)^519 := by
      have hnat : (25283807454341172183 : ℕ)^128*5000000000000000^519 ≤ 5013969147739663^519*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25283807454341172183 25000000000000000000 5013969147739663 5000000000000000 128 519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5013969147739663/5000000000000000 : ℝ)) (X := (25283807454341172183/25000000000000000000 : ℝ)) (by norm_num) 519 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2533402683/50000000000000000000 : ℝ) ≤ ((1625952504938747659/1626000000000000000 : ℝ)+2*(13969147614701/2764200000000000 : ℝ)*(289/100000 : ℝ))^(519/128 : ℝ) := by
    rw [show (1625952504938747659/1626000000000000000 : ℝ)+2*(13969147614701/2764200000000000 : ℝ)*(289/100000 : ℝ)=(2500000000062481/2500000000000000 : ℝ) by norm_num, show 1+2*(2533402683/50000000000000000000 : ℝ)=(25000000002533402683/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(283807454341172183/50000000000000000000 : ℝ)+(2533402683/50000000000000000000 : ℝ) ≤ ((1625952504938747659/1626000000000000000 : ℝ)+(13969147614701/2764200000000000 : ℝ)*((27931/100000 : ℝ)+(289/100000 : ℝ)))^(519/128 : ℝ) := by
    rw [show (1625952504938747659/1626000000000000000 : ℝ)+(13969147614701/2764200000000000 : ℝ)*((27931/100000 : ℝ)+(289/100000 : ℝ))=(80111753182917/80000000000000 : ℝ) by norm_num, show 1+(283807454341172183/50000000000000000000 : ℝ)+(2533402683/50000000000000000000 : ℝ)=(25141903728437287433/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(283807454341172183/50000000000000000000 : ℝ) ≤ ((1625952504938747659/1626000000000000000 : ℝ)+2*(13969147614701/2764200000000000 : ℝ)*(27931/100000 : ℝ))^(519/128 : ℝ) := by
    rw [show (1625952504938747659/1626000000000000000 : ℝ)+2*(13969147614701/2764200000000000 : ℝ)*(27931/100000 : ℝ)=(5013969147739663/5000000000000000 : ℝ) by norm_num, show 1+2*(283807454341172183/50000000000000000000 : ℝ)=(25283807454341172183/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1625952504938747659/1626000000000000000 : ℝ)*(X 1 0+X 2 0)+(13969147614701/2764200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (519/128 : ℝ)) (lo := (289/100000 : ℝ)) (hi := (27931/100000 : ℝ)) (c := (1625952504938747659/1626000000000000000 : ℝ)) (alpha := (13969147614701/2764200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1625952504938747659/1626000000000000000 : ℝ)*(X 0 1+X 2 1)+(13969147614701/2764200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (519/128 : ℝ)) (lo := (289/100000 : ℝ)) (hi := (27931/100000 : ℝ)) (c := (1625952504938747659/1626000000000000000 : ℝ)) (alpha := (13969147614701/2764200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1625952504938747659/1626000000000000000 : ℝ)*(X 0 2+X 1 2)+(13969147614701/2764200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (519/128 : ℝ)) (lo := (289/100000 : ℝ)) (hi := (27931/100000 : ℝ)) (c := (1625952504938747659/1626000000000000000 : ℝ)) (alpha := (13969147614701/2764200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-421633351/2000000000 : ℝ)*X 0 0+(2854809243/5000000000 : ℝ)*X 0 1+(499591523/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5420776417/10000000000 : ℝ)*X 1 0+(-1246957977/5000000000 : ℝ)*X 1 1+(499591517/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1084155549/2000000000 : ℝ)*X 2 0+(15612231/31250000 : ℝ)*X 2 1+(-623478953/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4319964187/10000000000 : ℝ)*X 0 0+(3671343249/10000000000 : ℝ)*X 0 1+(5082885479/10000000000 : ℝ)*X 0 2+(4319964187/10000000000 : ℝ)*X 1 0+(3671343249/10000000000 : ℝ)*X 1 1+(5082885479/10000000000 : ℝ)*X 1 2+(4319964187/10000000000 : ℝ)*X 2 0+(3671343249/10000000000 : ℝ)*X 2 1+(5082885479/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1054507899/5000000000 : ℝ)*X 0 0+(5005772901/10000000000 : ℝ)*X 0 1+(5699563621/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2619036503/5000000000 : ℝ)*X 1 0+(-1790267143/10000000000 : ℝ)*X 1 1+(2849781711/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2619036517/5000000000 : ℝ)*X 2 0+(2849781783/5000000000 : ℝ)*X 2 1+(-447566723/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4321641701/10000000000 : ℝ)*X 0 0+(506338997/1000000000 : ℝ)*X 0 1+(3691228629/10000000000 : ℝ)*X 0 2+(4321641701/10000000000 : ℝ)*X 1 0+(506338997/1000000000 : ℝ)*X 1 1+(3691228629/10000000000 : ℝ)*X 1 2+(4321641701/10000000000 : ℝ)*X 2 0+(506338997/1000000000 : ℝ)*X 2 1+(3691228629/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (128482705114541765367851/46070000000000000000000000000 : ℝ) := by norm_num
    linear_combination (224431321/100000000000000 : ℝ)*(base1) + (88424853/25000000000000 : ℝ)*(base19) + (72190921/10000000000000 : ℝ)*(base23) + (15104373/100000000000000 : ℝ)*(upper3) + (38203977/100000000000000 : ℝ)*(upper5) + (1054794526250521/100000000000000 : ℝ)*(major0) + (1054794526250521/100000000000000 : ℝ)*(major1) + (1054794526250521/100000000000000 : ℝ)*(major2) + (87571432193493/6250000000000 : ℝ)*(sp0) + (1401142924743853/100000000000000 : ℝ)*(sp1) + (1401143296885233/100000000000000 : ℝ)*(sp2) + (354222358156663/50000000000000 : ℝ)*(sp3) + (332032469/25000000000000 : ℝ)*(sp4) + (740351177/100000000000000 : ℝ)*(sp5) + (88555617593081/12500000000000 : ℝ)*(f.failure) + (1401144018794443/100000000000000 : ℝ)*(f.sum) + (111884468087681/138210000000000000000000000000 : ℝ)*base65 + (5868154106246624237/2764200000000000000000000000000000 : ℝ)*base68 + (10661543297729024237/2764200000000000000000000000000000 : ℝ)*base70 + (10513084678263975763/2764200000000000000000000000000000 : ℝ)*base71 + (269845557329989/138210000000000000000000000000 : ℝ)*base74 + (10212637884225375763/2764200000000000000000000000000000 : ℝ)*base75 + (11747585182891575763/2764200000000000000000000000000000 : ℝ)*base77 + (20547348413973824237/2764200000000000000000000000000000 : ℝ)*base80 + (194847401375959/138210000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (4922429/1250000000000000000000 : ℝ)*base89 + (4922429/1250000000000000000000 : ℝ)*base91 + (4922429/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1507803756491683177211299559/230350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3134459/4000000000000 : ℝ)*(base1) + (292411433/20000000000000 : ℝ)*(base19) + (297440957/20000000000000 : ℝ)*(base23) + (72279033/50000000000000 : ℝ)*(upper3) + (73582559/50000000000000 : ℝ)*(upper5) + (542533610516551/50000000000000 : ℝ)*(major0) + (542533610516551/50000000000000 : ℝ)*(major1) + (542533610516551/50000000000000 : ℝ)*(major2) + (2919389913/50000000000000 : ℝ)*(sp1) + (3169409543/50000000000000 : ℝ)*(sp2) + (180169616247927/12500000000000 : ℝ)*(sp4) + (1441349550784951/100000000000000 : ℝ)*(sp5) + (1441349025598071/100000000000000 : ℝ)*(sp6) + (182194323473131/25000000000000 : ℝ)*(sp7) + (364388686126999/50000000000000 : ℝ)*(f.failure) + (1441356851621941/100000000000000 : ℝ)*(f.sum) + (34030342570129/69105000000000000000000000000 : ℝ)*base66 + (15743899767375020147/1382100000000000000000000000000000 : ℝ)*base68 + (1911545589210620147/1382100000000000000000000000000000 : ℝ)*base70 + (8534376041544620147/1382100000000000000000000000000000 : ℝ)*base72 + (9282373001933/8638125000000000000000000000 : ℝ)*base74 + (20078024727643220147/1382100000000000000000000000000000 : ℝ)*base76 + (8005394316130220147/1382100000000000000000000000000000 : ℝ)*base78 + (25070792215404020147/1382100000000000000000000000000000 : ℝ)*base80 + (219158002382891/69105000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (8845709/5000000000000000000000 : ℝ)*base90 + (8845709/5000000000000000000000 : ℝ)*base92 + (8845709/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1112_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148888709/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27931/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (289/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (137/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (823/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1112_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1112_s2_0 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1689867/7812500 : ℝ)*x 0 + (5516621349/10000000000 : ℝ)*x 1 + (1288514301/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1689867/7812500 : ℝ)^8305 ≤ (3276118044323/25000000000000 : ℝ)^6257 := by
    have hnat : (1689867 : ℕ)^8305*25000000000000^6257 ≤ 3276118044323^6257*7812500^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1689867 7812500 3276118044323 25000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5516621349/10000000000 : ℝ)^8305 ≤ (5675829688289/12500000000000 : ℝ)^6257 := by
    have hnat : (5516621349 : ℕ)^8305*12500000000000^6257 ≤ 5675829688289^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5516621349 10000000000 5675829688289 12500000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1288514301/2500000000 : ℝ)^8305 ≤ (8297778061739/20000000000000 : ℝ)^6257 := by
    have hnat : (1288514301 : ℕ)^8305*20000000000000^6257 ≤ 8297778061739^6257*2500000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1288514301 2500000000 8297778061739 20000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1689867/7812500 : ℝ), (5516621349/10000000000 : ℝ), (1288514301/2500000000 : ℝ)] ![(3276118044323/25000000000000 : ℝ), (5675829688289/12500000000000 : ℝ), (8297778061739/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1689867/7812500 : ℝ)|^8305 ≤ (3276118044323/25000000000000 : ℝ)^6257
        have hw : |(-1689867/7812500 : ℝ)|=(1689867/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5516621349/10000000000 : ℝ)|^8305 ≤ (5675829688289/12500000000000 : ℝ)^6257
        have hw : |(5516621349/10000000000 : ℝ)|=(5516621349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1288514301/2500000000 : ℝ)|^8305 ≤ (8297778061739/20000000000000 : ℝ)^6257
        have hw : |(1288514301/2500000000 : ℝ)|=(1288514301/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_s2_1 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2687583381/5000000000 : ℝ)*x 0 + (-2351752123/10000000000 : ℝ)*x 1 + (2577029251/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2687583381/5000000000 : ℝ)^8305 ≤ (43867775295691/100000000000000 : ℝ)^6257 := by
    have hnat : (2687583381 : ℕ)^8305*100000000000000^6257 ≤ 43867775295691^6257*5000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687583381 5000000000 43867775295691 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2351752123/10000000000 : ℝ)^8305 ≤ (14643320513917/100000000000000 : ℝ)^6257 := by
    have hnat : (2351752123 : ℕ)^8305*100000000000000^6257 ≤ 14643320513917^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2351752123 10000000000 14643320513917 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2577029251/5000000000 : ℝ)^8305 ≤ (10372226044309/25000000000000 : ℝ)^6257 := by
    have hnat : (2577029251 : ℕ)^8305*25000000000000^6257 ≤ 10372226044309^6257*5000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2577029251 5000000000 10372226044309 25000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2687583381/5000000000 : ℝ), (-2351752123/10000000000 : ℝ), (2577029251/5000000000 : ℝ)] ![(43867775295691/100000000000000 : ℝ), (14643320513917/100000000000000 : ℝ), (10372226044309/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2687583381/5000000000 : ℝ)|^8305 ≤ (43867775295691/100000000000000 : ℝ)^6257
        have hw : |(2687583381/5000000000 : ℝ)|=(2687583381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2351752123/10000000000 : ℝ)|^8305 ≤ (14643320513917/100000000000000 : ℝ)^6257
        have hw : |(-2351752123/10000000000 : ℝ)|=(2351752123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2577029251/5000000000 : ℝ)|^8305 ≤ (10372226044309/25000000000000 : ℝ)^6257
        have hw : |(2577029251/5000000000 : ℝ)|=(2577029251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_s2_2 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (335947919/625000000 : ℝ)*x 0 + (16106433/31250000 : ℝ)*x 1 + (-587938031/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335947919/625000000 : ℝ)^8305 ≤ (2741735916713/6250000000000 : ℝ)^6257 := by
    have hnat : (335947919 : ℕ)^8305*6250000000000^6257 ≤ 2741735916713^6257*625000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335947919 625000000 2741735916713 6250000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16106433/31250000 : ℝ)^8305 ≤ (2074445239847/5000000000000 : ℝ)^6257 := by
    have hnat : (16106433 : ℕ)^8305*5000000000000^6257 ≤ 2074445239847^6257*31250000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16106433 31250000 2074445239847 5000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (587938031/2500000000 : ℝ)^8305 ≤ (14643320522181/100000000000000 : ℝ)^6257 := by
    have hnat : (587938031 : ℕ)^8305*100000000000000^6257 ≤ 14643320522181^6257*2500000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      587938031 2500000000 14643320522181 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335947919/625000000 : ℝ), (16106433/31250000 : ℝ), (-587938031/2500000000 : ℝ)] ![(2741735916713/6250000000000 : ℝ), (2074445239847/5000000000000 : ℝ), (14643320522181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335947919/625000000 : ℝ)|^8305 ≤ (2741735916713/6250000000000 : ℝ)^6257
        have hw : |(335947919/625000000 : ℝ)|=(335947919/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(16106433/31250000 : ℝ)|^8305 ≤ (2074445239847/5000000000000 : ℝ)^6257
        have hw : |(16106433/31250000 : ℝ)|=(16106433/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-587938031/2500000000 : ℝ)|^8305 ≤ (14643320522181/100000000000000 : ℝ)^6257
        have hw : |(-587938031/2500000000 : ℝ)|=(587938031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_s2_3 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (544690679/1250000000 : ℝ)*x 0 + (2006855169/5000000000 : ℝ)*x 1 + (4730777373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544690679/1250000000 : ℝ)^8305 ≤ (33201547192251/100000000000000 : ℝ)^6257 := by
    have hnat : (544690679 : ℕ)^8305*100000000000000^6257 ≤ 33201547192251^6257*1250000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544690679 1250000000 33201547192251 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2006855169/5000000000 : ℝ)^8305 ≤ (7442542688771/25000000000000 : ℝ)^6257 := by
    have hnat : (2006855169 : ℕ)^8305*25000000000000^6257 ≤ 7442542688771^6257*5000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2006855169 5000000000 7442542688771 25000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4730777373/10000000000 : ℝ)^8305 ≤ (37028282032311/100000000000000 : ℝ)^6257 := by
    have hnat : (4730777373 : ℕ)^8305*100000000000000^6257 ≤ 37028282032311^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4730777373 10000000000 37028282032311 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(544690679/1250000000 : ℝ), (2006855169/5000000000 : ℝ), (4730777373/10000000000 : ℝ)] ![(33201547192251/100000000000000 : ℝ), (7442542688771/25000000000000 : ℝ), (37028282032311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(544690679/1250000000 : ℝ)|^8305 ≤ (33201547192251/100000000000000 : ℝ)^6257
        have hw : |(544690679/1250000000 : ℝ)|=(544690679/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2006855169/5000000000 : ℝ)|^8305 ≤ (7442542688771/25000000000000 : ℝ)^6257
        have hw : |(2006855169/5000000000 : ℝ)|=(2006855169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4730777373/10000000000 : ℝ)|^8305 ≤ (37028282032311/100000000000000 : ℝ)^6257
        have hw : |(4730777373/10000000000 : ℝ)|=(4730777373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_s2_4 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2163140727/10000000000 : ℝ)*x 0 + (5156610877/10000000000 : ℝ)*x 1 + (86156903/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163140727/10000000000 : ℝ)^8305 ≤ (2621072902493/20000000000000 : ℝ)^6257 := by
    have hnat : (2163140727 : ℕ)^8305*20000000000000^6257 ≤ 2621072902493^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163140727 10000000000 2621072902493 20000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5156610877/10000000000 : ℝ)^8305 ≤ (41516177357103/100000000000000 : ℝ)^6257 := by
    have hnat : (5156610877 : ℕ)^8305*100000000000000^6257 ≤ 41516177357103^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5156610877 10000000000 41516177357103 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (86156903/156250000 : ℝ)^8305 ≤ (9075691623909/20000000000000 : ℝ)^6257 := by
    have hnat : (86156903 : ℕ)^8305*20000000000000^6257 ≤ 9075691623909^6257*156250000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86156903 156250000 9075691623909 20000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2163140727/10000000000 : ℝ), (5156610877/10000000000 : ℝ), (86156903/156250000 : ℝ)] ![(2621072902493/20000000000000 : ℝ), (41516177357103/100000000000000 : ℝ), (9075691623909/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2163140727/10000000000 : ℝ)|^8305 ≤ (2621072902493/20000000000000 : ℝ)^6257
        have hw : |(-2163140727/10000000000 : ℝ)|=(2163140727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5156610877/10000000000 : ℝ)|^8305 ≤ (41516177357103/100000000000000 : ℝ)^6257
        have hw : |(5156610877/10000000000 : ℝ)|=(5156610877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(86156903/156250000 : ℝ)|^8305 ≤ (9075691623909/20000000000000 : ℝ)^6257
        have hw : |(86156903/156250000 : ℝ)|=(86156903/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_s2_5 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5283360203/10000000000 : ℝ)*x 0 + (-995884103/5000000000 : ℝ)*x 1 + (8822467/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5283360203/10000000000 : ℝ)^8305 ≤ (4287607483193/10000000000000 : ℝ)^6257 := by
    have hnat : (5283360203 : ℕ)^8305*10000000000000^6257 ≤ 4287607483193^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5283360203 10000000000 4287607483193 10000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (995884103/5000000000 : ℝ)^8305 ≤ (2349093226163/20000000000000 : ℝ)^6257 := by
    have hnat : (995884103 : ℕ)^8305*20000000000000^6257 ≤ 2349093226163^6257*5000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      995884103 5000000000 2349093226163 20000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8822467/16000000 : ℝ)^8305 ≤ (45378459026177/100000000000000 : ℝ)^6257 := by
    have hnat : (8822467 : ℕ)^8305*100000000000000^6257 ≤ 45378459026177^6257*16000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8822467 16000000 45378459026177 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5283360203/10000000000 : ℝ), (-995884103/5000000000 : ℝ), (8822467/16000000 : ℝ)] ![(4287607483193/10000000000000 : ℝ), (2349093226163/20000000000000 : ℝ), (45378459026177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5283360203/10000000000 : ℝ)|^8305 ≤ (4287607483193/10000000000000 : ℝ)^6257
        have hw : |(5283360203/10000000000 : ℝ)|=(5283360203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-995884103/5000000000 : ℝ)|^8305 ≤ (2349093226163/20000000000000 : ℝ)^6257
        have hw : |(-995884103/5000000000 : ℝ)|=(995884103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8822467/16000000 : ℝ)|^8305 ≤ (45378459026177/100000000000000 : ℝ)^6257
        have hw : |(8822467/16000000 : ℝ)|=(8822467/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_s2_6 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2641680167/5000000000 : ℝ)*x 0 + (5514041823/10000000000 : ℝ)*x 1 + (-995884049/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2641680167/5000000000 : ℝ)^8305 ≤ (42876076243003/100000000000000 : ℝ)^6257 := by
    have hnat : (2641680167 : ℕ)^8305*100000000000000^6257 ≤ 42876076243003^6257*5000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641680167 5000000000 42876076243003 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5514041823/10000000000 : ℝ)^8305 ≤ (45378458458167/100000000000000 : ℝ)^6257 := by
    have hnat : (5514041823 : ℕ)^8305*100000000000000^6257 ≤ 45378458458167^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5514041823 10000000000 45378458458167 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (995884049/5000000000 : ℝ)^8305 ≤ (293636632137/2500000000000 : ℝ)^6257 := by
    have hnat : (995884049 : ℕ)^8305*2500000000000^6257 ≤ 293636632137^6257*5000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      995884049 5000000000 293636632137 2500000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2641680167/5000000000 : ℝ), (5514041823/10000000000 : ℝ), (-995884049/5000000000 : ℝ)] ![(42876076243003/100000000000000 : ℝ), (45378458458167/100000000000000 : ℝ), (293636632137/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2641680167/5000000000 : ℝ)|^8305 ≤ (42876076243003/100000000000000 : ℝ)^6257
        have hw : |(2641680167/5000000000 : ℝ)|=(2641680167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5514041823/10000000000 : ℝ)|^8305 ≤ (45378458458167/100000000000000 : ℝ)^6257
        have hw : |(5514041823/10000000000 : ℝ)|=(5514041823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-995884049/5000000000 : ℝ)|^8305 ≤ (293636632137/2500000000000 : ℝ)^6257
        have hw : |(-995884049/5000000000 : ℝ)|=(995884049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_s2_7 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4357746271/10000000000 : ℝ)*x 0 + (236286401/500000000 : ℝ)*x 1 + (4018809943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4357746271/10000000000 : ℝ)^8305 ≤ (6640756123321/20000000000000 : ℝ)^6257 := by
    have hnat : (4357746271 : ℕ)^8305*20000000000000^6257 ≤ 6640756123321^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357746271 10000000000 6640756123321 20000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (236286401/500000000 : ℝ)^8305 ≤ (4621979171783/12500000000000 : ℝ)^6257 := by
    have hnat : (236286401 : ℕ)^8305*12500000000000^6257 ≤ 4621979171783^6257*500000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      236286401 500000000 4621979171783 12500000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4018809943/10000000000 : ℝ)^8305 ≤ (3727548250039/12500000000000 : ℝ)^6257 := by
    have hnat : (4018809943 : ℕ)^8305*12500000000000^6257 ≤ 3727548250039^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4018809943 10000000000 3727548250039 12500000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4357746271/10000000000 : ℝ), (236286401/500000000 : ℝ), (4018809943/10000000000 : ℝ)] ![(6640756123321/20000000000000 : ℝ), (4621979171783/12500000000000 : ℝ), (3727548250039/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4357746271/10000000000 : ℝ)|^8305 ≤ (6640756123321/20000000000000 : ℝ)^6257
        have hw : |(4357746271/10000000000 : ℝ)|=(4357746271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(236286401/500000000 : ℝ)|^8305 ≤ (4621979171783/12500000000000 : ℝ)^6257
        have hw : |(236286401/500000000 : ℝ)|=(236286401/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4018809943/10000000000 : ℝ)|^8305 ≤ (3727548250039/12500000000000 : ℝ)^6257
        have hw : |(4018809943/10000000000 : ℝ)|=(4018809943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1112_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148888709/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (823/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (137/2500 : ℝ)*pair X i i ≤ pair X i h) :
    (2233/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8297/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (823/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (137/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (823/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (137/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (823/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (137/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (823/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (137/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (823/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (137/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (823/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (137/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (137/2500 : ℝ) ^ (519/128 : ℝ) ≤ (38469744336309/5000000000000000000 : ℝ) := by
    have hpowers : (137/2500 : ℝ)^519 ≤ (38469744336309/5000000000000000000 : ℝ)^128 := by
      have hnat : (137 : ℕ)^519*5000000000000000000^128 ≤ 38469744336309^128*2500^519 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        137 2500 38469744336309 5000000000000000000 519 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (137/2500 : ℝ)) (X := (38469744336309/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 519 128 (by norm_num) hpowers
    exact h
  have hpowhi : (823/4000 : ℝ) ^ (519/128 : ℝ) ≤ (164364358192471623/100000000000000000000 : ℝ) := by
    have hpowers : (823/4000 : ℝ)^519 ≤ (164364358192471623/100000000000000000000 : ℝ)^128 := by
      have hnat : (823 : ℕ)^519*100000000000000000000^128 ≤ 164364358192471623^128*4000^519 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        823 4000 164364358192471623 100000000000000000000 519 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (823/4000 : ℝ)) (X := (164364358192471623/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 519 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500038469744336309/2500000000000000000 : ℝ) ≤ (1000003795066461/1000000000000000 : ℝ) ^ (519/128 : ℝ) := by
    have hpowers : (2500038469744336309/2500000000000000000 : ℝ)^128 ≤ (1000003795066461/1000000000000000 : ℝ)^519 := by
      have hnat : (2500038469744336309 : ℕ)^128*1000000000000000^519 ≤ 1000003795066461^519*2500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500038469744336309 2500000000000000000 1000003795066461 1000000000000000 128 519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000003795066461/1000000000000000 : ℝ)) (X := (2500038469744336309/2500000000000000000 : ℝ)) (by norm_num) 519 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100165133753079197803/100000000000000000000 : ℝ) ≤ (10004070131989899/10000000000000000 : ℝ) ^ (519/128 : ℝ) := by
    have hpowers : (100165133753079197803/100000000000000000000 : ℝ)^128 ≤ (10004070131989899/10000000000000000 : ℝ)^519 := by
      have hnat : (100165133753079197803 : ℕ)^128*10000000000000000^519 ≤ 10004070131989899^519*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100165133753079197803 100000000000000000000 10004070131989899 10000000000000000 128 519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004070131989899/10000000000000000 : ℝ)) (X := (100165133753079197803/100000000000000000000 : ℝ)) (by norm_num) 519 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50164364358192471623/50000000000000000000 : ℝ) ≤ (2502025578328797/2500000000000000 : ℝ) ^ (519/128 : ℝ) := by
    have hpowers : (50164364358192471623/50000000000000000000 : ℝ)^128 ≤ (2502025578328797/2500000000000000 : ℝ)^519 := by
      have hnat : (50164364358192471623 : ℕ)^128*2500000000000000^519 ≤ 2502025578328797^519*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50164364358192471623 50000000000000000000 2502025578328797 2500000000000000 128 519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2502025578328797/2500000000000000 : ℝ)) (X := (50164364358192471623/50000000000000000000 : ℝ)) (by norm_num) 519 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(38469744336309/5000000000000000000 : ℝ) ≤ ((15090638015795712051/15095000000000000000 : ℝ)+2*(4032181325289/1509500000000000 : ℝ)*(137/2500 : ℝ))^(519/128 : ℝ) := by
    rw [show (15090638015795712051/15095000000000000000 : ℝ)+2*(4032181325289/1509500000000000 : ℝ)*(137/2500 : ℝ)=(1000003795066461/1000000000000000 : ℝ) by norm_num, show 1+2*(38469744336309/5000000000000000000 : ℝ)=(2500038469744336309/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(164364358192471623/100000000000000000000 : ℝ)+(38469744336309/5000000000000000000 : ℝ) ≤ ((15090638015795712051/15095000000000000000 : ℝ)+(4032181325289/1509500000000000 : ℝ)*((823/4000 : ℝ)+(137/2500 : ℝ)))^(519/128 : ℝ) := by
    rw [show (15090638015795712051/15095000000000000000 : ℝ)+(4032181325289/1509500000000000 : ℝ)*((823/4000 : ℝ)+(137/2500 : ℝ))=(10004070131989899/10000000000000000 : ℝ) by norm_num, show 1+(164364358192471623/100000000000000000000 : ℝ)+(38469744336309/5000000000000000000 : ℝ)=(100165133753079197803/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(164364358192471623/100000000000000000000 : ℝ) ≤ ((15090638015795712051/15095000000000000000 : ℝ)+2*(4032181325289/1509500000000000 : ℝ)*(823/4000 : ℝ))^(519/128 : ℝ) := by
    rw [show (15090638015795712051/15095000000000000000 : ℝ)+2*(4032181325289/1509500000000000 : ℝ)*(823/4000 : ℝ)=(2502025578328797/2500000000000000 : ℝ) by norm_num, show 1+2*(164364358192471623/100000000000000000000 : ℝ)=(50164364358192471623/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15090638015795712051/15095000000000000000 : ℝ)*(X 1 0+X 2 0)+(4032181325289/1509500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (519/128 : ℝ)) (lo := (137/2500 : ℝ)) (hi := (823/4000 : ℝ)) (c := (15090638015795712051/15095000000000000000 : ℝ)) (alpha := (4032181325289/1509500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15090638015795712051/15095000000000000000 : ℝ)*(X 0 1+X 2 1)+(4032181325289/1509500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (519/128 : ℝ)) (lo := (137/2500 : ℝ)) (hi := (823/4000 : ℝ)) (c := (15090638015795712051/15095000000000000000 : ℝ)) (alpha := (4032181325289/1509500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15090638015795712051/15095000000000000000 : ℝ)*(X 0 2+X 1 2)+(4032181325289/1509500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (519/128 : ℝ)) (lo := (137/2500 : ℝ)) (hi := (823/4000 : ℝ)) (c := (15090638015795712051/15095000000000000000 : ℝ)) (alpha := (4032181325289/1509500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1689867/7812500 : ℝ)*X 0 0+(5516621349/10000000000 : ℝ)*X 0 1+(1288514301/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2687583381/5000000000 : ℝ)*X 1 0+(-2351752123/10000000000 : ℝ)*X 1 1+(2577029251/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((335947919/625000000 : ℝ)*X 2 0+(16106433/31250000 : ℝ)*X 2 1+(-587938031/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((544690679/1250000000 : ℝ)*X 0 0+(2006855169/5000000000 : ℝ)*X 0 1+(4730777373/10000000000 : ℝ)*X 0 2+(544690679/1250000000 : ℝ)*X 1 0+(2006855169/5000000000 : ℝ)*X 1 1+(4730777373/10000000000 : ℝ)*X 1 2+(544690679/1250000000 : ℝ)*X 2 0+(2006855169/5000000000 : ℝ)*X 2 1+(4730777373/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2163140727/10000000000 : ℝ)*X 0 0+(5156610877/10000000000 : ℝ)*X 0 1+(86156903/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5283360203/10000000000 : ℝ)*X 1 0+(-995884103/5000000000 : ℝ)*X 1 1+(8822467/16000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2641680167/5000000000 : ℝ)*X 2 0+(5514041823/10000000000 : ℝ)*X 2 1+(-995884049/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4357746271/10000000000 : ℝ)*X 0 0+(236286401/500000000 : ℝ)*X 0 1+(4018809943/10000000000 : ℝ)*X 0 2+(4357746271/10000000000 : ℝ)*X 1 0+(236286401/500000000 : ℝ)*X 1 1+(4018809943/10000000000 : ℝ)*X 1 2+(4357746271/10000000000 : ℝ)*X 2 0+(236286401/500000000 : ℝ)*X 2 1+(4018809943/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (319746148385434053399453/37737500000000000000000000000 : ℝ) := by norm_num
    linear_combination (490261167/50000000000000 : ℝ)*(base19) + (353295191/50000000000000 : ℝ)*(base23) + (56809641/25000000000000 : ℝ)*(upper3) + (131245621/100000000000000 : ℝ)*(upper4) + (32787843/100000000000000 : ℝ)*(upper5) + (519093824050917/25000000000000 : ℝ)*(major0) + (519093824050917/25000000000000 : ℝ)*(major1) + (519093824050917/25000000000000 : ℝ)*(major2) + (689537842544911/25000000000000 : ℝ)*(sp0) + (344770902710621/12500000000000 : ℝ)*(sp1) + (68954187390423/2500000000000 : ℝ)*(sp2) + (87160936040493/6250000000000 : ℝ)*(sp3) + (8416013829/50000000000000 : ℝ)*(sp4) + (7131122063/100000000000000 : ℝ)*(sp7) + (27891642155399/2000000000000 : ℝ)*(f.failure) + (1379084101103651/50000000000000 : ℝ)*(f.sum) + (116334935909373/75475000000000000000000000000 : ℝ)*base66 + (1446291273717119233/377375000000000000000000000000000 : ℝ)*base68 + (2746374442100255767/377375000000000000000000000000000 : ℝ)*base69 + (765967365345255767/377375000000000000000000000000000 : ℝ)*base71 + (52796865637681/9434375000000000000000000000 : ℝ)*base74 + (2099784520531744233/377375000000000000000000000000000 : ℝ)*base76 + (1258668895943255767/377375000000000000000000000000000 : ℝ)*base77 + (5123274541489869233/377375000000000000000000000000000 : ℝ)*base80 + (144458309522377/75475000000000000000000000000 : ℝ)*base81 + (1510109/200000000000000000000 : ℝ)*base90 + (1510109/200000000000000000000 : ℝ)*base92 + (1510109/200000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2784998424742035084856873839/377375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1479764877/100000000000000 : ℝ)*(base19) + (423880423/25000000000000 : ℝ)*(base23) + (98903677/50000000000000 : ℝ)*(upper3) + (52134247/100000000000000 : ℝ)*(lower4) + (141007811/100000000000000 : ℝ)*(upper5) + (2106167039964537/100000000000000 : ℝ)*(major0) + (2106167039964537/100000000000000 : ℝ)*(major1) + (2106167039964537/100000000000000 : ℝ)*(major2) + (13590356427/100000000000000 : ℝ)*(sp1) + (16336103253/100000000000000 : ℝ)*(sp2) + (349717790231031/12500000000000 : ℝ)*(sp4) + (87428976616467/3125000000000 : ℝ)*(sp5) + (1398862145111651/50000000000000 : ℝ)*(sp6) + (1414591512083389/100000000000000 : ℝ)*(sp7) + (1414591512083389/100000000000000 : ℝ)*(f.failure) + (349717790231031/12500000000000 : ℝ)*(f.sum) + (5757995347101/2358593750000000000000000000 : ℝ)*base66 + (12559345871656534613/1509500000000000000000000000000000 : ℝ)*base68 + (3687758920156965387/1509500000000000000000000000000000 : ℝ)*base69 + (3361911937427965387/1509500000000000000000000000000000 : ℝ)*base71 + (2679987464269/589648437500000000000000000 : ℝ)*base74 + (5321804839745965387/1509500000000000000000000000000000 : ℝ)*base75 + (7399670507674965387/1509500000000000000000000000000000 : ℝ)*base77 + (10044719646908465387/1509500000000000000000000000000000 : ℝ)*base79 + (11695370546021/9434375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (11445199/10000000000000000000000 : ℝ)*base90 + (11445199/10000000000000000000000 : ℝ)*base92 + (11445199/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1112_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148888709/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (823/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (137/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2233/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8297/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1112_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1112_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148888709/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2233/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8297/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1112_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1112_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1112_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148888709/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2233/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8297/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1112_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

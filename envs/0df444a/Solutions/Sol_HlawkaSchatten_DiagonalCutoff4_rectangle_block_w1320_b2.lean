-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1320_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:43:01.791105+00:00
-- url     : https://prove2.me/submissions/55b02285-b9d0-4173-8ab2-20ca409c4cfa

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
theorem support_rectangle_w1320_s6_0 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2063123373/10000000000 : ℝ)*x 0 + (108277291/200000000 : ℝ)*x 1 + (5243888931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2063123373/10000000000 : ℝ)^535 ≤ (12558735118487/100000000000000 : ℝ)^407 := by
    have hnat : (2063123373 : ℕ)^535*100000000000000^407 ≤ 12558735118487^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063123373 10000000000 12558735118487 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108277291/200000000 : ℝ)^535 ≤ (22318574128133/50000000000000 : ℝ)^407 := by
    have hnat : (108277291 : ℕ)^535*50000000000000^407 ≤ 22318574128133^407*200000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108277291 200000000 22318574128133 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243888931/10000000000 : ℝ)^535 ≤ (5350514576693/12500000000000 : ℝ)^407 := by
    have hnat : (5243888931 : ℕ)^535*12500000000000^407 ≤ 5350514576693^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243888931 10000000000 5350514576693 12500000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2063123373/10000000000 : ℝ), (108277291/200000000 : ℝ), (5243888931/10000000000 : ℝ)] ![(12558735118487/100000000000000 : ℝ), (22318574128133/50000000000000 : ℝ), (5350514576693/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2063123373/10000000000 : ℝ)|^535 ≤ (12558735118487/100000000000000 : ℝ)^407
        have hw : |(-2063123373/10000000000 : ℝ)|=(2063123373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(108277291/200000000 : ℝ)|^535 ≤ (22318574128133/50000000000000 : ℝ)^407
        have hw : |(108277291/200000000 : ℝ)|=(108277291/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243888931/10000000000 : ℝ)|^535 ≤ (5350514576693/12500000000000 : ℝ)^407
        have hw : |(5243888931/10000000000 : ℝ)|=(5243888931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s6_1 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1069874421/2000000000 : ℝ)*x 0 + (-2149745539/10000000000 : ℝ)*x 1 + (5243889023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069874421/2000000000 : ℝ)^535 ≤ (1098487329793/2500000000000 : ℝ)^407 := by
    have hnat : (1069874421 : ℕ)^535*2500000000000^407 ≤ 1098487329793^407*2000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069874421 2000000000 1098487329793 2500000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2149745539/10000000000 : ℝ)^535 ≤ (1325638919689/10000000000000 : ℝ)^407 := by
    have hnat : (2149745539 : ℕ)^535*10000000000000^407 ≤ 1325638919689^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149745539 10000000000 1325638919689 10000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243889023/10000000000 : ℝ)^535 ≤ (21402058800343/50000000000000 : ℝ)^407 := by
    have hnat : (5243889023 : ℕ)^535*50000000000000^407 ≤ 21402058800343^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243889023 10000000000 21402058800343 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069874421/2000000000 : ℝ), (-2149745539/10000000000 : ℝ), (5243889023/10000000000 : ℝ)] ![(1098487329793/2500000000000 : ℝ), (1325638919689/10000000000000 : ℝ), (21402058800343/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069874421/2000000000 : ℝ)|^535 ≤ (1098487329793/2500000000000 : ℝ)^407
        have hw : |(1069874421/2000000000 : ℝ)|=(1069874421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2149745539/10000000000 : ℝ)|^535 ≤ (1325638919689/10000000000000 : ℝ)^407
        have hw : |(-2149745539/10000000000 : ℝ)|=(2149745539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243889023/10000000000 : ℝ)|^535 ≤ (21402058800343/50000000000000 : ℝ)^407
        have hw : |(5243889023/10000000000 : ℝ)|=(5243889023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s6_2 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2674686099/5000000000 : ℝ)*x 0 + (5243888793/10000000000 : ℝ)*x 1 + (-2149745719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674686099/5000000000 : ℝ)^535 ≤ (2196974709793/5000000000000 : ℝ)^407 := by
    have hnat : (2674686099 : ℕ)^535*5000000000000^407 ≤ 2196974709793^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674686099 5000000000 2196974709793 5000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243888793/10000000000 : ℝ)^535 ≤ (42804115132833/100000000000000 : ℝ)^407 := by
    have hnat : (5243888793 : ℕ)^535*100000000000000^407 ≤ 42804115132833^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243888793 10000000000 42804115132833 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2149745719/10000000000 : ℝ)^535 ≤ (13256390655939/100000000000000 : ℝ)^407 := by
    have hnat : (2149745719 : ℕ)^535*100000000000000^407 ≤ 13256390655939^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149745719 10000000000 13256390655939 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674686099/5000000000 : ℝ), (5243888793/10000000000 : ℝ), (-2149745719/10000000000 : ℝ)] ![(2196974709793/5000000000000 : ℝ), (42804115132833/100000000000000 : ℝ), (13256390655939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674686099/5000000000 : ℝ)|^535 ≤ (2196974709793/5000000000000 : ℝ)^407
        have hw : |(2674686099/5000000000 : ℝ)|=(2674686099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243888793/10000000000 : ℝ)|^535 ≤ (42804115132833/100000000000000 : ℝ)^407
        have hw : |(5243888793/10000000000 : ℝ)|=(5243888793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2149745719/10000000000 : ℝ)|^535 ≤ (13256390655939/100000000000000 : ℝ)^407
        have hw : |(-2149745719/10000000000 : ℝ)|=(2149745719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s6_3 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (270775139/625000000 : ℝ)*x 0 + (415925669/1000000000 : ℝ)*x 1 + (902467593/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270775139/625000000 : ℝ)^535 ≤ (8325710695563/25000000000000 : ℝ)^407 := by
    have hnat : (270775139 : ℕ)^535*25000000000000^407 ≤ 8325710695563^407*625000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270775139 625000000 8325710695563 25000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (415925669/1000000000 : ℝ)^535 ≤ (3156440252559/10000000000000 : ℝ)^407 := by
    have hnat : (415925669 : ℕ)^535*10000000000000^407 ≤ 3156440252559^407*1000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415925669 1000000000 3156440252559 10000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (902467593/2000000000 : ℝ)^535 ≤ (70265509357/200000000000 : ℝ)^407 := by
    have hnat : (902467593 : ℕ)^535*200000000000^407 ≤ 70265509357^407*2000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902467593 2000000000 70265509357 200000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(270775139/625000000 : ℝ), (415925669/1000000000 : ℝ), (902467593/2000000000 : ℝ)] ![(8325710695563/25000000000000 : ℝ), (3156440252559/10000000000000 : ℝ), (70265509357/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(270775139/625000000 : ℝ)|^535 ≤ (8325710695563/25000000000000 : ℝ)^407
        have hw : |(270775139/625000000 : ℝ)|=(270775139/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(415925669/1000000000 : ℝ)|^535 ≤ (3156440252559/10000000000000 : ℝ)^407
        have hw : |(415925669/1000000000 : ℝ)|=(415925669/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(902467593/2000000000 : ℝ)|^535 ≤ (70265509357/200000000000 : ℝ)^407
        have hw : |(902467593/2000000000 : ℝ)|=(902467593/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s6_4 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-412627307/2000000000 : ℝ)*x 0 + (5244496309/10000000000 : ℝ)*x 1 + (1082650699/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (412627307/2000000000 : ℝ)^535 ≤ (3139710109109/25000000000000 : ℝ)^407 := by
    have hnat : (412627307 : ℕ)^535*25000000000000^407 ≤ 3139710109109^407*2000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412627307 2000000000 3139710109109 25000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244496309/10000000000 : ℝ)^535 ≤ (42810633773701/100000000000000 : ℝ)^407 := by
    have hnat : (5244496309 : ℕ)^535*100000000000000^407 ≤ 42810633773701^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244496309 10000000000 42810633773701 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082650699/2000000000 : ℝ)^535 ≤ (44630525770681/100000000000000 : ℝ)^407 := by
    have hnat : (1082650699 : ℕ)^535*100000000000000^407 ≤ 44630525770681^407*2000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082650699 2000000000 44630525770681 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-412627307/2000000000 : ℝ), (5244496309/10000000000 : ℝ), (1082650699/2000000000 : ℝ)] ![(3139710109109/25000000000000 : ℝ), (42810633773701/100000000000000 : ℝ), (44630525770681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-412627307/2000000000 : ℝ)|^535 ≤ (3139710109109/25000000000000 : ℝ)^407
        have hw : |(-412627307/2000000000 : ℝ)|=(412627307/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244496309/10000000000 : ℝ)|^535 ≤ (42810633773701/100000000000000 : ℝ)^407
        have hw : |(5244496309/10000000000 : ℝ)|=(5244496309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082650699/2000000000 : ℝ)|^535 ≤ (44630525770681/100000000000000 : ℝ)^407
        have hw : |(1082650699/2000000000 : ℝ)|=(1082650699/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s6_5 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2652852031/5000000000 : ℝ)*x 0 + (-990190137/5000000000 : ℝ)*x 1 + (5413253529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652852031/5000000000 : ℝ)^535 ≤ (10867151615407/25000000000000 : ℝ)^407 := by
    have hnat : (2652852031 : ℕ)^535*25000000000000^407 ≤ 10867151615407^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652852031 5000000000 10867151615407 25000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (990190137/5000000000 : ℝ)^535 ≤ (2380173477053/20000000000000 : ℝ)^407 := by
    have hnat : (990190137 : ℕ)^535*20000000000000^407 ≤ 2380173477053^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      990190137 5000000000 2380173477053 20000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413253529/10000000000 : ℝ)^535 ≤ (44630526139159/100000000000000 : ℝ)^407 := by
    have hnat : (5413253529 : ℕ)^535*100000000000000^407 ≤ 44630526139159^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413253529 10000000000 44630526139159 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652852031/5000000000 : ℝ), (-990190137/5000000000 : ℝ), (5413253529/10000000000 : ℝ)] ![(10867151615407/25000000000000 : ℝ), (2380173477053/20000000000000 : ℝ), (44630526139159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652852031/5000000000 : ℝ)|^535 ≤ (10867151615407/25000000000000 : ℝ)^407
        have hw : |(2652852031/5000000000 : ℝ)|=(2652852031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-990190137/5000000000 : ℝ)|^535 ≤ (2380173477053/20000000000000 : ℝ)^407
        have hw : |(-990190137/5000000000 : ℝ)|=(990190137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413253529/10000000000 : ℝ)|^535 ≤ (44630526139159/100000000000000 : ℝ)^407
        have hw : |(5413253529/10000000000 : ℝ)|=(5413253529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s6_6 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1061140807/2000000000 : ℝ)*x 0 + (135331331/250000000 : ℝ)*x 1 + (-495095177/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061140807/2000000000 : ℝ)^535 ≤ (21734303085427/50000000000000 : ℝ)^407 := by
    have hnat : (1061140807 : ℕ)^535*50000000000000^407 ≤ 21734303085427^407*2000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061140807 2000000000 21734303085427 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135331331/250000000 : ℝ)^535 ≤ (22315261503547/50000000000000 : ℝ)^407 := by
    have hnat : (135331331 : ℕ)^535*50000000000000^407 ≤ 22315261503547^407*250000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135331331 250000000 22315261503547 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (495095177/2500000000 : ℝ)^535 ≤ (92975553231/781250000000 : ℝ)^407 := by
    have hnat : (495095177 : ℕ)^535*781250000000^407 ≤ 92975553231^407*2500000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      495095177 2500000000 92975553231 781250000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061140807/2000000000 : ℝ), (135331331/250000000 : ℝ), (-495095177/2500000000 : ℝ)] ![(21734303085427/50000000000000 : ℝ), (22315261503547/50000000000000 : ℝ), (92975553231/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061140807/2000000000 : ℝ)|^535 ≤ (21734303085427/50000000000000 : ℝ)^407
        have hw : |(1061140807/2000000000 : ℝ)|=(1061140807/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(135331331/250000000 : ℝ)|^535 ≤ (22315261503547/50000000000000 : ℝ)^407
        have hw : |(135331331/250000000 : ℝ)|=(135331331/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-495095177/2500000000 : ℝ)|^535 ≤ (92975553231/781250000000 : ℝ)^407
        have hw : |(-495095177/2500000000 : ℝ)|=(495095177/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s6_7 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4332428467/10000000000 : ℝ)*x 0 + (4511075491/10000000000 : ℝ)*x 1 + (4160525233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4332428467/10000000000 : ℝ)^535 ≤ (33303107953117/100000000000000 : ℝ)^407 := by
    have hnat : (4332428467 : ℕ)^535*100000000000000^407 ≤ 33303107953117^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4332428467 10000000000 33303107953117 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4511075491/10000000000 : ℝ)^535 ≤ (351198343579/1000000000000 : ℝ)^407 := by
    have hnat : (4511075491 : ℕ)^535*1000000000000^407 ≤ 351198343579^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4511075491 10000000000 351198343579 1000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4160525233/10000000000 : ℝ)^535 ≤ (31577057673977/100000000000000 : ℝ)^407 := by
    have hnat : (4160525233 : ℕ)^535*100000000000000^407 ≤ 31577057673977^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4160525233 10000000000 31577057673977 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4332428467/10000000000 : ℝ), (4511075491/10000000000 : ℝ), (4160525233/10000000000 : ℝ)] ![(33303107953117/100000000000000 : ℝ), (351198343579/1000000000000 : ℝ), (31577057673977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4332428467/10000000000 : ℝ)|^535 ≤ (33303107953117/100000000000000 : ℝ)^407
        have hw : |(4332428467/10000000000 : ℝ)|=(4332428467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4511075491/10000000000 : ℝ)|^535 ≤ (351198343579/1000000000000 : ℝ)^407
        have hw : |(4511075491/10000000000 : ℝ)|=(4511075491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4160525233/10000000000 : ℝ)|^535 ≤ (31577057673977/100000000000000 : ℝ)^407
        have hw : |(4160525233/10000000000 : ℝ)|=(4160525233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1320_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153862399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14703/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11087/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1387/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7347/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14703/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11087/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14703/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11087/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14703/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11087/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14703/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11087/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14703/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11087/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14703/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11087/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11087/100000 : ℝ) ^ (4279/1024 : ℝ) ≤ (2549728989347223/25000000000000000000 : ℝ) := by
    have hpowers : (11087/100000 : ℝ)^4279 ≤ (2549728989347223/25000000000000000000 : ℝ)^1024 := by
      have hnat : (11087 : ℕ)^4279*25000000000000000000^1024 ≤ 2549728989347223^1024*100000^4279 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11087 100000 2549728989347223 25000000000000000000 4279 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11087/100000 : ℝ)) (X := (2549728989347223/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14703/100000 : ℝ) ^ (4279/1024 : ℝ) ≤ (16588234697658087/50000000000000000000 : ℝ) := by
    have hpowers : (14703/100000 : ℝ)^4279 ≤ (16588234697658087/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14703 : ℕ)^4279*50000000000000000000^1024 ≤ 16588234697658087^1024*100000^4279 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14703 100000 16588234697658087 50000000000000000000 4279 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14703/100000 : ℝ)) (X := (16588234697658087/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502549728989347223/12500000000000000000 : ℝ) ≤ (5000244049539419/5000000000000000 : ℝ) ^ (4279/1024 : ℝ) := by
    have hpowers : (12502549728989347223/12500000000000000000 : ℝ)^1024 ≤ (5000244049539419/5000000000000000 : ℝ)^4279 := by
      have hnat : (12502549728989347223 : ℕ)^1024*5000000000000000^4279 ≤ 5000244049539419^4279*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502549728989347223 12500000000000000000 5000244049539419 5000000000000000 1024 4279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000244049539419/5000000000000000 : ℝ)) (X := (12502549728989347223/12500000000000000000 : ℝ)) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021687692676352533/50000000000000000000 : ℝ) ≤ (10001037837550951/10000000000000000 : ℝ) ^ (4279/1024 : ℝ) := by
    have hpowers : (50021687692676352533/50000000000000000000 : ℝ)^1024 ≤ (10001037837550951/10000000000000000 : ℝ)^4279 := by
      have hnat : (50021687692676352533 : ℕ)^1024*10000000000000000^4279 ≤ 10001037837550951^4279*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021687692676352533 50000000000000000000 10001037837550951 10000000000000000 1024 4279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001037837550951/10000000000000000 : ℝ)) (X := (50021687692676352533/50000000000000000000 : ℝ)) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016588234697658087/25000000000000000000 : ℝ) ≤ (1250198447002883/1250000000000000 : ℝ) ^ (4279/1024 : ℝ) := by
    have hpowers : (25016588234697658087/25000000000000000000 : ℝ)^1024 ≤ (1250198447002883/1250000000000000 : ℝ)^4279 := by
      have hnat : (25016588234697658087 : ℕ)^1024*1250000000000000^4279 ≤ 1250198447002883^4279*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016588234697658087 25000000000000000000 1250198447002883 1250000000000000 1024 4279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250198447002883/1250000000000000 : ℝ)) (X := (25016588234697658087/25000000000000000000 : ℝ)) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2549728989347223/25000000000000000000 : ℝ) ≤ ((18074787532694222273/18080000000000000000 : ℝ)+2*(549738472113/361600000000000 : ℝ)*(11087/100000 : ℝ))^(4279/1024 : ℝ) := by
    rw [show (18074787532694222273/18080000000000000000 : ℝ)+2*(549738472113/361600000000000 : ℝ)*(11087/100000 : ℝ)=(5000244049539419/5000000000000000 : ℝ) by norm_num, show 1+2*(2549728989347223/25000000000000000000 : ℝ)=(12502549728989347223/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16588234697658087/50000000000000000000 : ℝ)+(2549728989347223/25000000000000000000 : ℝ) ≤ ((18074787532694222273/18080000000000000000 : ℝ)+(549738472113/361600000000000 : ℝ)*((14703/100000 : ℝ)+(11087/100000 : ℝ)))^(4279/1024 : ℝ) := by
    rw [show (18074787532694222273/18080000000000000000 : ℝ)+(549738472113/361600000000000 : ℝ)*((14703/100000 : ℝ)+(11087/100000 : ℝ))=(10001037837550951/10000000000000000 : ℝ) by norm_num, show 1+(16588234697658087/50000000000000000000 : ℝ)+(2549728989347223/25000000000000000000 : ℝ)=(50021687692676352533/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16588234697658087/50000000000000000000 : ℝ) ≤ ((18074787532694222273/18080000000000000000 : ℝ)+2*(549738472113/361600000000000 : ℝ)*(14703/100000 : ℝ))^(4279/1024 : ℝ) := by
    rw [show (18074787532694222273/18080000000000000000 : ℝ)+2*(549738472113/361600000000000 : ℝ)*(14703/100000 : ℝ)=(1250198447002883/1250000000000000 : ℝ) by norm_num, show 1+2*(16588234697658087/50000000000000000000 : ℝ)=(25016588234697658087/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18074787532694222273/18080000000000000000 : ℝ)*(X 1 0+X 2 0)+(549738472113/361600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4279/1024 : ℝ)) (lo := (11087/100000 : ℝ)) (hi := (14703/100000 : ℝ)) (c := (18074787532694222273/18080000000000000000 : ℝ)) (alpha := (549738472113/361600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18074787532694222273/18080000000000000000 : ℝ)*(X 0 1+X 2 1)+(549738472113/361600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4279/1024 : ℝ)) (lo := (11087/100000 : ℝ)) (hi := (14703/100000 : ℝ)) (c := (18074787532694222273/18080000000000000000 : ℝ)) (alpha := (549738472113/361600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18074787532694222273/18080000000000000000 : ℝ)*(X 0 2+X 1 2)+(549738472113/361600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4279/1024 : ℝ)) (lo := (11087/100000 : ℝ)) (hi := (14703/100000 : ℝ)) (c := (18074787532694222273/18080000000000000000 : ℝ)) (alpha := (549738472113/361600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2063123373/10000000000 : ℝ)*X 0 0+(108277291/200000000 : ℝ)*X 0 1+(5243888931/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069874421/2000000000 : ℝ)*X 1 0+(-2149745539/10000000000 : ℝ)*X 1 1+(5243889023/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674686099/5000000000 : ℝ)*X 2 0+(5243888793/10000000000 : ℝ)*X 2 1+(-2149745719/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((270775139/625000000 : ℝ)*X 0 0+(415925669/1000000000 : ℝ)*X 0 1+(902467593/2000000000 : ℝ)*X 0 2+(270775139/625000000 : ℝ)*X 1 0+(415925669/1000000000 : ℝ)*X 1 1+(902467593/2000000000 : ℝ)*X 1 2+(270775139/625000000 : ℝ)*X 2 0+(415925669/1000000000 : ℝ)*X 2 1+(902467593/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-412627307/2000000000 : ℝ)*X 0 0+(5244496309/10000000000 : ℝ)*X 0 1+(1082650699/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652852031/5000000000 : ℝ)*X 1 0+(-990190137/5000000000 : ℝ)*X 1 1+(5413253529/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061140807/2000000000 : ℝ)*X 2 0+(135331331/250000000 : ℝ)*X 2 1+(-495095177/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4332428467/10000000000 : ℝ)*X 0 0+(4511075491/10000000000 : ℝ)*X 0 1+(4160525233/10000000000 : ℝ)*X 0 2+(4332428467/10000000000 : ℝ)*X 1 0+(4511075491/10000000000 : ℝ)*X 1 1+(4160525233/10000000000 : ℝ)*X 1 2+(4332428467/10000000000 : ℝ)*X 2 0+(4511075491/10000000000 : ℝ)*X 2 1+(4160525233/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3269427475845735421957659429/904000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (99135267/25000000000000 : ℝ)*(base19) + (151369437/25000000000000 : ℝ)*(base23) + (33676019/50000000000000 : ℝ)*(upper3) + (15761013/25000000000000 : ℝ)*(lower4) + (4357719705245603/100000000000000 : ℝ)*(major0) + (4357719705245603/100000000000000 : ℝ)*(major1) + (4357719705245603/100000000000000 : ℝ)*(major2) + (5883210190658497/100000000000000 : ℝ)*(sp0) + (1470805037219093/25000000000000 : ℝ)*(sp1) + (5883218568232333/100000000000000 : ℝ)*(sp2) + (1416106742037577/50000000000000 : ℝ)*(sp3) + (10354758943/100000000000000 : ℝ)*(sp4) + (1371707359/100000000000000 : ℝ)*(sp6) + (657555561/12500000000000 : ℝ)*(sp7) + (1416109372259821/50000000000000 : ℝ)*(f.failure) + (5883220545417441/100000000000000 : ℝ)*(f.sum) + (40104808300659/18080000000000000000000000000 : ℝ)*base65 + (171049595154865619/1808000000000000000000000000000000 : ℝ)*base67 + (14789284287746865619/1808000000000000000000000000000000 : ℝ)*base69 + (3667651359778865619/1808000000000000000000000000000000 : ℝ)*base71 + (23173433340339/18080000000000000000000000000 : ℝ)*base73 + (9693956876034865619/1808000000000000000000000000000000 : ℝ)*base75 + (28672348422066865619/1808000000000000000000000000000000 : ℝ)*base77 + (23558045793618865619/1808000000000000000000000000000000 : ℝ)*base79 + (138393560521939/18080000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (39629421/5000000000000000000000 : ℝ)*base90 + (39629421/5000000000000000000000 : ℝ)*base92 + (39629421/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (514132286301577952956793349/90400000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (890912649/25000000000000 : ℝ)*(base19) + (487396183/12500000000000 : ℝ)*(base23) + (235586913/100000000000000 : ℝ)*(upper2) + (316553497/100000000000000 : ℝ)*(upper3) + (20502461/5000000000000 : ℝ)*(upper5) + (438916264526871/10000000000000 : ℝ)*(major0) + (438916264526871/10000000000000 : ℝ)*(major1) + (438916264526871/10000000000000 : ℝ)*(major2) + (79010059013/100000000000000 : ℝ)*(sp1) + (34745019457/50000000000000 : ℝ)*(sp2) + (5925670603308647/100000000000000 : ℝ)*(sp4) + (2962794014799519/50000000000000 : ℝ)*(sp5) + (5925597214100269/100000000000000 : ℝ)*(sp6) + (713163624412991/25000000000000 : ℝ)*(sp7) + (713163624412991/25000000000000 : ℝ)*(f.failure) + (5925670603308647/100000000000000 : ℝ)*(f.sum) + (3655599242679/1808000000000000000000000000 : ℝ)*base65 + (2925561924981252217/180800000000000000000000000000000 : ℝ)*base68 + (719405737114747783/180800000000000000000000000000000 : ℝ)*base69 + (1982018372670852217/180800000000000000000000000000000 : ℝ)*base72 + (10004570939817/1808000000000000000000000000 : ℝ)*base74 + (1418544885874052217/180800000000000000000000000000000 : ℝ)*base76 + (1968218571483652217/180800000000000000000000000000000 : ℝ)*base78 + (920356293247547783/180800000000000000000000000000000 : ℝ)*base79 + (9678143155271/1808000000000000000000000000 : ℝ)*base81 + (12025409/2500000000000000000000 : ℝ)*base89 + (12025409/2500000000000000000000 : ℝ)*base91 + (12025409/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1320_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153862399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14703/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11087/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1387/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7347/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1320_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1320_s7_0 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-257891431/1250000000 : ℝ)*x 0 + (270689339/500000000 : ℝ)*x 1 + (5243961463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (257891431/1250000000 : ℝ)^535 ≤ (1569849966491/12500000000000 : ℝ)^407 := by
    have hnat : (257891431 : ℕ)^535*12500000000000^407 ≤ 1569849966491^407*1250000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257891431 1250000000 1569849966491 12500000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270689339/500000000 : ℝ)^535 ≤ (8927261077661/20000000000000 : ℝ)^407 := by
    have hnat : (270689339 : ℕ)^535*20000000000000^407 ≤ 8927261077661^407*500000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270689339 500000000 8927261077661 20000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243961463/10000000000 : ℝ)^535 ≤ (10701223717183/25000000000000 : ℝ)^407 := by
    have hnat : (5243961463 : ℕ)^535*25000000000000^407 ≤ 10701223717183^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243961463 10000000000 10701223717183 25000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-257891431/1250000000 : ℝ), (270689339/500000000 : ℝ), (5243961463/10000000000 : ℝ)] ![(1569849966491/12500000000000 : ℝ), (8927261077661/20000000000000 : ℝ), (10701223717183/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-257891431/1250000000 : ℝ)|^535 ≤ (1569849966491/12500000000000 : ℝ)^407
        have hw : |(-257891431/1250000000 : ℝ)|=(257891431/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270689339/500000000 : ℝ)|^535 ≤ (8927261077661/20000000000000 : ℝ)^407
        have hw : |(270689339/500000000 : ℝ)|=(270689339/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243961463/10000000000 : ℝ)|^535 ≤ (10701223717183/25000000000000 : ℝ)^407
        have hw : |(5243961463/10000000000 : ℝ)|=(5243961463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s7_1 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (668669023/1250000000 : ℝ)*x 0 + (-1074838081/5000000000 : ℝ)*x 1 + (5243961479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668669023/1250000000 : ℝ)^535 ≤ (10984819525149/25000000000000 : ℝ)^407 := by
    have hnat : (668669023 : ℕ)^535*25000000000000^407 ≤ 10984819525149^407*1250000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668669023 1250000000 10984819525149 25000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1074838081/5000000000 : ℝ)^535 ≤ (13255826841483/100000000000000 : ℝ)^407 := by
    have hnat : (1074838081 : ℕ)^535*100000000000000^407 ≤ 13255826841483^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074838081 5000000000 13255826841483 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243961479/10000000000 : ℝ)^535 ≤ (4280489504041/10000000000000 : ℝ)^407 := by
    have hnat : (5243961479 : ℕ)^535*10000000000000^407 ≤ 4280489504041^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243961479 10000000000 4280489504041 10000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668669023/1250000000 : ℝ), (-1074838081/5000000000 : ℝ), (5243961479/10000000000 : ℝ)] ![(10984819525149/25000000000000 : ℝ), (13255826841483/100000000000000 : ℝ), (4280489504041/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668669023/1250000000 : ℝ)|^535 ≤ (10984819525149/25000000000000 : ℝ)^407
        have hw : |(668669023/1250000000 : ℝ)|=(668669023/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1074838081/5000000000 : ℝ)|^535 ≤ (13255826841483/100000000000000 : ℝ)^407
        have hw : |(-1074838081/5000000000 : ℝ)|=(1074838081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243961479/10000000000 : ℝ)|^535 ≤ (4280489504041/10000000000000 : ℝ)^407
        have hw : |(5243961479/10000000000 : ℝ)|=(5243961479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s7_2 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (334334587/625000000 : ℝ)*x 0 + (1048792133/2000000000 : ℝ)*x 1 + (-2149675631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334334587/625000000 : ℝ)^535 ≤ (43939291143613/100000000000000 : ℝ)^407 := by
    have hnat : (334334587 : ℕ)^535*100000000000000^407 ≤ 43939291143613^407*625000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334334587 625000000 43939291143613 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048792133/2000000000 : ℝ)^535 ≤ (42804886306319/100000000000000 : ℝ)^407 := by
    have hnat : (1048792133 : ℕ)^535*100000000000000^407 ≤ 42804886306319^407*2000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048792133 2000000000 42804886306319 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2149675631/10000000000 : ℝ)^535 ≤ (13255822537331/100000000000000 : ℝ)^407 := by
    have hnat : (2149675631 : ℕ)^535*100000000000000^407 ≤ 13255822537331^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149675631 10000000000 13255822537331 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334334587/625000000 : ℝ), (1048792133/2000000000 : ℝ), (-2149675631/10000000000 : ℝ)] ![(43939291143613/100000000000000 : ℝ), (42804886306319/100000000000000 : ℝ), (13255822537331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334334587/625000000 : ℝ)|^535 ≤ (43939291143613/100000000000000 : ℝ)^407
        have hw : |(334334587/625000000 : ℝ)|=(334334587/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048792133/2000000000 : ℝ)|^535 ≤ (42804886306319/100000000000000 : ℝ)^407
        have hw : |(1048792133/2000000000 : ℝ)|=(1048792133/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2149675631/10000000000 : ℝ)|^535 ≤ (13255822537331/100000000000000 : ℝ)^407
        have hw : |(-2149675631/10000000000 : ℝ)|=(2149675631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s7_3 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2166204523/5000000000 : ℝ)*x 0 + (4159410091/10000000000 : ℝ)*x 1 + (4512181707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2166204523/5000000000 : ℝ)^535 ≤ (6660582342941/20000000000000 : ℝ)^407 := by
    have hnat : (2166204523 : ℕ)^535*20000000000000^407 ≤ 6660582342941^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166204523 5000000000 6660582342941 20000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4159410091/10000000000 : ℝ)^535 ≤ (30826106259/97656250000 : ℝ)^407 := by
    have hnat : (4159410091 : ℕ)^535*97656250000^407 ≤ 30826106259^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4159410091 10000000000 30826106259 97656250000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4512181707/10000000000 : ℝ)^535 ≤ (17565577726231/50000000000000 : ℝ)^407 := by
    have hnat : (4512181707 : ℕ)^535*50000000000000^407 ≤ 17565577726231^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4512181707 10000000000 17565577726231 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2166204523/5000000000 : ℝ), (4159410091/10000000000 : ℝ), (4512181707/10000000000 : ℝ)] ![(6660582342941/20000000000000 : ℝ), (30826106259/97656250000 : ℝ), (17565577726231/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2166204523/5000000000 : ℝ)|^535 ≤ (6660582342941/20000000000000 : ℝ)^407
        have hw : |(2166204523/5000000000 : ℝ)|=(2166204523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4159410091/10000000000 : ℝ)|^535 ≤ (30826106259/97656250000 : ℝ)^407
        have hw : |(4159410091/10000000000 : ℝ)|=(4159410091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4512181707/10000000000 : ℝ)|^535 ≤ (17565577726231/50000000000000 : ℝ)^407
        have hw : |(4512181707/10000000000 : ℝ)|=(4512181707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s7_4 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-515785947/2500000000 : ℝ)*x 0 + (209782697/400000000 : ℝ)*x 1 + (5413177729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (515785947/2500000000 : ℝ)^535 ≤ (6279449236311/50000000000000 : ℝ)^407 := by
    have hnat : (515785947 : ℕ)^535*50000000000000^407 ≤ 6279449236311^407*2500000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515785947 2500000000 6279449236311 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209782697/400000000 : ℝ)^535 ≤ (10702849215807/25000000000000 : ℝ)^407 := by
    have hnat : (209782697 : ℕ)^535*25000000000000^407 ≤ 10702849215807^407*400000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209782697 400000000 10702849215807 25000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413177729/10000000000 : ℝ)^535 ≤ (44629704651089/100000000000000 : ℝ)^407 := by
    have hnat : (5413177729 : ℕ)^535*100000000000000^407 ≤ 44629704651089^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413177729 10000000000 44629704651089 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-515785947/2500000000 : ℝ), (209782697/400000000 : ℝ), (5413177729/10000000000 : ℝ)] ![(6279449236311/50000000000000 : ℝ), (10702849215807/25000000000000 : ℝ), (44629704651089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-515785947/2500000000 : ℝ)|^535 ≤ (6279449236311/50000000000000 : ℝ)^407
        have hw : |(-515785947/2500000000 : ℝ)|=(515785947/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209782697/400000000 : ℝ)|^535 ≤ (10702849215807/25000000000000 : ℝ)^407
        have hw : |(209782697/400000000 : ℝ)|=(209782697/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413177729/10000000000 : ℝ)|^535 ≤ (44629704651089/100000000000000 : ℝ)^407
        have hw : |(5413177729/10000000000 : ℝ)|=(5413177729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s7_5 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (165803833/312500000 : ℝ)*x 0 + (-1980458951/10000000000 : ℝ)*x 1 + (1082635541/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165803833/312500000 : ℝ)^535 ≤ (2173440335411/5000000000000 : ℝ)^407 := by
    have hnat : (165803833 : ℕ)^535*5000000000000^407 ≤ 2173440335411^407*312500000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165803833 312500000 2173440335411 5000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1980458951/10000000000 : ℝ)^535 ≤ (11901488883503/100000000000000 : ℝ)^407 := by
    have hnat : (1980458951 : ℕ)^535*100000000000000^407 ≤ 11901488883503^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1980458951 10000000000 11901488883503 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082635541/2000000000 : ℝ)^535 ≤ (44629704390987/100000000000000 : ℝ)^407 := by
    have hnat : (1082635541 : ℕ)^535*100000000000000^407 ≤ 44629704390987^407*2000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082635541 2000000000 44629704390987 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165803833/312500000 : ℝ), (-1980458951/10000000000 : ℝ), (1082635541/2000000000 : ℝ)] ![(2173440335411/5000000000000 : ℝ), (11901488883503/100000000000000 : ℝ), (44629704390987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165803833/312500000 : ℝ)|^535 ≤ (2173440335411/5000000000000 : ℝ)^407
        have hw : |(165803833/312500000 : ℝ)|=(165803833/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1980458951/10000000000 : ℝ)|^535 ≤ (11901488883503/100000000000000 : ℝ)^407
        have hw : |(-1980458951/10000000000 : ℝ)|=(1980458951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082635541/2000000000 : ℝ)|^535 ≤ (44629704390987/100000000000000 : ℝ)^407
        have hw : |(1082635541/2000000000 : ℝ)|=(1082635541/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s7_6 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (663215339/1250000000 : ℝ)*x 0 + (2706588817/5000000000 : ℝ)*x 1 + (-495114743/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663215339/1250000000 : ℝ)^535 ≤ (10867201827827/25000000000000 : ℝ)^407 := by
    have hnat : (663215339 : ℕ)^535*25000000000000^407 ≤ 10867201827827^407*1250000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663215339 1250000000 10867201827827 25000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706588817/5000000000 : ℝ)^535 ≤ (44629703621521/100000000000000 : ℝ)^407 := by
    have hnat : (2706588817 : ℕ)^535*100000000000000^407 ≤ 44629703621521^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706588817 5000000000 44629703621521 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (495114743/2500000000 : ℝ)^535 ≤ (11901489049391/100000000000000 : ℝ)^407 := by
    have hnat : (495114743 : ℕ)^535*100000000000000^407 ≤ 11901489049391^407*2500000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      495114743 2500000000 11901489049391 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663215339/1250000000 : ℝ), (2706588817/5000000000 : ℝ), (-495114743/2500000000 : ℝ)] ![(10867201827827/25000000000000 : ℝ), (44629703621521/100000000000000 : ℝ), (11901489049391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663215339/1250000000 : ℝ)|^535 ≤ (10867201827827/25000000000000 : ℝ)^407
        have hw : |(663215339/1250000000 : ℝ)|=(663215339/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706588817/5000000000 : ℝ)|^535 ≤ (44629703621521/100000000000000 : ℝ)^407
        have hw : |(2706588817/5000000000 : ℝ)|=(2706588817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-495114743/2500000000 : ℝ)|^535 ≤ (11901489049391/100000000000000 : ℝ)^407
        have hw : |(-495114743/2500000000 : ℝ)|=(495114743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s7_7 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2166216727/5000000000 : ℝ)*x 0 + (4510922309/10000000000 : ℝ)*x 1 + (416067731/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2166216727/5000000000 : ℝ)^535 ≤ (1332126333761/4000000000000 : ℝ)^407 := by
    have hnat : (2166216727 : ℕ)^535*4000000000000^407 ≤ 1332126333761^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166216727 5000000000 1332126333761 4000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4510922309/10000000000 : ℝ)^535 ≤ (35118266751047/100000000000000 : ℝ)^407 := by
    have hnat : (4510922309 : ℕ)^535*100000000000000^407 ≤ 35118266751047^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4510922309 10000000000 35118266751047 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (416067731/1000000000 : ℝ)^535 ≤ (31578574895189/100000000000000 : ℝ)^407 := by
    have hnat : (416067731 : ℕ)^535*100000000000000^407 ≤ 31578574895189^407*1000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416067731 1000000000 31578574895189 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2166216727/5000000000 : ℝ), (4510922309/10000000000 : ℝ), (416067731/1000000000 : ℝ)] ![(1332126333761/4000000000000 : ℝ), (35118266751047/100000000000000 : ℝ), (31578574895189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2166216727/5000000000 : ℝ)|^535 ≤ (1332126333761/4000000000000 : ℝ)^407
        have hw : |(2166216727/5000000000 : ℝ)|=(2166216727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4510922309/10000000000 : ℝ)|^535 ≤ (35118266751047/100000000000000 : ℝ)^407
        have hw : |(4510922309/10000000000 : ℝ)|=(4510922309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(416067731/1000000000 : ℝ)|^535 ≤ (31578574895189/100000000000000 : ℝ)^407
        have hw : |(416067731/1000000000 : ℝ)|=(416067731/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1320_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153862399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7347/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1387/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11097/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3673/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7347/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1387/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7347/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1387/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7347/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1387/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7347/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1387/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7347/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1387/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7347/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1387/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1387/12500 : ℝ) ^ (4279/1024 : ℝ) ≤ (10233556532260969/100000000000000000000 : ℝ) := by
    have hpowers : (1387/12500 : ℝ)^4279 ≤ (10233556532260969/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1387 : ℕ)^4279*100000000000000000000^1024 ≤ 10233556532260969^1024*12500^4279 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1387 12500 10233556532260969 100000000000000000000 4279 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1387/12500 : ℝ)) (X := (10233556532260969/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7347/50000 : ℝ) ^ (4279/1024 : ℝ) ≤ (8272922685357059/25000000000000000000 : ℝ) := by
    have hpowers : (7347/50000 : ℝ)^4279 ≤ (8272922685357059/25000000000000000000 : ℝ)^1024 := by
      have hnat : (7347 : ℕ)^4279*25000000000000000000^1024 ≤ 8272922685357059^1024*50000^4279 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7347 50000 8272922685357059 25000000000000000000 4279 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7347/50000 : ℝ)) (X := (8272922685357059/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010233556532260969/50000000000000000000 : ℝ) ≤ (10000489756776259/10000000000000000 : ℝ) ^ (4279/1024 : ℝ) := by
    have hpowers : (50010233556532260969/50000000000000000000 : ℝ)^1024 ≤ (10000489756776259/10000000000000000 : ℝ)^4279 := by
      have hnat : (50010233556532260969 : ℕ)^1024*10000000000000000^4279 ≤ 10000489756776259^4279*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010233556532260969 50000000000000000000 10000489756776259 10000000000000000 1024 4279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000489756776259/10000000000000000 : ℝ)) (X := (50010233556532260969/50000000000000000000 : ℝ)) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008665049454737841/20000000000000000000 : ℝ) ≤ (10001036638100871/10000000000000000 : ℝ) ^ (4279/1024 : ℝ) := by
    have hpowers : (20008665049454737841/20000000000000000000 : ℝ)^1024 ≤ (10001036638100871/10000000000000000 : ℝ)^4279 := by
      have hnat : (20008665049454737841 : ℕ)^1024*10000000000000000^4279 ≤ 10001036638100871^4279*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008665049454737841 20000000000000000000 10001036638100871 10000000000000000 1024 4279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001036638100871/10000000000000000 : ℝ)) (X := (20008665049454737841/20000000000000000000 : ℝ)) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508272922685357059/12500000000000000000 : ℝ) ≤ (10001583519425483/10000000000000000 : ℝ) ^ (4279/1024 : ℝ) := by
    have hpowers : (12508272922685357059/12500000000000000000 : ℝ)^1024 ≤ (10001583519425483/10000000000000000 : ℝ)^4279 := by
      have hnat : (12508272922685357059 : ℕ)^1024*10000000000000000^4279 ≤ 10001583519425483^4279*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508272922685357059 12500000000000000000 10001583519425483 10000000000000000 1024 4279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001583519425483/10000000000000000 : ℝ)) (X := (12508272922685357059/12500000000000000000 : ℝ)) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10233556532260969/100000000000000000000 : ℝ) ≤ ((2569258982466085027/2570000000000000000 : ℝ)+2*(19531475879/12850000000000 : ℝ)*(1387/12500 : ℝ))^(4279/1024 : ℝ) := by
    rw [show (2569258982466085027/2570000000000000000 : ℝ)+2*(19531475879/12850000000000 : ℝ)*(1387/12500 : ℝ)=(10000489756776259/10000000000000000 : ℝ) by norm_num, show 1+2*(10233556532260969/100000000000000000000 : ℝ)=(50010233556532260969/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8272922685357059/25000000000000000000 : ℝ)+(10233556532260969/100000000000000000000 : ℝ) ≤ ((2569258982466085027/2570000000000000000 : ℝ)+(19531475879/12850000000000 : ℝ)*((7347/50000 : ℝ)+(1387/12500 : ℝ)))^(4279/1024 : ℝ) := by
    rw [show (2569258982466085027/2570000000000000000 : ℝ)+(19531475879/12850000000000 : ℝ)*((7347/50000 : ℝ)+(1387/12500 : ℝ))=(10001036638100871/10000000000000000 : ℝ) by norm_num, show 1+(8272922685357059/25000000000000000000 : ℝ)+(10233556532260969/100000000000000000000 : ℝ)=(20008665049454737841/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8272922685357059/25000000000000000000 : ℝ) ≤ ((2569258982466085027/2570000000000000000 : ℝ)+2*(19531475879/12850000000000 : ℝ)*(7347/50000 : ℝ))^(4279/1024 : ℝ) := by
    rw [show (2569258982466085027/2570000000000000000 : ℝ)+2*(19531475879/12850000000000 : ℝ)*(7347/50000 : ℝ)=(10001583519425483/10000000000000000 : ℝ) by norm_num, show 1+2*(8272922685357059/25000000000000000000 : ℝ)=(12508272922685357059/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2569258982466085027/2570000000000000000 : ℝ)*(X 1 0+X 2 0)+(19531475879/12850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4279/1024 : ℝ)) (lo := (1387/12500 : ℝ)) (hi := (7347/50000 : ℝ)) (c := (2569258982466085027/2570000000000000000 : ℝ)) (alpha := (19531475879/12850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2569258982466085027/2570000000000000000 : ℝ)*(X 0 1+X 2 1)+(19531475879/12850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4279/1024 : ℝ)) (lo := (1387/12500 : ℝ)) (hi := (7347/50000 : ℝ)) (c := (2569258982466085027/2570000000000000000 : ℝ)) (alpha := (19531475879/12850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2569258982466085027/2570000000000000000 : ℝ)*(X 0 2+X 1 2)+(19531475879/12850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4279/1024 : ℝ)) (lo := (1387/12500 : ℝ)) (hi := (7347/50000 : ℝ)) (c := (2569258982466085027/2570000000000000000 : ℝ)) (alpha := (19531475879/12850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-257891431/1250000000 : ℝ)*X 0 0+(270689339/500000000 : ℝ)*X 0 1+(5243961463/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668669023/1250000000 : ℝ)*X 1 0+(-1074838081/5000000000 : ℝ)*X 1 1+(5243961479/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334334587/625000000 : ℝ)*X 2 0+(1048792133/2000000000 : ℝ)*X 2 1+(-2149675631/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2166204523/5000000000 : ℝ)*X 0 0+(4159410091/10000000000 : ℝ)*X 0 1+(4512181707/10000000000 : ℝ)*X 0 2+(2166204523/5000000000 : ℝ)*X 1 0+(4159410091/10000000000 : ℝ)*X 1 1+(4512181707/10000000000 : ℝ)*X 1 2+(2166204523/5000000000 : ℝ)*X 2 0+(4159410091/10000000000 : ℝ)*X 2 1+(4512181707/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-515785947/2500000000 : ℝ)*X 0 0+(209782697/400000000 : ℝ)*X 0 1+(5413177729/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((165803833/312500000 : ℝ)*X 1 0+(-1980458951/10000000000 : ℝ)*X 1 1+(1082635541/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663215339/1250000000 : ℝ)*X 2 0+(2706588817/5000000000 : ℝ)*X 2 1+(-495114743/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2166216727/5000000000 : ℝ)*X 0 0+(4510922309/10000000000 : ℝ)*X 0 1+(416067731/1000000000 : ℝ)*X 0 2+(2166216727/5000000000 : ℝ)*X 1 0+(4510922309/10000000000 : ℝ)*X 1 1+(416067731/1000000000 : ℝ)*X 1 2+(2166216727/5000000000 : ℝ)*X 2 0+(4510922309/10000000000 : ℝ)*X 2 1+(416067731/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (378424110075198672930431709/64250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (837186739/50000000000000 : ℝ)*(base19) + (665991533/25000000000000 : ℝ)*(base23) + (181955573/100000000000000 : ℝ)*(lower2) + (15581167/10000000000000 : ℝ)*(upper3) + (785229757/100000000000000 : ℝ)*(upper5) + (2180793848469589/50000000000000 : ℝ)*(major0) + (2180793848469589/50000000000000 : ℝ)*(major1) + (2180793848469589/50000000000000 : ℝ)*(major2) + (5888404114555013/100000000000000 : ℝ)*(sp0) + (5888440849510003/100000000000000 : ℝ)*(sp1) + (5888439859917349/100000000000000 : ℝ)*(sp2) + (1417357669824737/50000000000000 : ℝ)*(sp3) + (9602332117/25000000000000 : ℝ)*(sp4) + (541688013/3125000000000 : ℝ)*(sp7) + (283473267366589/10000000000000 : ℝ)*(f.failure) + (5888442523883481/100000000000000 : ℝ)*(f.sum) + (215545656603/160625000000000000000000000 : ℝ)*base65 + (253574049719056097/128500000000000000000000000000000 : ℝ)*base68 + (345926556522556097/128500000000000000000000000000000 : ℝ)*base70 + (255251319273943903/128500000000000000000000000000000 : ℝ)*base71 + (403259550449/321250000000000000000000000 : ℝ)*base74 + (7768686633556097/128500000000000000000000000000000 : ℝ)*base76 + (790466507877943903/128500000000000000000000000000000 : ℝ)*base77 + (760762784501556097/128500000000000000000000000000000 : ℝ)*base80 + (8730463878891/1285000000000000000000000000 : ℝ)*base82 + (15987011/1000000000000000000000 : ℝ)*base89 + (15987011/1000000000000000000000 : ℝ)*base91 + (15987011/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (176111618836308134426762157/32125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (367482319/20000000000000 : ℝ)*(base19) + (2239226551/100000000000000 : ℝ)*(base23) + (633611201/100000000000000 : ℝ)*(lower1) + (84823609/50000000000000 : ℝ)*(upper2) + (19494293/10000000000000 : ℝ)*(upper3) + (317146921/100000000000000 : ℝ)*(upper5) + (1098240361354603/25000000000000 : ℝ)*(major0) + (1098240361354603/25000000000000 : ℝ)*(major1) + (1098240361354603/25000000000000 : ℝ)*(major2) + (148006403/6250000000000 : ℝ)*(sp2) + (1186159850211563/20000000000000 : ℝ)*(sp4) + (296539870682311/5000000000000 : ℝ)*(sp5) + (370674665233051/6250000000000 : ℝ)*(sp6) + (1427561728521603/50000000000000 : ℝ)*(sp7) + (1427561728521603/50000000000000 : ℝ)*(f.failure) + (1186159850211563/20000000000000 : ℝ)*(f.sum) + (663358346543/160625000000000000000000000 : ℝ)*base66 + (749000102489979281/64250000000000000000000000000000 : ℝ)*base67 + (795190756075520719/64250000000000000000000000000000 : ℝ)*base70 + (860896950626229281/64250000000000000000000000000000 : ℝ)*base71 + (3113481407803/642500000000000000000000000 : ℝ)*base73 + (681780343423229281/64250000000000000000000000000000 : ℝ)*base75 + (244820638877770719/64250000000000000000000000000000 : ℝ)*base78 + (762233489371729281/64250000000000000000000000000000 : ℝ)*base79 + (1770993786851/321250000000000000000000000 : ℝ)*base82 + (39094403/5000000000000000000000 : ℝ)*base90 + (39094403/5000000000000000000000 : ℝ)*base92 + (39094403/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1320_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153862399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7347/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1387/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11097/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3673/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1320_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1320_box_0 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-473525517/2500000000 : ℝ)*x 0 + (269542929/500000000 : ℝ)*x 1 + (1347714677/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (473525517/2500000000 : ℝ)^535 ≤ (11224045119291/100000000000000 : ℝ)^407 := by
    have hnat : (473525517 : ℕ)^535*100000000000000^407 ≤ 11224045119291^407*2500000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      473525517 2500000000 11224045119291 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269542929/500000000 : ℝ)^535 ≤ (22193988370367/50000000000000 : ℝ)^407 := by
    have hnat : (269542929 : ℕ)^535*50000000000000^407 ≤ 22193988370367^407*500000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269542929 500000000 22193988370367 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347714677/2500000000 : ℝ)^535 ≤ (44387978126139/100000000000000 : ℝ)^407 := by
    have hnat : (1347714677 : ℕ)^535*100000000000000^407 ≤ 44387978126139^407*2500000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347714677 2500000000 44387978126139 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-473525517/2500000000 : ℝ), (269542929/500000000 : ℝ), (1347714677/2500000000 : ℝ)] ![(11224045119291/100000000000000 : ℝ), (22193988370367/50000000000000 : ℝ), (44387978126139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-473525517/2500000000 : ℝ)|^535 ≤ (11224045119291/100000000000000 : ℝ)^407
        have hw : |(-473525517/2500000000 : ℝ)|=(473525517/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269542929/500000000 : ℝ)|^535 ≤ (22193988370367/50000000000000 : ℝ)^407
        have hw : |(269542929/500000000 : ℝ)|=(269542929/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347714677/2500000000 : ℝ)|^535 ≤ (44387978126139/100000000000000 : ℝ)^407
        have hw : |(1347714677/2500000000 : ℝ)|=(1347714677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_box_1 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1321210071/2500000000 : ℝ)*x 0 + (-31863113/156250000 : ℝ)*x 1 + (5390858321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321210071/2500000000 : ℝ)^535 ≤ (43244054864041/100000000000000 : ℝ)^407 := by
    have hnat : (1321210071 : ℕ)^535*100000000000000^407 ≤ 43244054864041^407*2500000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321210071 2500000000 43244054864041 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (31863113/156250000 : ℝ)^535 ≤ (1236797118043/10000000000000 : ℝ)^407 := by
    have hnat : (31863113 : ℕ)^535*10000000000000^407 ≤ 1236797118043^407*156250000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31863113 156250000 1236797118043 10000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390858321/10000000000 : ℝ)^535 ≤ (44387973937453/100000000000000 : ℝ)^407 := by
    have hnat : (5390858321 : ℕ)^535*100000000000000^407 ≤ 44387973937453^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390858321 10000000000 44387973937453 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321210071/2500000000 : ℝ), (-31863113/156250000 : ℝ), (5390858321/10000000000 : ℝ)] ![(43244054864041/100000000000000 : ℝ), (1236797118043/10000000000000 : ℝ), (44387973937453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321210071/2500000000 : ℝ)|^535 ≤ (43244054864041/100000000000000 : ℝ)^407
        have hw : |(1321210071/2500000000 : ℝ)|=(1321210071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-31863113/156250000 : ℝ)|^535 ≤ (1236797118043/10000000000000 : ℝ)^407
        have hw : |(-31863113/156250000 : ℝ)|=(31863113/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390858321/10000000000 : ℝ)|^535 ≤ (44387973937453/100000000000000 : ℝ)^407
        have hw : |(5390858321/10000000000 : ℝ)|=(5390858321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_box_2 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1056968013/2000000000 : ℝ)*x 0 + (539085869/1000000000 : ℝ)*x 1 + (-2039239027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056968013/2000000000 : ℝ)^535 ≤ (2162202625423/5000000000000 : ℝ)^407 := by
    have hnat : (1056968013 : ℕ)^535*5000000000000^407 ≤ 2162202625423^407*2000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056968013 2000000000 2162202625423 5000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539085869/1000000000 : ℝ)^535 ≤ (11096994482829/25000000000000 : ℝ)^407 := by
    have hnat : (539085869 : ℕ)^535*25000000000000^407 ≤ 11096994482829^407*1000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539085869 1000000000 11096994482829 25000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2039239027/10000000000 : ℝ)^535 ≤ (6183984773043/50000000000000 : ℝ)^407 := by
    have hnat : (2039239027 : ℕ)^535*50000000000000^407 ≤ 6183984773043^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2039239027 10000000000 6183984773043 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1056968013/2000000000 : ℝ), (539085869/1000000000 : ℝ), (-2039239027/10000000000 : ℝ)] ![(2162202625423/5000000000000 : ℝ), (11096994482829/25000000000000 : ℝ), (6183984773043/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1056968013/2000000000 : ℝ)|^535 ≤ (2162202625423/5000000000000 : ℝ)^407
        have hw : |(1056968013/2000000000 : ℝ)|=(1056968013/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539085869/1000000000 : ℝ)|^535 ≤ (11096994482829/25000000000000 : ℝ)^407
        have hw : |(539085869/1000000000 : ℝ)|=(539085869/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2039239027/10000000000 : ℝ)|^535 ≤ (6183984773043/50000000000000 : ℝ)^407
        have hw : |(-2039239027/10000000000 : ℝ)|=(2039239027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_box_3 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (28007071/62500000 : ℝ)*x 0 + (2130992403/5000000000 : ℝ)*x 1 + (852397033/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (28007071/62500000 : ℝ)^535 ≤ (34813716118119/100000000000000 : ℝ)^407 := by
    have hnat : (28007071 : ℕ)^535*100000000000000^407 ≤ 34813716118119^407*62500000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28007071 62500000 34813716118119 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2130992403/5000000000 : ℝ)^535 ≤ (127316953631/390625000000 : ℝ)^407 := by
    have hnat : (2130992403 : ℕ)^535*390625000000^407 ≤ 127316953631^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130992403 5000000000 127316953631 390625000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (852397033/2000000000 : ℝ)^535 ≤ (32593143738381/100000000000000 : ℝ)^407 := by
    have hnat : (852397033 : ℕ)^535*100000000000000^407 ≤ 32593143738381^407*2000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      852397033 2000000000 32593143738381 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(28007071/62500000 : ℝ), (2130992403/5000000000 : ℝ), (852397033/2000000000 : ℝ)] ![(34813716118119/100000000000000 : ℝ), (127316953631/390625000000 : ℝ), (32593143738381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(28007071/62500000 : ℝ)|^535 ≤ (34813716118119/100000000000000 : ℝ)^407
        have hw : |(28007071/62500000 : ℝ)|=(28007071/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2130992403/5000000000 : ℝ)|^535 ≤ (127316953631/390625000000 : ℝ)^407
        have hw : |(2130992403/5000000000 : ℝ)|=(2130992403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(852397033/2000000000 : ℝ)|^535 ≤ (32593143738381/100000000000000 : ℝ)^407
        have hw : |(852397033/2000000000 : ℝ)|=(852397033/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_box_4 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2234920951/10000000000 : ℝ)*x 0 + (5264412999/10000000000 : ℝ)*x 1 + (5264411871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2234920951/10000000000 : ℝ)^535 ≤ (1743883744829/12500000000000 : ℝ)^407 := by
    have hnat : (2234920951 : ℕ)^535*12500000000000^407 ≤ 1743883744829^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2234920951 10000000000 1743883744829 12500000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264412999/10000000000 : ℝ)^535 ≤ (8604894214117/20000000000000 : ℝ)^407 := by
    have hnat : (5264412999 : ℕ)^535*20000000000000^407 ≤ 8604894214117^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264412999 10000000000 8604894214117 20000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264411871/10000000000 : ℝ)^535 ≤ (21512229476249/50000000000000 : ℝ)^407 := by
    have hnat : (5264411871 : ℕ)^535*50000000000000^407 ≤ 21512229476249^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264411871 10000000000 21512229476249 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2234920951/10000000000 : ℝ), (5264412999/10000000000 : ℝ), (5264411871/10000000000 : ℝ)] ![(1743883744829/12500000000000 : ℝ), (8604894214117/20000000000000 : ℝ), (21512229476249/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2234920951/10000000000 : ℝ)|^535 ≤ (1743883744829/12500000000000 : ℝ)^407
        have hw : |(-2234920951/10000000000 : ℝ)|=(2234920951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264412999/10000000000 : ℝ)|^535 ≤ (8604894214117/20000000000000 : ℝ)^407
        have hw : |(5264412999/10000000000 : ℝ)|=(5264412999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264411871/10000000000 : ℝ)|^535 ≤ (21512229476249/50000000000000 : ℝ)^407
        have hw : |(5264411871/10000000000 : ℝ)|=(5264411871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_box_5 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5373736829/10000000000 : ℝ)*x 0 + (-2089820457/10000000000 : ℝ)*x 1 + (2632205891/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5373736829/10000000000 : ℝ)^535 ≤ (11050688122327/25000000000000 : ℝ)^407 := by
    have hnat : (5373736829 : ℕ)^535*25000000000000^407 ≤ 11050688122327^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5373736829 10000000000 11050688122327 25000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2089820457/10000000000 : ℝ)^535 ≤ (12772789498183/100000000000000 : ℝ)^407 := by
    have hnat : (2089820457 : ℕ)^535*100000000000000^407 ≤ 12772789498183^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089820457 10000000000 12772789498183 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632205891/5000000000 : ℝ)^535 ≤ (43024457996373/100000000000000 : ℝ)^407 := by
    have hnat : (2632205891 : ℕ)^535*100000000000000^407 ≤ 43024457996373^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632205891 5000000000 43024457996373 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5373736829/10000000000 : ℝ), (-2089820457/10000000000 : ℝ), (2632205891/5000000000 : ℝ)] ![(11050688122327/25000000000000 : ℝ), (12772789498183/100000000000000 : ℝ), (43024457996373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5373736829/10000000000 : ℝ)|^535 ≤ (11050688122327/25000000000000 : ℝ)^407
        have hw : |(5373736829/10000000000 : ℝ)|=(5373736829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2089820457/10000000000 : ℝ)|^535 ≤ (12772789498183/100000000000000 : ℝ)^407
        have hw : |(-2089820457/10000000000 : ℝ)|=(2089820457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632205891/5000000000 : ℝ)|^535 ≤ (43024457996373/100000000000000 : ℝ)^407
        have hw : |(2632205891/5000000000 : ℝ)|=(2632205891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_box_6 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (335858603/625000000 : ℝ)*x 0 + (2632205711/5000000000 : ℝ)*x 1 + (-522454959/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335858603/625000000 : ℝ)^535 ≤ (44202761344871/100000000000000 : ℝ)^407 := by
    have hnat : (335858603 : ℕ)^535*100000000000000^407 ≤ 44202761344871^407*625000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335858603 625000000 44202761344871 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632205711/5000000000 : ℝ)^535 ≤ (43024454128899/100000000000000 : ℝ)^407 := by
    have hnat : (2632205711 : ℕ)^535*100000000000000^407 ≤ 43024454128899^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632205711 5000000000 43024454128899 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (522454959/2500000000 : ℝ)^535 ≤ (12772784509019/100000000000000 : ℝ)^407 := by
    have hnat : (522454959 : ℕ)^535*100000000000000^407 ≤ 12772784509019^407*2500000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522454959 2500000000 12772784509019 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335858603/625000000 : ℝ), (2632205711/5000000000 : ℝ), (-522454959/2500000000 : ℝ)] ![(44202761344871/100000000000000 : ℝ), (43024454128899/100000000000000 : ℝ), (12772784509019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335858603/625000000 : ℝ)|^535 ≤ (44202761344871/100000000000000 : ℝ)^407
        have hw : |(335858603/625000000 : ℝ)|=(335858603/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632205711/5000000000 : ℝ)|^535 ≤ (43024454128899/100000000000000 : ℝ)^407
        have hw : |(2632205711/5000000000 : ℝ)|=(2632205711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-522454959/2500000000 : ℝ)|^535 ≤ (12772784509019/100000000000000 : ℝ)^407
        have hw : |(-522454959/2500000000 : ℝ)|=(522454959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_box_7 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (522848993/1250000000 : ℝ)*x 0 + (2205550027/5000000000 : ℝ)*x 1 + (2205550319/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (522848993/1250000000 : ℝ)^535 ≤ (31799390627817/100000000000000 : ℝ)^407 := by
    have hnat : (522848993 : ℕ)^535*100000000000000^407 ≤ 31799390627817^407*1250000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522848993 1250000000 31799390627817 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2205550027/5000000000 : ℝ)^535 ≤ (3410030170851/10000000000000 : ℝ)^407 := by
    have hnat : (2205550027 : ℕ)^535*10000000000000^407 ≤ 3410030170851^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205550027 5000000000 3410030170851 10000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2205550319/5000000000 : ℝ)^535 ≤ (17050153821501/50000000000000 : ℝ)^407 := by
    have hnat : (2205550319 : ℕ)^535*50000000000000^407 ≤ 17050153821501^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205550319 5000000000 17050153821501 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(522848993/1250000000 : ℝ), (2205550027/5000000000 : ℝ), (2205550319/5000000000 : ℝ)] ![(31799390627817/100000000000000 : ℝ), (3410030170851/10000000000000 : ℝ), (17050153821501/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(522848993/1250000000 : ℝ)|^535 ≤ (31799390627817/100000000000000 : ℝ)^407
        have hw : |(522848993/1250000000 : ℝ)|=(522848993/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2205550027/5000000000 : ℝ)|^535 ≤ (3410030170851/10000000000000 : ℝ)^407
        have hw : |(2205550027/5000000000 : ℝ)|=(2205550027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2205550319/5000000000 : ℝ)|^535 ≤ (17050153821501/50000000000000 : ℝ)^407
        have hw : |(2205550319/5000000000 : ℝ)|=(2205550319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_box_8 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2163409363/10000000000 : ℝ)*x 0 + (1294367067/2500000000 : ℝ)*x 1 + (1351221943/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163409363/10000000000 : ℝ)^535 ≤ (3341814096857/25000000000000 : ℝ)^407 := by
    have hnat : (2163409363 : ℕ)^535*25000000000000^407 ≤ 3341814096857^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163409363 10000000000 3341814096857 25000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1294367067/2500000000 : ℝ)^535 ≤ (21046430062253/50000000000000 : ℝ)^407 := by
    have hnat : (1294367067 : ℕ)^535*50000000000000^407 ≤ 21046430062253^407*2500000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294367067 2500000000 21046430062253 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351221943/2500000000 : ℝ)^535 ≤ (22269941736933/50000000000000 : ℝ)^407 := by
    have hnat : (1351221943 : ℕ)^535*50000000000000^407 ≤ 22269941736933^407*2500000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351221943 2500000000 22269941736933 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2163409363/10000000000 : ℝ), (1294367067/2500000000 : ℝ), (1351221943/2500000000 : ℝ)] ![(3341814096857/25000000000000 : ℝ), (21046430062253/50000000000000 : ℝ), (22269941736933/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2163409363/10000000000 : ℝ)|^535 ≤ (3341814096857/25000000000000 : ℝ)^407
        have hw : |(-2163409363/10000000000 : ℝ)|=(2163409363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1294367067/2500000000 : ℝ)|^535 ≤ (21046430062253/50000000000000 : ℝ)^407
        have hw : |(1294367067/2500000000 : ℝ)|=(1294367067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351221943/2500000000 : ℝ)|^535 ≤ (22269941736933/50000000000000 : ℝ)^407
        have hw : |(1351221943/2500000000 : ℝ)|=(1351221943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_box_9 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1054994277/2000000000 : ℝ)*x 0 + (-406698611/2000000000 : ℝ)*x 1 + (2702443909/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054994277/2000000000 : ℝ)^535 ≤ (4313793540719/10000000000000 : ℝ)^407 := by
    have hnat : (1054994277 : ℕ)^535*10000000000000^407 ≤ 4313793540719^407*2000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054994277 2000000000 4313793540719 10000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (406698611/2000000000 : ℝ)^535 ≤ (6161090304729/50000000000000 : ℝ)^407 := by
    have hnat : (406698611 : ℕ)^535*50000000000000^407 ≤ 6161090304729^407*2000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      406698611 2000000000 6161090304729 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2702443909/5000000000 : ℝ)^535 ≤ (44539883972153/100000000000000 : ℝ)^407 := by
    have hnat : (2702443909 : ℕ)^535*100000000000000^407 ≤ 44539883972153^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702443909 5000000000 44539883972153 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1054994277/2000000000 : ℝ), (-406698611/2000000000 : ℝ), (2702443909/5000000000 : ℝ)] ![(4313793540719/10000000000000 : ℝ), (6161090304729/50000000000000 : ℝ), (44539883972153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1054994277/2000000000 : ℝ)|^535 ≤ (4313793540719/10000000000000 : ℝ)^407
        have hw : |(1054994277/2000000000 : ℝ)|=(1054994277/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-406698611/2000000000 : ℝ)|^535 ≤ (6161090304729/50000000000000 : ℝ)^407
        have hw : |(-406698611/2000000000 : ℝ)|=(406698611/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2702443909/5000000000 : ℝ)|^535 ≤ (44539883972153/100000000000000 : ℝ)^407
        have hw : |(2702443909/5000000000 : ℝ)|=(2702443909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_box_10 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5274971473/10000000000 : ℝ)*x 0 + (1351221939/2500000000 : ℝ)*x 1 + (-101674651/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5274971473/10000000000 : ℝ)^535 ≤ (2696121022073/6250000000000 : ℝ)^407 := by
    have hnat : (5274971473 : ℕ)^535*6250000000000^407 ≤ 2696121022073^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274971473 10000000000 2696121022073 6250000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351221939/2500000000 : ℝ)^535 ≤ (44539883300549/100000000000000 : ℝ)^407 := by
    have hnat : (1351221939 : ℕ)^535*100000000000000^407 ≤ 44539883300549^407*2500000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351221939 2500000000 44539883300549 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (101674651/500000000 : ℝ)^535 ≤ (12322180330671/100000000000000 : ℝ)^407 := by
    have hnat : (101674651 : ℕ)^535*100000000000000^407 ≤ 12322180330671^407*500000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101674651 500000000 12322180330671 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5274971473/10000000000 : ℝ), (1351221939/2500000000 : ℝ), (-101674651/500000000 : ℝ)] ![(2696121022073/6250000000000 : ℝ), (44539883300549/100000000000000 : ℝ), (12322180330671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5274971473/10000000000 : ℝ)|^535 ≤ (2696121022073/6250000000000 : ℝ)^407
        have hw : |(5274971473/10000000000 : ℝ)|=(5274971473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351221939/2500000000 : ℝ)|^535 ≤ (44539883300549/100000000000000 : ℝ)^407
        have hw : |(1351221939/2500000000 : ℝ)|=(1351221939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-101674651/500000000 : ℝ)|^535 ≤ (12322180330671/100000000000000 : ℝ)^407
        have hw : |(-101674651/500000000 : ℝ)|=(101674651/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_box_11 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2256836071/5000000000 : ℝ)*x 0 + (1061356761/2500000000 : ℝ)*x 1 + (2122713503/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2256836071/5000000000 : ℝ)^535 ≤ (3514641005239/10000000000000 : ℝ)^407 := by
    have hnat : (2256836071 : ℕ)^535*10000000000000^407 ≤ 3514641005239^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2256836071 5000000000 3514641005239 10000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1061356761/2500000000 : ℝ)^535 ≤ (648535903103/2000000000000 : ℝ)^407 := by
    have hnat : (1061356761 : ℕ)^535*2000000000000^407 ≤ 648535903103^407*2500000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061356761 2500000000 648535903103 2000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2122713503/5000000000 : ℝ)^535 ≤ (32426794773623/100000000000000 : ℝ)^407 := by
    have hnat : (2122713503 : ℕ)^535*100000000000000^407 ≤ 32426794773623^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122713503 5000000000 32426794773623 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2256836071/5000000000 : ℝ), (1061356761/2500000000 : ℝ), (2122713503/5000000000 : ℝ)] ![(3514641005239/10000000000000 : ℝ), (648535903103/2000000000000 : ℝ), (32426794773623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2256836071/5000000000 : ℝ)|^535 ≤ (3514641005239/10000000000000 : ℝ)^407
        have hw : |(2256836071/5000000000 : ℝ)|=(2256836071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1061356761/2500000000 : ℝ)|^535 ≤ (648535903103/2000000000000 : ℝ)^407
        have hw : |(1061356761/2500000000 : ℝ)|=(1061356761/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2122713503/5000000000 : ℝ)|^535 ≤ (32426794773623/100000000000000 : ℝ)^407
        have hw : |(2122713503/5000000000 : ℝ)|=(2122713503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_box_12 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-491498671/2500000000 : ℝ)*x 0 + (5475546547/10000000000 : ℝ)*x 1 + (5253361823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (491498671/2500000000 : ℝ)^535 ≤ (5893680552979/50000000000000 : ℝ)^407 := by
    have hnat : (491498671 : ℕ)^535*50000000000000^407 ≤ 5893680552979^407*2500000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      491498671 2500000000 5893680552979 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5475546547/10000000000 : ℝ)^535 ≤ (45306851217393/100000000000000 : ℝ)^407 := by
    have hnat : (5475546547 : ℕ)^535*100000000000000^407 ≤ 45306851217393^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5475546547 10000000000 45306851217393 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5253361823/10000000000 : ℝ)^535 ≤ (21452893832091/50000000000000 : ℝ)^407 := by
    have hnat : (5253361823 : ℕ)^535*50000000000000^407 ≤ 21452893832091^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253361823 10000000000 21452893832091 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-491498671/2500000000 : ℝ), (5475546547/10000000000 : ℝ), (5253361823/10000000000 : ℝ)] ![(5893680552979/50000000000000 : ℝ), (45306851217393/100000000000000 : ℝ), (21452893832091/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-491498671/2500000000 : ℝ)|^535 ≤ (5893680552979/50000000000000 : ℝ)^407
        have hw : |(-491498671/2500000000 : ℝ)|=(491498671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5475546547/10000000000 : ℝ)|^535 ≤ (45306851217393/100000000000000 : ℝ)^407
        have hw : |(5475546547/10000000000 : ℝ)|=(5475546547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5253361823/10000000000 : ℝ)|^535 ≤ (21452893832091/50000000000000 : ℝ)^407
        have hw : |(5253361823/10000000000 : ℝ)|=(5253361823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_box_13 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (134537567/250000000 : ℝ)*x 0 + (-523533929/2500000000 : ℝ)*x 1 + (1050672391/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134537567/250000000 : ℝ)^535 ≤ (354293928177/800000000000 : ℝ)^407 := by
    have hnat : (134537567 : ℕ)^535*800000000000^407 ≤ 354293928177^407*250000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134537567 250000000 354293928177 800000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (523533929/2500000000 : ℝ)^535 ≤ (12807469885969/100000000000000 : ℝ)^407 := by
    have hnat : (523533929 : ℕ)^535*100000000000000^407 ≤ 12807469885969^407*2500000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523533929 2500000000 12807469885969 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1050672391/2000000000 : ℝ)^535 ≤ (42905789081319/100000000000000 : ℝ)^407 := by
    have hnat : (1050672391 : ℕ)^535*100000000000000^407 ≤ 42905789081319^407*2000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050672391 2000000000 42905789081319 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134537567/250000000 : ℝ), (-523533929/2500000000 : ℝ), (1050672391/2000000000 : ℝ)] ![(354293928177/800000000000 : ℝ), (12807469885969/100000000000000 : ℝ), (42905789081319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134537567/250000000 : ℝ)|^535 ≤ (354293928177/800000000000 : ℝ)^407
        have hw : |(134537567/250000000 : ℝ)|=(134537567/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-523533929/2500000000 : ℝ)|^535 ≤ (12807469885969/100000000000000 : ℝ)^407
        have hw : |(-523533929/2500000000 : ℝ)|=(523533929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1050672391/2000000000 : ℝ)|^535 ≤ (42905789081319/100000000000000 : ℝ)^407
        have hw : |(1050672391/2000000000 : ℝ)|=(1050672391/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_box_14 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5381502879/10000000000 : ℝ)*x 0 + (2626680841/5000000000 : ℝ)*x 1 + (-523533953/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5381502879/10000000000 : ℝ)^535 ≤ (2214337158741/5000000000000 : ℝ)^407 := by
    have hnat : (5381502879 : ℕ)^535*5000000000000^407 ≤ 2214337158741^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5381502879 10000000000 2214337158741 5000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2626680841/5000000000 : ℝ)^535 ≤ (21452893075211/50000000000000 : ℝ)^407 := by
    have hnat : (2626680841 : ℕ)^535*50000000000000^407 ≤ 21452893075211^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626680841 5000000000 21452893075211 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (523533953/2500000000 : ℝ)^535 ≤ (12807470657741/100000000000000 : ℝ)^407 := by
    have hnat : (523533953 : ℕ)^535*100000000000000^407 ≤ 12807470657741^407*2500000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523533953 2500000000 12807470657741 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5381502879/10000000000 : ℝ), (2626680841/5000000000 : ℝ), (-523533953/2500000000 : ℝ)] ![(2214337158741/5000000000000 : ℝ), (21452893075211/50000000000000 : ℝ), (12807470657741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5381502879/10000000000 : ℝ)|^535 ≤ (2214337158741/5000000000000 : ℝ)^407
        have hw : |(5381502879/10000000000 : ℝ)|=(5381502879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2626680841/5000000000 : ℝ)|^535 ≤ (21452893075211/50000000000000 : ℝ)^407
        have hw : |(2626680841/5000000000 : ℝ)|=(2626680841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-523533953/2500000000 : ℝ)|^535 ≤ (12807470657741/100000000000000 : ℝ)^407
        have hw : |(-523533953/2500000000 : ℝ)|=(523533953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_box_15 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (415626997/1000000000 : ℝ)*x 0 + (442412243/1000000000 : ℝ)*x 1 + (2212061253/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (415626997/1000000000 : ℝ)^535 ≤ (31534611415831/100000000000000 : ℝ)^407 := by
    have hnat : (415626997 : ℕ)^535*100000000000000^407 ≤ 31534611415831^407*1000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415626997 1000000000 31534611415831 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (442412243/1000000000 : ℝ)^535 ≤ (34232693891833/100000000000000 : ℝ)^407 := by
    have hnat : (442412243 : ℕ)^535*100000000000000^407 ≤ 34232693891833^407*1000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442412243 1000000000 34232693891833 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2212061253/5000000000 : ℝ)^535 ≤ (17116347332423/50000000000000 : ℝ)^407 := by
    have hnat : (2212061253 : ℕ)^535*50000000000000^407 ≤ 17116347332423^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2212061253 5000000000 17116347332423 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(415626997/1000000000 : ℝ), (442412243/1000000000 : ℝ), (2212061253/5000000000 : ℝ)] ![(31534611415831/100000000000000 : ℝ), (34232693891833/100000000000000 : ℝ), (17116347332423/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(415626997/1000000000 : ℝ)|^535 ≤ (31534611415831/100000000000000 : ℝ)^407
        have hw : |(415626997/1000000000 : ℝ)|=(415626997/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(442412243/1000000000 : ℝ)|^535 ≤ (34232693891833/100000000000000 : ℝ)^407
        have hw : |(442412243/1000000000 : ℝ)|=(442412243/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2212061253/5000000000 : ℝ)|^535 ≤ (17116347332423/50000000000000 : ℝ)^407
        have hw : |(2212061253/5000000000 : ℝ)|=(2212061253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1320_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153862399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3673/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11097/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62847/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58899/100000 : ℝ) ∧ (3193/4000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (42133/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3673/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11097/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3673/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11097/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3673/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11097/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3673/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11097/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3673/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11097/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3673/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11097/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11097/100000 : ℝ) ^ (4279/1024 : ℝ) ≤ (2047482200472697/20000000000000000000 : ℝ) := by
    have hpowers : (11097/100000 : ℝ)^4279 ≤ (2047482200472697/20000000000000000000 : ℝ)^1024 := by
      have hnat : (11097 : ℕ)^4279*20000000000000000000^1024 ≤ 2047482200472697^1024*100000^4279 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11097 100000 2047482200472697 20000000000000000000 4279 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11097/100000 : ℝ)) (X := (2047482200472697/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3673/25000 : ℝ) ^ (4279/1024 : ℝ) ≤ (16536436720982933/50000000000000000000 : ℝ) := by
    have hpowers : (3673/25000 : ℝ)^4279 ≤ (16536436720982933/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3673 : ℕ)^4279*50000000000000000000^1024 ≤ 16536436720982933^1024*25000^4279 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3673 25000 16536436720982933 50000000000000000000 4279 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3673/25000 : ℝ)) (X := (16536436720982933/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002047482200472697/10000000000000000000 : ℝ) ≤ (2500122485307209/2500000000000000 : ℝ) ^ (4279/1024 : ℝ) := by
    have hpowers : (10002047482200472697/10000000000000000000 : ℝ)^1024 ≤ (2500122485307209/2500000000000000 : ℝ)^4279 := by
      have hnat : (10002047482200472697 : ℕ)^1024*2500000000000000^4279 ≤ 2500122485307209^4279*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002047482200472697 10000000000000000000 2500122485307209 2500000000000000 1024 4279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500122485307209/2500000000000000 : ℝ)) (X := (10002047482200472697/10000000000000000000 : ℝ)) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100043310284444329351/100000000000000000000 : ℝ) ≤ (5000518140072983/5000000000000000 : ℝ) ^ (4279/1024 : ℝ) := by
    have hpowers : (100043310284444329351/100000000000000000000 : ℝ)^1024 ≤ (5000518140072983/5000000000000000 : ℝ)^4279 := by
      have hnat : (100043310284444329351 : ℕ)^1024*5000000000000000^4279 ≤ 5000518140072983^4279*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100043310284444329351 100000000000000000000 5000518140072983 5000000000000000 1024 4279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000518140072983/5000000000000000 : ℝ)) (X := (100043310284444329351/100000000000000000000 : ℝ)) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016536436720982933/25000000000000000000 : ℝ) ≤ (1250197827382887/1250000000000000 : ℝ) ^ (4279/1024 : ℝ) := by
    have hpowers : (25016536436720982933/25000000000000000000 : ℝ)^1024 ≤ (1250197827382887/1250000000000000 : ℝ)^4279 := by
      have hnat : (25016536436720982933 : ℕ)^1024*1250000000000000^4279 ≤ 1250197827382887^4279*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016536436720982933 25000000000000000000 1250197827382887 1250000000000000 1024 4279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250197827382887/1250000000000000 : ℝ)) (X := (25016536436720982933/25000000000000000000 : ℝ)) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2047482200472697/20000000000000000000 : ℝ) ≤ ((179698179463954411/179750000000000000 : ℝ)+2*(54633891713/35950000000000 : ℝ)*(11097/100000 : ℝ))^(4279/1024 : ℝ) := by
    rw [show (179698179463954411/179750000000000000 : ℝ)+2*(54633891713/35950000000000 : ℝ)*(11097/100000 : ℝ)=(2500122485307209/2500000000000000 : ℝ) by norm_num, show 1+2*(2047482200472697/20000000000000000000 : ℝ)=(10002047482200472697/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16536436720982933/50000000000000000000 : ℝ)+(2047482200472697/20000000000000000000 : ℝ) ≤ ((179698179463954411/179750000000000000 : ℝ)+(54633891713/35950000000000 : ℝ)*((3673/25000 : ℝ)+(11097/100000 : ℝ)))^(4279/1024 : ℝ) := by
    rw [show (179698179463954411/179750000000000000 : ℝ)+(54633891713/35950000000000 : ℝ)*((3673/25000 : ℝ)+(11097/100000 : ℝ))=(5000518140072983/5000000000000000 : ℝ) by norm_num, show 1+(16536436720982933/50000000000000000000 : ℝ)+(2047482200472697/20000000000000000000 : ℝ)=(100043310284444329351/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16536436720982933/50000000000000000000 : ℝ) ≤ ((179698179463954411/179750000000000000 : ℝ)+2*(54633891713/35950000000000 : ℝ)*(3673/25000 : ℝ))^(4279/1024 : ℝ) := by
    rw [show (179698179463954411/179750000000000000 : ℝ)+2*(54633891713/35950000000000 : ℝ)*(3673/25000 : ℝ)=(1250197827382887/1250000000000000 : ℝ) by norm_num, show 1+2*(16536436720982933/50000000000000000000 : ℝ)=(25016536436720982933/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (179698179463954411/179750000000000000 : ℝ)*(X 1 0+X 2 0)+(54633891713/35950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4279/1024 : ℝ)) (lo := (11097/100000 : ℝ)) (hi := (3673/25000 : ℝ)) (c := (179698179463954411/179750000000000000 : ℝ)) (alpha := (54633891713/35950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (179698179463954411/179750000000000000 : ℝ)*(X 0 1+X 2 1)+(54633891713/35950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4279/1024 : ℝ)) (lo := (11097/100000 : ℝ)) (hi := (3673/25000 : ℝ)) (c := (179698179463954411/179750000000000000 : ℝ)) (alpha := (54633891713/35950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (179698179463954411/179750000000000000 : ℝ)*(X 0 2+X 1 2)+(54633891713/35950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4279/1024 : ℝ)) (lo := (11097/100000 : ℝ)) (hi := (3673/25000 : ℝ)) (c := (179698179463954411/179750000000000000 : ℝ)) (alpha := (54633891713/35950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-473525517/2500000000 : ℝ)*X 0 0+(269542929/500000000 : ℝ)*X 0 1+(1347714677/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1321210071/2500000000 : ℝ)*X 1 0+(-31863113/156250000 : ℝ)*X 1 1+(5390858321/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1056968013/2000000000 : ℝ)*X 2 0+(539085869/1000000000 : ℝ)*X 2 1+(-2039239027/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((28007071/62500000 : ℝ)*X 0 0+(2130992403/5000000000 : ℝ)*X 0 1+(852397033/2000000000 : ℝ)*X 0 2+(28007071/62500000 : ℝ)*X 1 0+(2130992403/5000000000 : ℝ)*X 1 1+(852397033/2000000000 : ℝ)*X 1 2+(28007071/62500000 : ℝ)*X 2 0+(2130992403/5000000000 : ℝ)*X 2 1+(852397033/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2234920951/10000000000 : ℝ)*X 0 0+(5264412999/10000000000 : ℝ)*X 0 1+(5264411871/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5373736829/10000000000 : ℝ)*X 1 0+(-2089820457/10000000000 : ℝ)*X 1 1+(2632205891/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((335858603/625000000 : ℝ)*X 2 0+(2632205711/5000000000 : ℝ)*X 2 1+(-522454959/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((522848993/1250000000 : ℝ)*X 0 0+(2205550027/5000000000 : ℝ)*X 0 1+(2205550319/5000000000 : ℝ)*X 0 2+(522848993/1250000000 : ℝ)*X 1 0+(2205550027/5000000000 : ℝ)*X 1 1+(2205550319/5000000000 : ℝ)*X 1 2+(522848993/1250000000 : ℝ)*X 2 0+(2205550027/5000000000 : ℝ)*X 2 1+(2205550319/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2163409363/10000000000 : ℝ)*X 0 0+(1294367067/2500000000 : ℝ)*X 0 1+(1351221943/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1054994277/2000000000 : ℝ)*X 1 0+(-406698611/2000000000 : ℝ)*X 1 1+(2702443909/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5274971473/10000000000 : ℝ)*X 2 0+(1351221939/2500000000 : ℝ)*X 2 1+(-101674651/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2256836071/5000000000 : ℝ)*X 0 0+(1061356761/2500000000 : ℝ)*X 0 1+(2122713503/5000000000 : ℝ)*X 0 2+(2256836071/5000000000 : ℝ)*X 1 0+(1061356761/2500000000 : ℝ)*X 1 1+(2122713503/5000000000 : ℝ)*X 1 2+(2256836071/5000000000 : ℝ)*X 2 0+(1061356761/2500000000 : ℝ)*X 2 1+(2122713503/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-491498671/2500000000 : ℝ)*X 0 0+(5475546547/10000000000 : ℝ)*X 0 1+(5253361823/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((134537567/250000000 : ℝ)*X 1 0+(-523533929/2500000000 : ℝ)*X 1 1+(1050672391/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5381502879/10000000000 : ℝ)*X 2 0+(2626680841/5000000000 : ℝ)*X 2 1+(-523533953/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((415626997/1000000000 : ℝ)*X 0 0+(442412243/1000000000 : ℝ)*X 0 1+(2212061253/5000000000 : ℝ)*X 0 2+(415626997/1000000000 : ℝ)*X 1 0+(442412243/1000000000 : ℝ)*X 1 1+(2212061253/5000000000 : ℝ)*X 1 2+(415626997/1000000000 : ℝ)*X 2 0+(442412243/1000000000 : ℝ)*X 2 1+(2212061253/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62847/100000 : ℝ) ≤ (-706023323963180035034477674503/1123437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (126111587/100000000000000 : ℝ)*(upper0) + (186028119/100000000000000 : ℝ)*(lower1) + (395449777/100000000000000 : ℝ)*(lower2) + (1447881598175993/50000000000000 : ℝ)*(major0) + (1447881598175993/50000000000000 : ℝ)*(major1) + (1447881598175993/50000000000000 : ℝ)*(major2) + (17955381489/50000000000000 : ℝ)*(sp1) + (13818514003/50000000000000 : ℝ)*(sp2) + (3930410760032287/100000000000000 : ℝ)*(sp4) + (3930391440744817/100000000000000 : ℝ)*(sp5) + (3930399714479789/100000000000000 : ℝ)*(sp6) + (1882033899869239/100000000000000 : ℝ)*(sp7) + (4147868877/25000000000000 : ℝ)*(sp8) + (6722896579/50000000000000 : ℝ)*(sp15) + (1882047345662397/100000000000000 : ℝ)*(f.failure) + (786085470301559/20000000000000 : ℝ)*(f.sum) + (12048476405711/3595000000000000000000000000 : ℝ)*base65 + (51901111194012377/8987500000000000000000000000000 : ℝ)*base68 + (8833944815512377/8987500000000000000000000000000 : ℝ)*base70 + (48077785715787377/8987500000000000000000000000000 : ℝ)*base72 + (559758585341/3595000000000000000000000000 : ℝ)*base73 + (25071338906975123/8987500000000000000000000000000 : ℝ)*base75 + (20273027698574877/8987500000000000000000000000000 : ℝ)*base78 + (39377418572499877/8987500000000000000000000000000 : ℝ)*base80 + (2407031952989/898750000000000000000000000 : ℝ)*base81 + (46510403/10000000000000000000000 : ℝ)*base89 + (46510403/10000000000000000000000 : ℝ)*base91 + (46510403/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (58899/100000 : ℝ) ≤ (2646866010579686597962196335347/4493750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (37462709/100000000000000 : ℝ)*(lower1) + (12875421/100000000000000 : ℝ)*(lower3) + (24832633/50000000000000 : ℝ)*(upper5) + (2963723140908759/100000000000000 : ℝ)*(major0) + (2963723140908759/100000000000000 : ℝ)*(major1) + (2963723140908759/100000000000000 : ℝ)*(major2) + (3981593753696667/100000000000000 : ℝ)*(sp0) + (62210783483967/1562500000000 : ℝ)*(sp1) + (99539462443219/2500000000000 : ℝ)*(sp2) + (963108298073831/50000000000000 : ℝ)*(sp3) + (49485661/100000000000000 : ℝ)*(sp7) + (52904655847/50000000000000 : ℝ)*(sp9) + (8727278411/50000000000000 : ℝ)*(sp10) + (1099294457/50000000000000 : ℝ)*(sp12) + (963108322816661/50000000000000 : ℝ)*(f.failure) + (1990797976142791/50000000000000 : ℝ)*(f.sum) + (136803238503/1797500000000000000000000000 : ℝ)*base66 + (82843602602479051/17975000000000000000000000000000 : ℝ)*base68 + (225385220609570949/17975000000000000000000000000000 : ℝ)*base69 + (91469690098429051/17975000000000000000000000000000 : ℝ)*base72 + (1432710295367/1797500000000000000000000000 : ℝ)*base73 + (491995398734379051/17975000000000000000000000000000 : ℝ)*base76 + (37543392734829051/17975000000000000000000000000000 : ℝ)*base78 + (161995850279129051/17975000000000000000000000000000 : ℝ)*base80 + (56122731853237/1797500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (51370261/5000000000000000000000 : ℝ)*base90 + (51370261/5000000000000000000000 : ℝ)*base92 + (51370261/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (3193/4000 : ℝ) ≤ (358722854346704831642227226457/449375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (137303/25000000000000 : ℝ)*(upper0) + (12046801/100000000000000 : ℝ)*(lower3) + (29595399/100000000000000 : ℝ)*(upper4) + (163835019590607/5000000000000 : ℝ)*(major0) + (163835019590607/5000000000000 : ℝ)*(major1) + (163835019590607/5000000000000 : ℝ)*(major2) + (1156096969/5000000000000 : ℝ)*(sp1) + (6950934441/50000000000000 : ℝ)*(sp2) + (7325782767/100000000000000 : ℝ)*(sp3) + (2351643/20000000000000 : ℝ)*(sp4) + (439716137205613/10000000000000 : ℝ)*(sp8) + (1099284565468741/25000000000000 : ℝ)*(sp9) + (2198573740972731/50000000000000 : ℝ)*(sp10) + (53240576344241/2500000000000 : ℝ)*(sp11) + (266203797444051/12500000000000 : ℝ)*(f.failure) + (549645172976793/12500000000000 : ℝ)*(f.sum) + (299202024273/719000000000000000000000000 : ℝ)*base65 + (1428528694956227/898750000000000000000000000000 : ℝ)*base67 + (1506036865297477/898750000000000000000000000000 : ℝ)*base69 + (6777233440597477/898750000000000000000000000000 : ℝ)*base71 + (686737068153/71900000000000000000000000 : ℝ)*base74 + (6061839345131227/898750000000000000000000000000 : ℝ)*base75 + (7330617366442477/898750000000000000000000000000 : ℝ)*base77 + (7258784450939977/898750000000000000000000000000 : ℝ)*base79 + (1617207630851/719000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (5138349/1250000000000000000000 : ℝ)*base89 + (5138349/1250000000000000000000 : ℝ)*base91 + (5138349/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-42133/50000 : ℝ) ≤ (-118330857768880514743009672083/140429687500000000000000000000 : ℝ) := by norm_num
    linear_combination (1973489/20000000000000 : ℝ)*(lower1) + (6114853/20000000000000 : ℝ)*(upper3) + (43646911/100000000000000 : ℝ)*(upper5) + (828231333045553/25000000000000 : ℝ)*(major0) + (828231333045553/25000000000000 : ℝ)*(major1) + (828231333045553/25000000000000 : ℝ)*(major2) + (540644483/20000000000000 : ℝ)*(sp4) + (23068266947/20000000000000 : ℝ)*(sp6) + (44550218129/100000000000000 : ℝ)*(sp7) + (1054691089/100000000000000 : ℝ)*(sp8) + (4500760608480609/100000000000000 : ℝ)*(sp12) + (4500764366394113/100000000000000 : ℝ)*(sp13) + (2250324512529689/50000000000000 : ℝ)*(sp14) + (1076564777255241/50000000000000 : ℝ)*(sp15) + (215317410472861/10000000000000 : ℝ)*(f.failure) + (4500764366394113/100000000000000 : ℝ)*(f.sum) + (4134994963637/898750000000000000000000000 : ℝ)*base66 + (10167751936108217/4493750000000000000000000000000 : ℝ)*base68 + (59130226464683217/4493750000000000000000000000000 : ℝ)*base70 + (23651551555045717/4493750000000000000000000000000 : ℝ)*base72 + (678136387449/1797500000000000000000000000 : ℝ)*base74 + (17612598443839467/4493750000000000000000000000000 : ℝ)*base76 + (27456992528408217/4493750000000000000000000000000 : ℝ)*base78 + (44944224429320717/4493750000000000000000000000000 : ℝ)*base80 + (12938120812749/1797500000000000000000000000 : ℝ)*base82 + (2146461/1000000000000000000000 : ℝ)*base90 + (2146461/1000000000000000000000 : ℝ)*base92 + (2146461/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1320_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153862399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3673/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11097/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62847/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58899/100000 : ℝ) else (3193/4000 : ℝ) ≤ X j i ∧ X j i ≤ (42133/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1320_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1320_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153862399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14703/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11087/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62847/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58899/100000 : ℝ) else (3193/4000 : ℝ) ≤ X j i ∧ X j i ≤ (42133/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1320_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1320_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1320_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153862399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14703/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11087/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62847/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58899/100000 : ℝ) else (3193/4000 : ℝ) ≤ X j i ∧ X j i ≤ (42133/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1320_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

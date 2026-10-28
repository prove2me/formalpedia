-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1103_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:02:22.041607+00:00
-- url     : https://prove2.me/submissions/ecc5a9d2-8ba9-43f6-8986-3e028e592972

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
theorem support_rectangle_w1103_s6_0 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2185637501/10000000000 : ℝ)*x 0 + (1348541107/2500000000 : ℝ)*x 1 + (2632340563/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185637501/10000000000 : ℝ)^1037 ≤ (13277057132567/100000000000000 : ℝ)^781 := by
    have hnat : (2185637501 : ℕ)^1037*100000000000000^781 ≤ 13277057132567^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185637501 10000000000 13277057132567 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348541107/2500000000 : ℝ)^1037 ≤ (5507607599327/12500000000000 : ℝ)^781 := by
    have hnat : (1348541107 : ℕ)^1037*12500000000000^781 ≤ 5507607599327^781*2500000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348541107 2500000000 5507607599327 12500000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632340563/5000000000 : ℝ)^1037 ≤ (21331041023451/50000000000000 : ℝ)^781 := by
    have hnat : (2632340563 : ℕ)^1037*50000000000000^781 ≤ 21331041023451^781*5000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632340563 5000000000 21331041023451 50000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2185637501/10000000000 : ℝ), (1348541107/2500000000 : ℝ), (2632340563/5000000000 : ℝ)] ![(13277057132567/100000000000000 : ℝ), (5507607599327/12500000000000 : ℝ), (21331041023451/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2185637501/10000000000 : ℝ)|^1037 ≤ (13277057132567/100000000000000 : ℝ)^781
        have hw : |(-2185637501/10000000000 : ℝ)|=(2185637501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348541107/2500000000 : ℝ)|^1037 ≤ (5507607599327/12500000000000 : ℝ)^781
        have hw : |(1348541107/2500000000 : ℝ)|=(1348541107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632340563/5000000000 : ℝ)|^1037 ≤ (21331041023451/50000000000000 : ℝ)^781
        have hw : |(2632340563/5000000000 : ℝ)|=(2632340563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_s6_1 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5344996627/10000000000 : ℝ)*x 0 + (-70354061/312500000 : ℝ)*x 1 + (1052936223/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344996627/10000000000 : ℝ)^1037 ≤ (5441050142883/12500000000000 : ℝ)^781 := by
    have hnat : (5344996627 : ℕ)^1037*12500000000000^781 ≤ 5441050142883^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344996627 10000000000 5441050142883 12500000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (70354061/312500000 : ℝ)^1037 ≤ (6904758457387/50000000000000 : ℝ)^781 := by
    have hnat : (70354061 : ℕ)^1037*50000000000000^781 ≤ 6904758457387^781*312500000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70354061 312500000 6904758457387 50000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052936223/2000000000 : ℝ)^1037 ≤ (21331040964273/50000000000000 : ℝ)^781 := by
    have hnat : (1052936223 : ℕ)^1037*50000000000000^781 ≤ 21331040964273^781*2000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052936223 2000000000 21331040964273 50000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344996627/10000000000 : ℝ), (-70354061/312500000 : ℝ), (1052936223/2000000000 : ℝ)] ![(5441050142883/12500000000000 : ℝ), (6904758457387/50000000000000 : ℝ), (21331040964273/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344996627/10000000000 : ℝ)|^1037 ≤ (5441050142883/12500000000000 : ℝ)^781
        have hw : |(5344996627/10000000000 : ℝ)|=(5344996627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-70354061/312500000 : ℝ)|^1037 ≤ (6904758457387/50000000000000 : ℝ)^781
        have hw : |(-70354061/312500000 : ℝ)|=(70354061/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052936223/2000000000 : ℝ)|^1037 ≤ (21331040964273/50000000000000 : ℝ)^781
        have hw : |(1052936223/2000000000 : ℝ)|=(1052936223/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_s6_2 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5344996639/10000000000 : ℝ)*x 0 + (2632340557/5000000000 : ℝ)*x 1 + (-140708121/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344996639/10000000000 : ℝ)^1037 ≤ (21764200636411/50000000000000 : ℝ)^781 := by
    have hnat : (5344996639 : ℕ)^1037*50000000000000^781 ≤ 21764200636411^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344996639 10000000000 21764200636411 50000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632340557/5000000000 : ℝ)^1037 ≤ (21331040958893/50000000000000 : ℝ)^781 := by
    have hnat : (2632340557 : ℕ)^1037*50000000000000^781 ≤ 21331040958893^781*5000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632340557 5000000000 21331040958893 50000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (140708121/625000000 : ℝ)^1037 ≤ (13809516784461/100000000000000 : ℝ)^781 := by
    have hnat : (140708121 : ℕ)^1037*100000000000000^781 ≤ 13809516784461^781*625000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140708121 625000000 13809516784461 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344996639/10000000000 : ℝ), (2632340557/5000000000 : ℝ), (-140708121/625000000 : ℝ)] ![(21764200636411/50000000000000 : ℝ), (21331040958893/50000000000000 : ℝ), (13809516784461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344996639/10000000000 : ℝ)|^1037 ≤ (21764200636411/50000000000000 : ℝ)^781
        have hw : |(5344996639/10000000000 : ℝ)|=(5344996639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632340557/5000000000 : ℝ)|^1037 ≤ (21331040958893/50000000000000 : ℝ)^781
        have hw : |(2632340557/5000000000 : ℝ)|=(2632340557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-140708121/625000000 : ℝ)|^1037 ≤ (13809516784461/100000000000000 : ℝ)^781
        have hw : |(-140708121/625000000 : ℝ)|=(140708121/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_s6_3 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4370175039/10000000000 : ℝ)*x 0 + (848846961/2000000000 : ℝ)*x 1 + (899973889/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4370175039/10000000000 : ℝ)^1037 ≤ (33316531437953/100000000000000 : ℝ)^781 := by
    have hnat : (4370175039 : ℕ)^1037*100000000000000^781 ≤ 33316531437953^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370175039 10000000000 33316531437953 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (848846961/2000000000 : ℝ)^1037 ≤ (32047759301667/100000000000000 : ℝ)^781 := by
    have hnat : (848846961 : ℕ)^1037*100000000000000^781 ≤ 32047759301667^781*2000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848846961 2000000000 32047759301667 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (899973889/2000000000 : ℝ)^1037 ≤ (692714184873/2000000000000 : ℝ)^781 := by
    have hnat : (899973889 : ℕ)^1037*2000000000000^781 ≤ 692714184873^781*2000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899973889 2000000000 692714184873 2000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4370175039/10000000000 : ℝ), (848846961/2000000000 : ℝ), (899973889/2000000000 : ℝ)] ![(33316531437953/100000000000000 : ℝ), (32047759301667/100000000000000 : ℝ), (692714184873/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4370175039/10000000000 : ℝ)|^1037 ≤ (33316531437953/100000000000000 : ℝ)^781
        have hw : |(4370175039/10000000000 : ℝ)|=(4370175039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(848846961/2000000000 : ℝ)|^1037 ≤ (32047759301667/100000000000000 : ℝ)^781
        have hw : |(848846961/2000000000 : ℝ)|=(848846961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(899973889/2000000000 : ℝ)|^1037 ≤ (692714184873/2000000000000 : ℝ)^781
        have hw : |(899973889/2000000000 : ℝ)|=(899973889/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_s6_4 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2185642571/10000000000 : ℝ)*x 0 + (164531503/312500000 : ℝ)*x 1 + (1348459069/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185642571/10000000000 : ℝ)^1037 ≤ (6638549013281/50000000000000 : ℝ)^781 := by
    have hnat : (2185642571 : ℕ)^1037*50000000000000^781 ≤ 6638549013281^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185642571 10000000000 6638549013281 50000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164531503/312500000 : ℝ)^1037 ≤ (853312003237/2000000000000 : ℝ)^781 := by
    have hnat : (164531503 : ℕ)^1037*2000000000000^781 ≤ 853312003237^781*312500000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164531503 312500000 853312003237 2000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348459069/2500000000 : ℝ)^1037 ≤ (44057301800707/100000000000000 : ℝ)^781 := by
    have hnat : (1348459069 : ℕ)^1037*100000000000000^781 ≤ 44057301800707^781*2500000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348459069 2500000000 44057301800707 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2185642571/10000000000 : ℝ), (164531503/312500000 : ℝ), (1348459069/2500000000 : ℝ)] ![(6638549013281/50000000000000 : ℝ), (853312003237/2000000000000 : ℝ), (44057301800707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2185642571/10000000000 : ℝ)|^1037 ≤ (6638549013281/50000000000000 : ℝ)^781
        have hw : |(-2185642571/10000000000 : ℝ)|=(2185642571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164531503/312500000 : ℝ)|^1037 ≤ (853312003237/2000000000000 : ℝ)^781
        have hw : |(164531503/312500000 : ℝ)|=(164531503/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348459069/2500000000 : ℝ)|^1037 ≤ (44057301800707/100000000000000 : ℝ)^781
        have hw : |(1348459069/2500000000 : ℝ)|=(1348459069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_s6_5 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5312287891/10000000000 : ℝ)*x 0 + (-212217479/1000000000 : ℝ)*x 1 + (1348459069/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312287891/10000000000 : ℝ)^1037 ≤ (43175071256319/100000000000000 : ℝ)^781 := by
    have hnat : (5312287891 : ℕ)^1037*100000000000000^781 ≤ 43175071256319^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312287891 10000000000 43175071256319 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (212217479/1000000000 : ℝ)^1037 ≤ (2553525385293/20000000000000 : ℝ)^781 := by
    have hnat : (212217479 : ℕ)^1037*20000000000000^781 ≤ 2553525385293^781*1000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212217479 1000000000 2553525385293 20000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348459069/2500000000 : ℝ)^1037 ≤ (44057301800707/100000000000000 : ℝ)^781 := by
    have hnat : (1348459069 : ℕ)^1037*100000000000000^781 ≤ 44057301800707^781*2500000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348459069 2500000000 44057301800707 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312287891/10000000000 : ℝ), (-212217479/1000000000 : ℝ), (1348459069/2500000000 : ℝ)] ![(43175071256319/100000000000000 : ℝ), (2553525385293/20000000000000 : ℝ), (44057301800707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312287891/10000000000 : ℝ)|^1037 ≤ (43175071256319/100000000000000 : ℝ)^781
        have hw : |(5312287891/10000000000 : ℝ)|=(5312287891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-212217479/1000000000 : ℝ)|^1037 ≤ (2553525385293/20000000000000 : ℝ)^781
        have hw : |(-212217479/1000000000 : ℝ)|=(212217479/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348459069/2500000000 : ℝ)|^1037 ≤ (44057301800707/100000000000000 : ℝ)^781
        have hw : |(1348459069/2500000000 : ℝ)|=(1348459069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_s6_6 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (531228789/1000000000 : ℝ)*x 0 + (1348459069/2500000000 : ℝ)*x 1 + (-212217479/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531228789/1000000000 : ℝ)^1037 ≤ (5396883905691/12500000000000 : ℝ)^781 := by
    have hnat : (531228789 : ℕ)^1037*12500000000000^781 ≤ 5396883905691^781*1000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531228789 1000000000 5396883905691 12500000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348459069/2500000000 : ℝ)^1037 ≤ (44057301800707/100000000000000 : ℝ)^781 := by
    have hnat : (1348459069 : ℕ)^1037*100000000000000^781 ≤ 44057301800707^781*2500000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348459069 2500000000 44057301800707 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (212217479/1000000000 : ℝ)^1037 ≤ (2553525385293/20000000000000 : ℝ)^781 := by
    have hnat : (212217479 : ℕ)^1037*20000000000000^781 ≤ 2553525385293^781*1000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212217479 1000000000 2553525385293 20000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531228789/1000000000 : ℝ), (1348459069/2500000000 : ℝ), (-212217479/1000000000 : ℝ)] ![(5396883905691/12500000000000 : ℝ), (44057301800707/100000000000000 : ℝ), (2553525385293/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531228789/1000000000 : ℝ)|^1037 ≤ (5396883905691/12500000000000 : ℝ)^781
        have hw : |(531228789/1000000000 : ℝ)|=(531228789/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348459069/2500000000 : ℝ)|^1037 ≤ (44057301800707/100000000000000 : ℝ)^781
        have hw : |(1348459069/2500000000 : ℝ)|=(1348459069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-212217479/1000000000 : ℝ)|^1037 ≤ (2553525385293/20000000000000 : ℝ)^781
        have hw : |(-212217479/1000000000 : ℝ)|=(212217479/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_s6_7 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (54627313/125000000 : ℝ)*x 0 + (449922391/1000000000 : ℝ)*x 1 + (2122441353/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (54627313/125000000 : ℝ)^1037 ≤ (832915816833/2500000000000 : ℝ)^781 := by
    have hnat : (54627313 : ℕ)^1037*2500000000000^781 ≤ 832915816833^781*125000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54627313 125000000 832915816833 2500000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (449922391/1000000000 : ℝ)^1037 ≤ (6925822403181/20000000000000 : ℝ)^781 := by
    have hnat : (449922391 : ℕ)^1037*20000000000000^781 ≤ 6925822403181^781*1000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449922391 1000000000 6925822403181 20000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2122441353/5000000000 : ℝ)^1037 ≤ (8013563823507/25000000000000 : ℝ)^781 := by
    have hnat : (2122441353 : ℕ)^1037*25000000000000^781 ≤ 8013563823507^781*5000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122441353 5000000000 8013563823507 25000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(54627313/125000000 : ℝ), (449922391/1000000000 : ℝ), (2122441353/5000000000 : ℝ)] ![(832915816833/2500000000000 : ℝ), (6925822403181/20000000000000 : ℝ), (8013563823507/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(54627313/125000000 : ℝ)|^1037 ≤ (832915816833/2500000000000 : ℝ)^781
        have hw : |(54627313/125000000 : ℝ)|=(54627313/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(449922391/1000000000 : ℝ)|^1037 ≤ (6925822403181/20000000000000 : ℝ)^781
        have hw : |(449922391/1000000000 : ℝ)|=(449922391/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2122441353/5000000000 : ℝ)|^1037 ≤ (8013563823507/25000000000000 : ℝ)^781
        have hw : |(2122441353/5000000000 : ℝ)|=(2122441353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1103_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74356671/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14073/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11257/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11293/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2807/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14073/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11257/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14073/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11257/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14073/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11257/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14073/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11257/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14073/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11257/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14073/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11257/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11257/100000 : ℝ) ^ (8295/2048 : ℝ) ≤ (14387452212530451/100000000000000000000 : ℝ) := by
    have hpowers : (11257/100000 : ℝ)^8295 ≤ (14387452212530451/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11257 : ℕ)^8295*100000000000000000000^2048 ≤ 14387452212530451^2048*100000^8295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11257 100000 14387452212530451 100000000000000000000 8295 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11257/100000 : ℝ)) (X := (14387452212530451/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8295 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14073/100000 : ℝ) ^ (8295/2048 : ℝ) ≤ (35539931709185627/100000000000000000000 : ℝ) := by
    have hpowers : (14073/100000 : ℝ)^8295 ≤ (35539931709185627/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14073 : ℕ)^8295*100000000000000000000^2048 ≤ 35539931709185627^2048*100000^8295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14073 100000 35539931709185627 100000000000000000000 8295 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14073/100000 : ℝ)) (X := (35539931709185627/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8295 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014387452212530451/50000000000000000000 : ℝ) ≤ (2500177590777617/2500000000000000 : ℝ) ^ (8295/2048 : ℝ) := by
    have hpowers : (50014387452212530451/50000000000000000000 : ℝ)^2048 ≤ (2500177590777617/2500000000000000 : ℝ)^8295 := by
      have hnat : (50014387452212530451 : ℕ)^2048*2500000000000000^8295 ≤ 2500177590777617^8295*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014387452212530451 50000000000000000000 2500177590777617 2500000000000000 2048 8295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500177590777617/2500000000000000 : ℝ)) (X := (50014387452212530451/50000000000000000000 : ℝ)) (by norm_num) 8295 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024963691960858039/50000000000000000000 : ℝ) ≤ (10001232454061099/10000000000000000 : ℝ) ^ (8295/2048 : ℝ) := by
    have hpowers : (50024963691960858039/50000000000000000000 : ℝ)^2048 ≤ (10001232454061099/10000000000000000 : ℝ)^8295 := by
      have hnat : (50024963691960858039 : ℕ)^2048*10000000000000000^8295 ≤ 10001232454061099^8295*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024963691960858039 50000000000000000000 10001232454061099 10000000000000000 2048 8295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001232454061099/10000000000000000 : ℝ)) (X := (50024963691960858039/50000000000000000000 : ℝ)) (by norm_num) 8295 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035539931709185627/50000000000000000000 : ℝ) ≤ (1000175454501173/1000000000000000 : ℝ) ^ (8295/2048 : ℝ) := by
    have hpowers : (50035539931709185627/50000000000000000000 : ℝ)^2048 ≤ (1000175454501173/1000000000000000 : ℝ)^8295 := by
      have hnat : (50035539931709185627 : ℕ)^2048*1000000000000000^8295 ≤ 1000175454501173^8295*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035539931709185627 50000000000000000000 1000175454501173 1000000000000000 2048 8295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000175454501173/1000000000000000 : ℝ)) (X := (50035539931709185627/50000000000000000000 : ℝ)) (by norm_num) 8295 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14387452212530451/100000000000000000000 : ℝ) ≤ ((14075123013428285777/14080000000000000000 : ℝ)+2*(522090950631/281600000000000 : ℝ)*(11257/100000 : ℝ))^(8295/2048 : ℝ) := by
    rw [show (14075123013428285777/14080000000000000000 : ℝ)+2*(522090950631/281600000000000 : ℝ)*(11257/100000 : ℝ)=(2500177590777617/2500000000000000 : ℝ) by norm_num, show 1+2*(14387452212530451/100000000000000000000 : ℝ)=(50014387452212530451/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35539931709185627/100000000000000000000 : ℝ)+(14387452212530451/100000000000000000000 : ℝ) ≤ ((14075123013428285777/14080000000000000000 : ℝ)+(522090950631/281600000000000 : ℝ)*((14073/100000 : ℝ)+(11257/100000 : ℝ)))^(8295/2048 : ℝ) := by
    rw [show (14075123013428285777/14080000000000000000 : ℝ)+(522090950631/281600000000000 : ℝ)*((14073/100000 : ℝ)+(11257/100000 : ℝ))=(10001232454061099/10000000000000000 : ℝ) by norm_num, show 1+(35539931709185627/100000000000000000000 : ℝ)+(14387452212530451/100000000000000000000 : ℝ)=(50024963691960858039/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35539931709185627/100000000000000000000 : ℝ) ≤ ((14075123013428285777/14080000000000000000 : ℝ)+2*(522090950631/281600000000000 : ℝ)*(14073/100000 : ℝ))^(8295/2048 : ℝ) := by
    rw [show (14075123013428285777/14080000000000000000 : ℝ)+2*(522090950631/281600000000000 : ℝ)*(14073/100000 : ℝ)=(1000175454501173/1000000000000000 : ℝ) by norm_num, show 1+2*(35539931709185627/100000000000000000000 : ℝ)=(50035539931709185627/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14075123013428285777/14080000000000000000 : ℝ)*(X 1 0+X 2 0)+(522090950631/281600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8295/2048 : ℝ)) (lo := (11257/100000 : ℝ)) (hi := (14073/100000 : ℝ)) (c := (14075123013428285777/14080000000000000000 : ℝ)) (alpha := (522090950631/281600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14075123013428285777/14080000000000000000 : ℝ)*(X 0 1+X 2 1)+(522090950631/281600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8295/2048 : ℝ)) (lo := (11257/100000 : ℝ)) (hi := (14073/100000 : ℝ)) (c := (14075123013428285777/14080000000000000000 : ℝ)) (alpha := (522090950631/281600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14075123013428285777/14080000000000000000 : ℝ)*(X 0 2+X 1 2)+(522090950631/281600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8295/2048 : ℝ)) (lo := (11257/100000 : ℝ)) (hi := (14073/100000 : ℝ)) (c := (14075123013428285777/14080000000000000000 : ℝ)) (alpha := (522090950631/281600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2185637501/10000000000 : ℝ)*X 0 0+(1348541107/2500000000 : ℝ)*X 0 1+(2632340563/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344996627/10000000000 : ℝ)*X 1 0+(-70354061/312500000 : ℝ)*X 1 1+(1052936223/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344996639/10000000000 : ℝ)*X 2 0+(2632340557/5000000000 : ℝ)*X 2 1+(-140708121/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4370175039/10000000000 : ℝ)*X 0 0+(848846961/2000000000 : ℝ)*X 0 1+(899973889/2000000000 : ℝ)*X 0 2+(4370175039/10000000000 : ℝ)*X 1 0+(848846961/2000000000 : ℝ)*X 1 1+(899973889/2000000000 : ℝ)*X 1 2+(4370175039/10000000000 : ℝ)*X 2 0+(848846961/2000000000 : ℝ)*X 2 1+(899973889/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2185642571/10000000000 : ℝ)*X 0 0+(164531503/312500000 : ℝ)*X 0 1+(1348459069/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312287891/10000000000 : ℝ)*X 1 0+(-212217479/1000000000 : ℝ)*X 1 1+(1348459069/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((531228789/1000000000 : ℝ)*X 2 0+(1348459069/2500000000 : ℝ)*X 2 1+(-212217479/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((54627313/125000000 : ℝ)*X 0 0+(449922391/1000000000 : ℝ)*X 0 1+(2122441353/5000000000 : ℝ)*X 0 2+(54627313/125000000 : ℝ)*X 1 0+(449922391/1000000000 : ℝ)*X 1 1+(2122441353/5000000000 : ℝ)*X 1 2+(54627313/125000000 : ℝ)*X 2 0+(449922391/1000000000 : ℝ)*X 2 1+(2122441353/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (188631552504756899643/55000000000000000000000000 : ℝ) := by norm_num
    linear_combination (739005603/100000000000000 : ℝ)*(base19) + (703255567/100000000000000 : ℝ)*(base23) + (28376033/100000000000000 : ℝ)*(lower2) + (16590153/20000000000000 : ℝ)*(upper3) + (71082039/100000000000000 : ℝ)*(upper5) + (11362203984047/195312500000 : ℝ)*(major0) + (11362203984047/195312500000 : ℝ)*(major1) + (11362203984047/195312500000 : ℝ)*(major2) + (7723023004914891/100000000000000 : ℝ)*(sp0) + (7723042280334163/100000000000000 : ℝ)*(sp1) + (3861521158042099/50000000000000 : ℝ)*(sp2) + (1955921494449549/50000000000000 : ℝ)*(sp3) + (10007212437/50000000000000 : ℝ)*(sp4) + (10757103103/100000000000000 : ℝ)*(sp7) + (3911853746002201/100000000000000 : ℝ)*(f.failure) + (1544608603867953/20000000000000 : ℝ)*(f.sum) + (299654385021/55000000000000000000000000 : ℝ)*base66 + (40169696599849519/2750000000000000000000000000000 : ℝ)*base67 + (51597052248349519/2750000000000000000000000000000 : ℝ)*base69 + (18214690645400481/2750000000000000000000000000000 : ℝ)*base72 + (204153001447/27500000000000000000000000 : ℝ)*base73 + (12459949702900481/2750000000000000000000000000000 : ℝ)*base76 + (2493332028150481/2750000000000000000000000000000 : ℝ)*base78 + (31779558469849519/2750000000000000000000000000000 : ℝ)*base79 + (132070068657/27500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (25032871/5000000000000000000000 : ℝ)*base89 + (25032871/5000000000000000000000 : ℝ)*base91 + (25032871/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (547317967560903566524640841/176000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (580217387/100000000000000 : ℝ)*(base19) + (628413977/100000000000000 : ℝ)*(base23) + (31446081/50000000000000 : ℝ)*(upper3) + (22707153/100000000000000 : ℝ)*(lower4) + (7988029/12500000000000 : ℝ)*(upper5) + (1461750316125263/25000000000000 : ℝ)*(major0) + (1461750316125263/25000000000000 : ℝ)*(major1) + (1461750316125263/25000000000000 : ℝ)*(major2) + (15823252077/100000000000000 : ℝ)*(sp1) + (16946030907/100000000000000 : ℝ)*(sp2) + (7762276336838801/100000000000000 : ℝ)*(sp4) + (970282491671167/12500000000000 : ℝ)*(sp5) + (7762258762393917/100000000000000 : ℝ)*(sp6) + (3931726088504589/100000000000000 : ℝ)*(sp7) + (3931726088504589/100000000000000 : ℝ)*(f.failure) + (7762276336838801/100000000000000 : ℝ)*(f.sum) + (14631036705673/3520000000000000000000000000 : ℝ)*base65 + (854901095568934351/352000000000000000000000000000000 : ℝ)*base67 + (1565403583120934351/352000000000000000000000000000000 : ℝ)*base69 + (1799828435760934351/352000000000000000000000000000000 : ℝ)*base71 + (23184559065033/3520000000000000000000000000 : ℝ)*base73 + (6813331625840934351/352000000000000000000000000000000 : ℝ)*base75 + (3632117954864934351/352000000000000000000000000000000 : ℝ)*base77 + (5378949206480934351/352000000000000000000000000000000 : ℝ)*base79 + (4523755260087/3520000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (6263219/5000000000000000000000 : ℝ)*base89 + (6263219/5000000000000000000000 : ℝ)*base91 + (6263219/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1103_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74356671/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14073/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11257/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11293/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2807/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1103_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1103_s7_0 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2185672411/10000000000 : ℝ)*x 0 + (5393774169/10000000000 : ℝ)*x 1 + (5265048327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185672411/10000000000 : ℝ)^1037 ≤ (1659667339119/12500000000000 : ℝ)^781 := by
    have hnat : (2185672411 : ℕ)^1037*12500000000000^781 ≤ 1659667339119^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185672411 10000000000 1659667339119 12500000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393774169/10000000000 : ℝ)^1037 ≤ (22028314111589/50000000000000 : ℝ)^781 := by
    have hnat : (5393774169 : ℕ)^1037*50000000000000^781 ≤ 22028314111589^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393774169 10000000000 22028314111589 50000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265048327/10000000000 : ℝ)^1037 ≤ (21333016521119/50000000000000 : ℝ)^781 := by
    have hnat : (5265048327 : ℕ)^1037*50000000000000^781 ≤ 21333016521119^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265048327 10000000000 21333016521119 50000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2185672411/10000000000 : ℝ), (5393774169/10000000000 : ℝ), (5265048327/10000000000 : ℝ)] ![(1659667339119/12500000000000 : ℝ), (22028314111589/50000000000000 : ℝ), (21333016521119/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2185672411/10000000000 : ℝ)|^1037 ≤ (1659667339119/12500000000000 : ℝ)^781
        have hw : |(-2185672411/10000000000 : ℝ)|=(2185672411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393774169/10000000000 : ℝ)|^1037 ≤ (22028314111589/50000000000000 : ℝ)^781
        have hw : |(5393774169/10000000000 : ℝ)|=(5393774169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265048327/10000000000 : ℝ)|^1037 ≤ (21333016521119/50000000000000 : ℝ)^781
        have hw : |(5265048327/10000000000 : ℝ)|=(5265048327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_s7_1 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2672449271/5000000000 : ℝ)*x 0 + (-2250975041/10000000000 : ℝ)*x 1 + (5265048327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672449271/5000000000 : ℝ)^1037 ≤ (1360229391767/3125000000000 : ℝ)^781 := by
    have hnat : (2672449271 : ℕ)^1037*3125000000000^781 ≤ 1360229391767^781*5000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672449271 5000000000 1360229391767 3125000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2250975041/10000000000 : ℝ)^1037 ≤ (13806626399303/100000000000000 : ℝ)^781 := by
    have hnat : (2250975041 : ℕ)^1037*100000000000000^781 ≤ 13806626399303^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250975041 10000000000 13806626399303 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265048327/10000000000 : ℝ)^1037 ≤ (21333016521119/50000000000000 : ℝ)^781 := by
    have hnat : (5265048327 : ℕ)^1037*50000000000000^781 ≤ 21333016521119^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265048327 10000000000 21333016521119 50000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672449271/5000000000 : ℝ), (-2250975041/10000000000 : ℝ), (5265048327/10000000000 : ℝ)] ![(1360229391767/3125000000000 : ℝ), (13806626399303/100000000000000 : ℝ), (21333016521119/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672449271/5000000000 : ℝ)|^1037 ≤ (1360229391767/3125000000000 : ℝ)^781
        have hw : |(2672449271/5000000000 : ℝ)|=(2672449271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2250975041/10000000000 : ℝ)|^1037 ≤ (13806626399303/100000000000000 : ℝ)^781
        have hw : |(-2250975041/10000000000 : ℝ)|=(2250975041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265048327/10000000000 : ℝ)|^1037 ≤ (21333016521119/50000000000000 : ℝ)^781
        have hw : |(5265048327/10000000000 : ℝ)|=(5265048327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_s7_2 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5344898543/10000000000 : ℝ)*x 0 + (658131041/1250000000 : ℝ)*x 1 + (-2250975039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344898543/10000000000 : ℝ)^1037 ≤ (43527340547357/100000000000000 : ℝ)^781 := by
    have hnat : (5344898543 : ℕ)^1037*100000000000000^781 ≤ 43527340547357^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344898543 10000000000 43527340547357 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658131041/1250000000 : ℝ)^1037 ≤ (42666033052997/100000000000000 : ℝ)^781 := by
    have hnat : (658131041 : ℕ)^1037*100000000000000^781 ≤ 42666033052997^781*1250000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658131041 1250000000 42666033052997 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2250975039/10000000000 : ℝ)^1037 ≤ (2761325276603/20000000000000 : ℝ)^781 := by
    have hnat : (2250975039 : ℕ)^1037*20000000000000^781 ≤ 2761325276603^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250975039 10000000000 2761325276603 20000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344898543/10000000000 : ℝ), (658131041/1250000000 : ℝ), (-2250975039/10000000000 : ℝ)] ![(43527340547357/100000000000000 : ℝ), (42666033052997/100000000000000 : ℝ), (2761325276603/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344898543/10000000000 : ℝ)|^1037 ≤ (43527340547357/100000000000000 : ℝ)^781
        have hw : |(5344898543/10000000000 : ℝ)|=(5344898543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658131041/1250000000 : ℝ)|^1037 ≤ (42666033052997/100000000000000 : ℝ)^781
        have hw : |(658131041/1250000000 : ℝ)|=(658131041/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2250975039/10000000000 : ℝ)|^1037 ≤ (2761325276603/20000000000000 : ℝ)^781
        have hw : |(-2250975039/10000000000 : ℝ)|=(2250975039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_s7_3 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (437019437/1000000000 : ℝ)*x 0 + (4244980029/10000000000 : ℝ)*x 1 + (899823837/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (437019437/1000000000 : ℝ)^1037 ≤ (33316727116541/100000000000000 : ℝ)^781 := by
    have hnat : (437019437 : ℕ)^1037*100000000000000^781 ≤ 33316727116541^781*1000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437019437 1000000000 33316727116541 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4244980029/10000000000 : ℝ)^1037 ≤ (1001725971971/3125000000000 : ℝ)^781 := by
    have hnat : (4244980029 : ℕ)^1037*3125000000000^781 ≤ 1001725971971^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244980029 10000000000 1001725971971 3125000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (899823837/2000000000 : ℝ)^1037 ≤ (34628041778359/100000000000000 : ℝ)^781 := by
    have hnat : (899823837 : ℕ)^1037*100000000000000^781 ≤ 34628041778359^781*2000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899823837 2000000000 34628041778359 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(437019437/1000000000 : ℝ), (4244980029/10000000000 : ℝ), (899823837/2000000000 : ℝ)] ![(33316727116541/100000000000000 : ℝ), (1001725971971/3125000000000 : ℝ), (34628041778359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(437019437/1000000000 : ℝ)|^1037 ≤ (33316727116541/100000000000000 : ℝ)^781
        have hw : |(437019437/1000000000 : ℝ)|=(437019437/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4244980029/10000000000 : ℝ)|^1037 ≤ (1001725971971/3125000000000 : ℝ)^781
        have hw : |(4244980029/10000000000 : ℝ)|=(4244980029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(899823837/2000000000 : ℝ)|^1037 ≤ (34628041778359/100000000000000 : ℝ)^781
        have hw : |(899823837/2000000000 : ℝ)|=(899823837/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_s7_4 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2185677381/10000000000 : ℝ)*x 0 + (5265371491/10000000000 : ℝ)*x 1 + (5393449851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185677381/10000000000 : ℝ)^1037 ≤ (13277378800569/100000000000000 : ℝ)^781 := by
    have hnat : (2185677381 : ℕ)^1037*100000000000000^781 ≤ 13277378800569^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185677381 10000000000 13277378800569 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265371491/10000000000 : ℝ)^1037 ≤ (42669510284663/100000000000000 : ℝ)^781 := by
    have hnat : (5265371491 : ℕ)^1037*100000000000000^781 ≤ 42669510284663^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265371491 10000000000 42669510284663 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393449851/10000000000 : ℝ)^1037 ≤ (1762124435767/4000000000000 : ℝ)^781 := by
    have hnat : (5393449851 : ℕ)^1037*4000000000000^781 ≤ 1762124435767^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393449851 10000000000 1762124435767 4000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2185677381/10000000000 : ℝ), (5265371491/10000000000 : ℝ), (5393449851/10000000000 : ℝ)] ![(13277378800569/100000000000000 : ℝ), (42669510284663/100000000000000 : ℝ), (1762124435767/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2185677381/10000000000 : ℝ)|^1037 ≤ (13277378800569/100000000000000 : ℝ)^781
        have hw : |(-2185677381/10000000000 : ℝ)|=(2185677381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265371491/10000000000 : ℝ)|^1037 ≤ (42669510284663/100000000000000 : ℝ)^781
        have hw : |(5265371491/10000000000 : ℝ)|=(5265371491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393449851/10000000000 : ℝ)|^1037 ≤ (1762124435767/4000000000000 : ℝ)^781
        have hw : |(5393449851/10000000000 : ℝ)|=(5393449851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_s7_5 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2656190543/5000000000 : ℝ)*x 0 + (-84902941/400000000 : ℝ)*x 1 + (5393449839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656190543/5000000000 : ℝ)^1037 ≤ (43176076966957/100000000000000 : ℝ)^781 := by
    have hnat : (2656190543 : ℕ)^1037*100000000000000^781 ≤ 43176076966957^781*5000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656190543 5000000000 43176076966957 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84902941/400000000 : ℝ)^1037 ≤ (3192703064217/25000000000000 : ℝ)^781 := by
    have hnat : (84902941 : ℕ)^1037*25000000000000^781 ≤ 3192703064217^781*400000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84902941 400000000 3192703064217 25000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393449839/10000000000 : ℝ)^1037 ≤ (44053110764033/100000000000000 : ℝ)^781 := by
    have hnat : (5393449839 : ℕ)^1037*100000000000000^781 ≤ 44053110764033^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393449839 10000000000 44053110764033 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656190543/5000000000 : ℝ), (-84902941/400000000 : ℝ), (5393449839/10000000000 : ℝ)] ![(43176076966957/100000000000000 : ℝ), (3192703064217/25000000000000 : ℝ), (44053110764033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656190543/5000000000 : ℝ)|^1037 ≤ (43176076966957/100000000000000 : ℝ)^781
        have hw : |(2656190543/5000000000 : ℝ)|=(2656190543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-84902941/400000000 : ℝ)|^1037 ≤ (3192703064217/25000000000000 : ℝ)^781
        have hw : |(-84902941/400000000 : ℝ)|=(84902941/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393449839/10000000000 : ℝ)|^1037 ≤ (44053110764033/100000000000000 : ℝ)^781
        have hw : |(5393449839/10000000000 : ℝ)|=(5393449839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_s7_6 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5312381079/10000000000 : ℝ)*x 0 + (2696724921/5000000000 : ℝ)*x 1 + (-212257353/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312381079/10000000000 : ℝ)^1037 ≤ (43176076891417/100000000000000 : ℝ)^781 := by
    have hnat : (5312381079 : ℕ)^1037*100000000000000^781 ≤ 43176076891417^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312381079 10000000000 43176076891417 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696724921/5000000000 : ℝ)^1037 ≤ (44053110796569/100000000000000 : ℝ)^781 := by
    have hnat : (2696724921 : ℕ)^1037*100000000000000^781 ≤ 44053110796569^781*5000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696724921 5000000000 44053110796569 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (212257353/1000000000 : ℝ)^1037 ≤ (3192703074203/25000000000000 : ℝ)^781 := by
    have hnat : (212257353 : ℕ)^1037*25000000000000^781 ≤ 3192703074203^781*1000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212257353 1000000000 3192703074203 25000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312381079/10000000000 : ℝ), (2696724921/5000000000 : ℝ), (-212257353/1000000000 : ℝ)] ![(43176076891417/100000000000000 : ℝ), (44053110796569/100000000000000 : ℝ), (3192703074203/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312381079/10000000000 : ℝ)|^1037 ≤ (43176076891417/100000000000000 : ℝ)^781
        have hw : |(5312381079/10000000000 : ℝ)|=(5312381079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696724921/5000000000 : ℝ)|^1037 ≤ (44053110796569/100000000000000 : ℝ)^781
        have hw : |(2696724921/5000000000 : ℝ)|=(2696724921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-212257353/1000000000 : ℝ)|^1037 ≤ (3192703074203/25000000000000 : ℝ)^781
        have hw : |(-212257353/1000000000 : ℝ)|=(212257353/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_s7_7 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2185102099/5000000000 : ℝ)*x 0 + (4498481193/10000000000 : ℝ)*x 1 + (4245620343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185102099/5000000000 : ℝ)^1037 ≤ (6663365320171/20000000000000 : ℝ)^781 := by
    have hnat : (2185102099 : ℕ)^1037*20000000000000^781 ≤ 6663365320171^781*5000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185102099 5000000000 6663365320171 20000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4498481193/10000000000 : ℝ)^1037 ≤ (34621521993027/100000000000000 : ℝ)^781 := by
    have hnat : (4498481193 : ℕ)^1037*100000000000000^781 ≤ 34621521993027^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498481193 10000000000 34621521993027 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4245620343/10000000000 : ℝ)^1037 ≤ (3206165139413/10000000000000 : ℝ)^781 := by
    have hnat : (4245620343 : ℕ)^1037*10000000000000^781 ≤ 3206165139413^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4245620343 10000000000 3206165139413 10000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2185102099/5000000000 : ℝ), (4498481193/10000000000 : ℝ), (4245620343/10000000000 : ℝ)] ![(6663365320171/20000000000000 : ℝ), (34621521993027/100000000000000 : ℝ), (3206165139413/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2185102099/5000000000 : ℝ)|^1037 ≤ (6663365320171/20000000000000 : ℝ)^781
        have hw : |(2185102099/5000000000 : ℝ)|=(2185102099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4498481193/10000000000 : ℝ)|^1037 ≤ (34621521993027/100000000000000 : ℝ)^781
        have hw : |(4498481193/10000000000 : ℝ)|=(4498481193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4245620343/10000000000 : ℝ)|^1037 ≤ (3206165139413/10000000000000 : ℝ)^781
        have hw : |(4245620343/10000000000 : ℝ)|=(4245620343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1103_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74356671/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2807/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11293/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11301/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14027/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2807/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11293/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2807/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11293/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2807/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11293/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2807/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11293/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2807/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11293/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2807/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11293/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11293/100000 : ℝ) ^ (8295/2048 : ℝ) ≤ (7287361033177699/50000000000000000000 : ℝ) := by
    have hpowers : (11293/100000 : ℝ)^8295 ≤ (7287361033177699/50000000000000000000 : ℝ)^2048 := by
      have hnat : (11293 : ℕ)^8295*50000000000000000000^2048 ≤ 7287361033177699^2048*100000^8295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11293 100000 7287361033177699 50000000000000000000 8295 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11293/100000 : ℝ)) (X := (7287361033177699/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8295 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2807/20000 : ℝ) ^ (8295/2048 : ℝ) ≤ (35152842522836767/100000000000000000000 : ℝ) := by
    have hpowers : (2807/20000 : ℝ)^8295 ≤ (35152842522836767/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2807 : ℕ)^8295*100000000000000000000^2048 ≤ 35152842522836767^2048*20000^8295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2807 20000 35152842522836767 100000000000000000000 8295 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2807/20000 : ℝ)) (X := (35152842522836767/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8295 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007287361033177699/25000000000000000000 : ℝ) ≤ (10000719608319109/10000000000000000 : ℝ) ^ (8295/2048 : ℝ) := by
    have hpowers : (25007287361033177699/25000000000000000000 : ℝ)^2048 ≤ (10000719608319109/10000000000000000 : ℝ)^8295 := by
      have hnat : (25007287361033177699 : ℕ)^2048*10000000000000000^8295 ≤ 10000719608319109^8295*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007287361033177699 25000000000000000000 10000719608319109 10000000000000000 2048 8295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000719608319109/10000000000000000 : ℝ)) (X := (25007287361033177699/25000000000000000000 : ℝ)) (by norm_num) 8295 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009945512917838433/20000000000000000000 : ℝ) ≤ (500061376122889/500000000000000 : ℝ) ^ (8295/2048 : ℝ) := by
    have hpowers : (20009945512917838433/20000000000000000000 : ℝ)^2048 ≤ (500061376122889/500000000000000 : ℝ)^8295 := by
      have hnat : (20009945512917838433 : ℕ)^2048*500000000000000^8295 ≤ 500061376122889^8295*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009945512917838433 20000000000000000000 500061376122889 500000000000000 2048 8295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500061376122889/500000000000000 : ℝ)) (X := (20009945512917838433/20000000000000000000 : ℝ)) (by norm_num) 8295 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035152842522836767/50000000000000000000 : ℝ) ≤ (10001735436596451/10000000000000000 : ℝ) ^ (8295/2048 : ℝ) := by
    have hpowers : (50035152842522836767/50000000000000000000 : ℝ)^2048 ≤ (10001735436596451/10000000000000000 : ℝ)^8295 := by
      have hnat : (50035152842522836767 : ℕ)^2048*10000000000000000^8295 ≤ 10001735436596451^8295*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035152842522836767 50000000000000000000 10001735436596451 10000000000000000 2048 8295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001735436596451/10000000000000000 : ℝ)) (X := (50035152842522836767/50000000000000000000 : ℝ)) (by norm_num) 8295 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7287361033177699/50000000000000000000 : ℝ) ≤ ((3426312677159371709/3427500000000000000 : ℝ)+2*(507914138671/274200000000000 : ℝ)*(11293/100000 : ℝ))^(8295/2048 : ℝ) := by
    rw [show (3426312677159371709/3427500000000000000 : ℝ)+2*(507914138671/274200000000000 : ℝ)*(11293/100000 : ℝ)=(10000719608319109/10000000000000000 : ℝ) by norm_num, show 1+2*(7287361033177699/50000000000000000000 : ℝ)=(25007287361033177699/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35152842522836767/100000000000000000000 : ℝ)+(7287361033177699/50000000000000000000 : ℝ) ≤ ((3426312677159371709/3427500000000000000 : ℝ)+(507914138671/274200000000000 : ℝ)*((2807/20000 : ℝ)+(11293/100000 : ℝ)))^(8295/2048 : ℝ) := by
    rw [show (3426312677159371709/3427500000000000000 : ℝ)+(507914138671/274200000000000 : ℝ)*((2807/20000 : ℝ)+(11293/100000 : ℝ))=(500061376122889/500000000000000 : ℝ) by norm_num, show 1+(35152842522836767/100000000000000000000 : ℝ)+(7287361033177699/50000000000000000000 : ℝ)=(20009945512917838433/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35152842522836767/100000000000000000000 : ℝ) ≤ ((3426312677159371709/3427500000000000000 : ℝ)+2*(507914138671/274200000000000 : ℝ)*(2807/20000 : ℝ))^(8295/2048 : ℝ) := by
    rw [show (3426312677159371709/3427500000000000000 : ℝ)+2*(507914138671/274200000000000 : ℝ)*(2807/20000 : ℝ)=(10001735436596451/10000000000000000 : ℝ) by norm_num, show 1+2*(35152842522836767/100000000000000000000 : ℝ)=(50035152842522836767/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3426312677159371709/3427500000000000000 : ℝ)*(X 1 0+X 2 0)+(507914138671/274200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8295/2048 : ℝ)) (lo := (11293/100000 : ℝ)) (hi := (2807/20000 : ℝ)) (c := (3426312677159371709/3427500000000000000 : ℝ)) (alpha := (507914138671/274200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3426312677159371709/3427500000000000000 : ℝ)*(X 0 1+X 2 1)+(507914138671/274200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8295/2048 : ℝ)) (lo := (11293/100000 : ℝ)) (hi := (2807/20000 : ℝ)) (c := (3426312677159371709/3427500000000000000 : ℝ)) (alpha := (507914138671/274200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3426312677159371709/3427500000000000000 : ℝ)*(X 0 2+X 1 2)+(507914138671/274200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8295/2048 : ℝ)) (lo := (11293/100000 : ℝ)) (hi := (2807/20000 : ℝ)) (c := (3426312677159371709/3427500000000000000 : ℝ)) (alpha := (507914138671/274200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2185672411/10000000000 : ℝ)*X 0 0+(5393774169/10000000000 : ℝ)*X 0 1+(5265048327/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672449271/5000000000 : ℝ)*X 1 0+(-2250975041/10000000000 : ℝ)*X 1 1+(5265048327/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344898543/10000000000 : ℝ)*X 2 0+(658131041/1250000000 : ℝ)*X 2 1+(-2250975039/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((437019437/1000000000 : ℝ)*X 0 0+(4244980029/10000000000 : ℝ)*X 0 1+(899823837/2000000000 : ℝ)*X 0 2+(437019437/1000000000 : ℝ)*X 1 0+(4244980029/10000000000 : ℝ)*X 1 1+(899823837/2000000000 : ℝ)*X 1 2+(437019437/1000000000 : ℝ)*X 2 0+(4244980029/10000000000 : ℝ)*X 2 1+(899823837/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2185677381/10000000000 : ℝ)*X 0 0+(5265371491/10000000000 : ℝ)*X 0 1+(5393449851/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656190543/5000000000 : ℝ)*X 1 0+(-84902941/400000000 : ℝ)*X 1 1+(5393449839/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312381079/10000000000 : ℝ)*X 2 0+(2696724921/5000000000 : ℝ)*X 2 1+(-212257353/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2185102099/5000000000 : ℝ)*X 0 0+(4498481193/10000000000 : ℝ)*X 0 1+(4245620343/10000000000 : ℝ)*X 0 2+(2185102099/5000000000 : ℝ)*X 1 0+(4498481193/10000000000 : ℝ)*X 1 1+(4245620343/10000000000 : ℝ)*X 1 2+(2185102099/5000000000 : ℝ)*X 2 0+(4498481193/10000000000 : ℝ)*X 2 1+(4245620343/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11098174157288894097241309/5712500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (198189423/50000000000000 : ℝ)*(base19) + (371981797/100000000000000 : ℝ)*(base23) + (6908411/50000000000000 : ℝ)*(lower2) + (48125063/100000000000000 : ℝ)*(upper3) + (32824969/100000000000000 : ℝ)*(upper5) + (585166663363967/10000000000000 : ℝ)*(major0) + (585166663363967/10000000000000 : ℝ)*(major1) + (585166663363967/10000000000000 : ℝ)*(major2) + (7768459089373599/100000000000000 : ℝ)*(sp0) + (7768469561900399/100000000000000 : ℝ)*(sp1) + (971058698287181/12500000000000 : ℝ)*(sp2) + (122964295324367/3125000000000 : ℝ)*(sp3) + (5434452823/50000000000000 : ℝ)*(sp4) + (5793860757/100000000000000 : ℝ)*(sp7) + (7869726488481/200000000000 : ℝ)*(f.failure) + (1553693991655849/20000000000000 : ℝ)*(f.sum) + (341216192929/85687500000000000000000000 : ℝ)*base66 + (400151703713827897/34275000000000000000000000000000 : ℝ)*base68 + (37452550607227897/34275000000000000000000000000000 : ℝ)*base70 + (578191111749577897/34275000000000000000000000000000 : ℝ)*base72 + (5632486782121/1371000000000000000000000000 : ℝ)*base74 + (66617314478077897/34275000000000000000000000000000 : ℝ)*base76 + (619852374455227897/34275000000000000000000000000000 : ℝ)*base78 + (496428962876752897/34275000000000000000000000000000 : ℝ)*base80 + (148952473501/171375000000000000000000000 : ℝ)*base81 + (6751/10000000000000000000 : ℝ)*base89 + (6751/10000000000000000000 : ℝ)*base91 + (6751/10000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (141103558563341147671651029/28562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (869000331/100000000000000 : ℝ)*(base19) + (947654453/100000000000000 : ℝ)*(base23) + (8779969/10000000000000 : ℝ)*(upper3) + (41938139/100000000000000 : ℝ)*(lower4) + (9324869/10000000000000 : ℝ)*(upper5) + (5881231583670231/100000000000000 : ℝ)*(major0) + (5881231583670231/100000000000000 : ℝ)*(major1) + (5881231583670231/100000000000000 : ℝ)*(major2) + (236087879/1000000000000 : ℝ)*(sp1) + (394408753/1562500000000 : ℝ)*(sp2) + (1561543852482471/20000000000000 : ℝ)*(sp4) + (1951923696156031/25000000000000 : ℝ)*(sp5) + (7807693072597711/100000000000000 : ℝ)*(sp6) + (1977371870127911/50000000000000 : ℝ)*(sp7) + (1977371870127911/50000000000000 : ℝ)*(f.failure) + (1561543852482471/20000000000000 : ℝ)*(f.sum) + (2427286718097/4570000000000000000000000000 : ℝ)*base65 + (123595805570280907/114250000000000000000000000000000 : ℝ)*base68 + (1410042599754719093/114250000000000000000000000000000 : ℝ)*base69 + (202265415803530907/114250000000000000000000000000000 : ℝ)*base72 + (3762029464553/4570000000000000000000000000 : ℝ)*base74 + (952744539137030907/114250000000000000000000000000000 : ℝ)*base76 + (1417239898847780907/114250000000000000000000000000000 : ℝ)*base78 + (239799404365530907/114250000000000000000000000000000 : ℝ)*base80 + (18473237067707/4570000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (31144281/2500000000000000000000 : ℝ)*base89 + (31144281/2500000000000000000000 : ℝ)*base91 + (31144281/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1103_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74356671/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2807/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11293/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11301/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14027/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1103_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1103_s8_0 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1092839227/5000000000 : ℝ)*x 0 + (1078738317/2000000000 : ℝ)*x 1 + (2632563519/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092839227/5000000000 : ℝ)^1037 ≤ (1659673431913/12500000000000 : ℝ)^781 := by
    have hnat : (1092839227 : ℕ)^1037*12500000000000^781 ≤ 1659673431913^781*5000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092839227 5000000000 1659673431913 12500000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078738317/2000000000 : ℝ)^1037 ≤ (2202786628379/5000000000000 : ℝ)^781 := by
    have hnat : (1078738317 : ℕ)^1037*5000000000000^781 ≤ 2202786628379^781*2000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078738317 2000000000 2202786628379 5000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632563519/5000000000 : ℝ)^1037 ≤ (21333439982807/50000000000000 : ℝ)^781 := by
    have hnat : (2632563519 : ℕ)^1037*50000000000000^781 ≤ 21333439982807^781*5000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632563519 5000000000 21333439982807 50000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1092839227/5000000000 : ℝ), (1078738317/2000000000 : ℝ), (2632563519/5000000000 : ℝ)] ![(1659673431913/12500000000000 : ℝ), (2202786628379/5000000000000 : ℝ), (21333439982807/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1092839227/5000000000 : ℝ)|^1037 ≤ (1659673431913/12500000000000 : ℝ)^781
        have hw : |(-1092839227/5000000000 : ℝ)|=(1092839227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078738317/2000000000 : ℝ)|^1037 ≤ (2202786628379/5000000000000 : ℝ)^781
        have hw : |(1078738317/2000000000 : ℝ)|=(1078738317/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632563519/5000000000 : ℝ)|^1037 ≤ (21333439982807/50000000000000 : ℝ)^781
        have hw : |(2632563519/5000000000 : ℝ)|=(2632563519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_s8_1 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5344878181/10000000000 : ℝ)*x 0 + (-450179603/2000000000 : ℝ)*x 1 + (526512709/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344878181/10000000000 : ℝ)^1037 ≤ (21763560185533/50000000000000 : ℝ)^781 := by
    have hnat : (5344878181 : ℕ)^1037*50000000000000^781 ≤ 21763560185533^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344878181 10000000000 21763560185533 50000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (450179603/2000000000 : ℝ)^1037 ≤ (13805999093181/100000000000000 : ℝ)^781 := by
    have hnat : (450179603 : ℕ)^1037*100000000000000^781 ≤ 13805999093181^781*2000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450179603 2000000000 13805999093181 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526512709/1000000000 : ℝ)^1037 ≤ (4266688052513/10000000000000 : ℝ)^781 := by
    have hnat : (526512709 : ℕ)^1037*10000000000000^781 ≤ 4266688052513^781*1000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526512709 1000000000 4266688052513 10000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344878181/10000000000 : ℝ), (-450179603/2000000000 : ℝ), (526512709/1000000000 : ℝ)] ![(21763560185533/50000000000000 : ℝ), (13805999093181/100000000000000 : ℝ), (4266688052513/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344878181/10000000000 : ℝ)|^1037 ≤ (21763560185533/50000000000000 : ℝ)^781
        have hw : |(5344878181/10000000000 : ℝ)|=(5344878181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-450179603/2000000000 : ℝ)|^1037 ≤ (13805999093181/100000000000000 : ℝ)^781
        have hw : |(-450179603/2000000000 : ℝ)|=(450179603/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526512709/1000000000 : ℝ)|^1037 ≤ (4266688052513/10000000000000 : ℝ)^781
        have hw : |(526512709/1000000000 : ℝ)|=(526512709/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_s8_2 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1336219541/2500000000 : ℝ)*x 0 + (210605083/400000000 : ℝ)*x 1 + (-1125449029/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336219541/2500000000 : ℝ)^1037 ≤ (43527120187243/100000000000000 : ℝ)^781 := by
    have hnat : (1336219541 : ℕ)^1037*100000000000000^781 ≤ 43527120187243^781*2500000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336219541 2500000000 43527120187243 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210605083/400000000 : ℝ)^1037 ≤ (42666880363731/100000000000000 : ℝ)^781 := by
    have hnat : (210605083 : ℕ)^1037*100000000000000^781 ≤ 42666880363731^781*400000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210605083 400000000 42666880363731 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1125449029/5000000000 : ℝ)^1037 ≤ (110447995547/800000000000 : ℝ)^781 := by
    have hnat : (1125449029 : ℕ)^1037*800000000000^781 ≤ 110447995547^781*5000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125449029 5000000000 110447995547 800000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336219541/2500000000 : ℝ), (210605083/400000000 : ℝ), (-1125449029/5000000000 : ℝ)] ![(43527120187243/100000000000000 : ℝ), (42666880363731/100000000000000 : ℝ), (110447995547/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336219541/2500000000 : ℝ)|^1037 ≤ (43527120187243/100000000000000 : ℝ)^781
        have hw : |(1336219541/2500000000 : ℝ)|=(1336219541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210605083/400000000 : ℝ)|^1037 ≤ (42666880363731/100000000000000 : ℝ)^781
        have hw : |(210605083/400000000 : ℝ)|=(210605083/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1125449029/5000000000 : ℝ)|^1037 ≤ (110447995547/800000000000 : ℝ)^781
        have hw : |(-1125449029/5000000000 : ℝ)|=(1125449029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_s8_3 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (437019851/1000000000 : ℝ)*x 0 + (4245138699/10000000000 : ℝ)*x 1 + (2249479703/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (437019851/1000000000 : ℝ)^1037 ≤ (8329192255961/25000000000000 : ℝ)^781 := by
    have hnat : (437019851 : ℕ)^1037*25000000000000^781 ≤ 8329192255961^781*1000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437019851 1000000000 8329192255961 25000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4245138699/10000000000 : ℝ)^1037 ≤ (32056822023527/100000000000000 : ℝ)^781 := by
    have hnat : (4245138699 : ℕ)^1037*100000000000000^781 ≤ 32056822023527^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4245138699 10000000000 32056822023527 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2249479703/5000000000 : ℝ)^1037 ≤ (34626408931977/100000000000000 : ℝ)^781 := by
    have hnat : (2249479703 : ℕ)^1037*100000000000000^781 ≤ 34626408931977^781*5000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249479703 5000000000 34626408931977 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(437019851/1000000000 : ℝ), (4245138699/10000000000 : ℝ), (2249479703/5000000000 : ℝ)] ![(8329192255961/25000000000000 : ℝ), (32056822023527/100000000000000 : ℝ), (34626408931977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(437019851/1000000000 : ℝ)|^1037 ≤ (8329192255961/25000000000000 : ℝ)^781
        have hw : |(437019851/1000000000 : ℝ)|=(437019851/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4245138699/10000000000 : ℝ)|^1037 ≤ (32056822023527/100000000000000 : ℝ)^781
        have hw : |(4245138699/10000000000 : ℝ)|=(4245138699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2249479703/5000000000 : ℝ)|^1037 ≤ (34626408931977/100000000000000 : ℝ)^781
        have hw : |(2249479703/5000000000 : ℝ)|=(2249479703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_s8_4 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1092841691/5000000000 : ℝ)*x 0 + (5265449513/10000000000 : ℝ)*x 1 + (2696683989/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092841691/5000000000 : ℝ)^1037 ≤ (3319356801047/25000000000000 : ℝ)^781 := by
    have hnat : (1092841691 : ℕ)^1037*25000000000000^781 ≤ 3319356801047^781*5000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092841691 5000000000 3319356801047 25000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265449513/10000000000 : ℝ)^1037 ≤ (10667587452833/25000000000000 : ℝ)^781 := by
    have hnat : (5265449513 : ℕ)^1037*25000000000000^781 ≤ 10667587452833^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265449513 10000000000 10667587452833 25000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696683989/5000000000 : ℝ)^1037 ≤ (11013055741783/25000000000000 : ℝ)^781 := by
    have hnat : (2696683989 : ℕ)^1037*25000000000000^781 ≤ 11013055741783^781*5000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696683989 5000000000 11013055741783 25000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1092841691/5000000000 : ℝ), (5265449513/10000000000 : ℝ), (2696683989/5000000000 : ℝ)] ![(3319356801047/25000000000000 : ℝ), (10667587452833/25000000000000 : ℝ), (11013055741783/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1092841691/5000000000 : ℝ)|^1037 ≤ (3319356801047/25000000000000 : ℝ)^781
        have hw : |(-1092841691/5000000000 : ℝ)|=(1092841691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265449513/10000000000 : ℝ)|^1037 ≤ (10667587452833/25000000000000 : ℝ)^781
        have hw : |(5265449513/10000000000 : ℝ)|=(5265449513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696683989/5000000000 : ℝ)|^1037 ≤ (11013055741783/25000000000000 : ℝ)^781
        have hw : |(2696683989/5000000000 : ℝ)|=(2696683989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_s8_5 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5312401573/10000000000 : ℝ)*x 0 + (-2122656989/10000000000 : ℝ)*x 1 + (5393367971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312401573/10000000000 : ℝ)^1037 ≤ (5397037256561/12500000000000 : ℝ)^781 := by
    have hnat : (5312401573 : ℕ)^1037*12500000000000^781 ≤ 5397037256561^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312401573 10000000000 5397037256561 12500000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2122656989/10000000000 : ℝ)^1037 ≤ (3192869760341/25000000000000 : ℝ)^781 := by
    have hnat : (2122656989 : ℕ)^1037*25000000000000^781 ≤ 3192869760341^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122656989 10000000000 3192869760341 25000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393367971/10000000000 : ℝ)^1037 ≤ (2753263930701/6250000000000 : ℝ)^781 := by
    have hnat : (5393367971 : ℕ)^1037*6250000000000^781 ≤ 2753263930701^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393367971 10000000000 2753263930701 6250000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312401573/10000000000 : ℝ), (-2122656989/10000000000 : ℝ), (5393367971/10000000000 : ℝ)] ![(5397037256561/12500000000000 : ℝ), (3192869760341/25000000000000 : ℝ), (2753263930701/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312401573/10000000000 : ℝ)|^1037 ≤ (5397037256561/12500000000000 : ℝ)^781
        have hw : |(5312401573/10000000000 : ℝ)|=(5312401573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2122656989/10000000000 : ℝ)|^1037 ≤ (3192869760341/25000000000000 : ℝ)^781
        have hw : |(-2122656989/10000000000 : ℝ)|=(2122656989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393367971/10000000000 : ℝ)|^1037 ≤ (2753263930701/6250000000000 : ℝ)^781
        have hw : |(5393367971/10000000000 : ℝ)|=(5393367971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_s8_6 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2656200717/5000000000 : ℝ)*x 0 + (5393368109/10000000000 : ℝ)*x 1 + (-212265699/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656200717/5000000000 : ℝ)^1037 ≤ (43176296552469/100000000000000 : ℝ)^781 := by
    have hnat : (2656200717 : ℕ)^1037*100000000000000^781 ≤ 43176296552469^781*5000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656200717 5000000000 43176296552469 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393368109/10000000000 : ℝ)^1037 ≤ (22026112193923/50000000000000 : ℝ)^781 := by
    have hnat : (5393368109 : ℕ)^1037*50000000000000^781 ≤ 22026112193923^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393368109 10000000000 22026112193923 50000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (212265699/1000000000 : ℝ)^1037 ≤ (12771479049353/100000000000000 : ℝ)^781 := by
    have hnat : (212265699 : ℕ)^1037*100000000000000^781 ≤ 12771479049353^781*1000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212265699 1000000000 12771479049353 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656200717/5000000000 : ℝ), (5393368109/10000000000 : ℝ), (-212265699/1000000000 : ℝ)] ![(43176296552469/100000000000000 : ℝ), (22026112193923/50000000000000 : ℝ), (12771479049353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656200717/5000000000 : ℝ)|^1037 ≤ (43176296552469/100000000000000 : ℝ)^781
        have hw : |(2656200717/5000000000 : ℝ)|=(2656200717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393368109/10000000000 : ℝ)|^1037 ≤ (22026112193923/50000000000000 : ℝ)^781
        have hw : |(5393368109/10000000000 : ℝ)|=(5393368109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-212265699/1000000000 : ℝ)|^1037 ≤ (12771479049353/100000000000000 : ℝ)^781
        have hw : |(-212265699/1000000000 : ℝ)|=(212265699/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_s8_7 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (546276027/1250000000 : ℝ)*x 0 + (1124580739/2500000000 : ℝ)*x 1 + (84915551/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546276027/1250000000 : ℝ)^1037 ≤ (16658433636619/50000000000000 : ℝ)^781 := by
    have hnat : (546276027 : ℕ)^1037*50000000000000^781 ≤ 16658433636619^781*1250000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546276027 1250000000 16658433636619 50000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1124580739/2500000000 : ℝ)^1037 ≤ (34619904980047/100000000000000 : ℝ)^781 := by
    have hnat : (1124580739 : ℕ)^1037*100000000000000^781 ≤ 34619904980047^781*2500000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124580739 2500000000 34619904980047 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84915551/200000000 : ℝ)^1037 ≤ (3206322772351/10000000000000 : ℝ)^781 := by
    have hnat : (84915551 : ℕ)^1037*10000000000000^781 ≤ 3206322772351^781*200000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84915551 200000000 3206322772351 10000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(546276027/1250000000 : ℝ), (1124580739/2500000000 : ℝ), (84915551/200000000 : ℝ)] ![(16658433636619/50000000000000 : ℝ), (34619904980047/100000000000000 : ℝ), (3206322772351/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(546276027/1250000000 : ℝ)|^1037 ≤ (16658433636619/50000000000000 : ℝ)^781
        have hw : |(546276027/1250000000 : ℝ)|=(546276027/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1124580739/2500000000 : ℝ)|^1037 ≤ (34619904980047/100000000000000 : ℝ)^781
        have hw : |(1124580739/2500000000 : ℝ)|=(1124580739/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84915551/200000000 : ℝ)|^1037 ≤ (3206322772351/10000000000000 : ℝ)^781
        have hw : |(84915551/200000000 : ℝ)|=(84915551/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1103_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74356671/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14027/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11301/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5651/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (561/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14027/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11301/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14027/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11301/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14027/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11301/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14027/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11301/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14027/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11301/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14027/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11301/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11301/100000 : ℝ) ^ (8295/2048 : ℝ) ≤ (1827073208296349/12500000000000000000 : ℝ) := by
    have hpowers : (11301/100000 : ℝ)^8295 ≤ (1827073208296349/12500000000000000000 : ℝ)^2048 := by
      have hnat : (11301 : ℕ)^8295*12500000000000000000^2048 ≤ 1827073208296349^2048*100000^8295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11301 100000 1827073208296349 12500000000000000000 8295 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11301/100000 : ℝ)) (X := (1827073208296349/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8295 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14027/100000 : ℝ) ^ (8295/2048 : ℝ) ≤ (17535878166802129/50000000000000000000 : ℝ) := by
    have hpowers : (14027/100000 : ℝ)^8295 ≤ (17535878166802129/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14027 : ℕ)^8295*50000000000000000000^2048 ≤ 17535878166802129^2048*100000^8295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14027 100000 17535878166802129 50000000000000000000 8295 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14027/100000 : ℝ)) (X := (17535878166802129/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8295 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251827073208296349/6250000000000000000 : ℝ) ≤ (2500180418763377/2500000000000000 : ℝ) ^ (8295/2048 : ℝ) := by
    have hpowers : (6251827073208296349/6250000000000000000 : ℝ)^2048 ≤ (2500180418763377/2500000000000000 : ℝ)^8295 := by
      have hnat : (6251827073208296349 : ℕ)^2048*2500000000000000^8295 ≤ 2500180418763377^8295*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251827073208296349 6250000000000000000 2500180418763377 2500000000000000 2048 8295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500180418763377/2500000000000000 : ℝ)) (X := (6251827073208296349/6250000000000000000 : ℝ)) (by norm_num) 8295 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (2000993766839999501/2000000000000000000 : ℝ) ≤ (10001226554431199/10000000000000000 : ℝ) ^ (8295/2048 : ℝ) := by
    have hpowers : (2000993766839999501/2000000000000000000 : ℝ)^2048 ≤ (10001226554431199/10000000000000000 : ℝ)^8295 := by
      have hnat : (2000993766839999501 : ℕ)^2048*10000000000000000^8295 ≤ 10001226554431199^8295*2000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000993766839999501 2000000000000000000 10001226554431199 10000000000000000 2048 8295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001226554431199/10000000000000000 : ℝ)) (X := (2000993766839999501/2000000000000000000 : ℝ)) (by norm_num) 8295 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017535878166802129/25000000000000000000 : ℝ) ≤ (1000173143380889/1000000000000000 : ℝ) ^ (8295/2048 : ℝ) := by
    have hpowers : (25017535878166802129/25000000000000000000 : ℝ)^2048 ≤ (1000173143380889/1000000000000000 : ℝ)^8295 := by
      have hnat : (25017535878166802129 : ℕ)^2048*1000000000000000^8295 ≤ 1000173143380889^8295*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017535878166802129 25000000000000000000 1000173143380889 1000000000000000 2048 8295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000173143380889/1000000000000000 : ℝ)) (X := (25017535878166802129/25000000000000000000 : ℝ)) (by norm_num) 8295 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1827073208296349/12500000000000000000 : ℝ) ≤ ((13625278001250645413/13630000000000000000 : ℝ)+2*(504879377691/272600000000000 : ℝ)*(11301/100000 : ℝ))^(8295/2048 : ℝ) := by
    rw [show (13625278001250645413/13630000000000000000 : ℝ)+2*(504879377691/272600000000000 : ℝ)*(11301/100000 : ℝ)=(2500180418763377/2500000000000000 : ℝ) by norm_num, show 1+2*(1827073208296349/12500000000000000000 : ℝ)=(6251827073208296349/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17535878166802129/50000000000000000000 : ℝ)+(1827073208296349/12500000000000000000 : ℝ) ≤ ((13625278001250645413/13630000000000000000 : ℝ)+(504879377691/272600000000000 : ℝ)*((14027/100000 : ℝ)+(11301/100000 : ℝ)))^(8295/2048 : ℝ) := by
    rw [show (13625278001250645413/13630000000000000000 : ℝ)+(504879377691/272600000000000 : ℝ)*((14027/100000 : ℝ)+(11301/100000 : ℝ))=(10001226554431199/10000000000000000 : ℝ) by norm_num, show 1+(17535878166802129/50000000000000000000 : ℝ)+(1827073208296349/12500000000000000000 : ℝ)=(2000993766839999501/2000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17535878166802129/50000000000000000000 : ℝ) ≤ ((13625278001250645413/13630000000000000000 : ℝ)+2*(504879377691/272600000000000 : ℝ)*(14027/100000 : ℝ))^(8295/2048 : ℝ) := by
    rw [show (13625278001250645413/13630000000000000000 : ℝ)+2*(504879377691/272600000000000 : ℝ)*(14027/100000 : ℝ)=(1000173143380889/1000000000000000 : ℝ) by norm_num, show 1+2*(17535878166802129/50000000000000000000 : ℝ)=(25017535878166802129/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13625278001250645413/13630000000000000000 : ℝ)*(X 1 0+X 2 0)+(504879377691/272600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8295/2048 : ℝ)) (lo := (11301/100000 : ℝ)) (hi := (14027/100000 : ℝ)) (c := (13625278001250645413/13630000000000000000 : ℝ)) (alpha := (504879377691/272600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13625278001250645413/13630000000000000000 : ℝ)*(X 0 1+X 2 1)+(504879377691/272600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8295/2048 : ℝ)) (lo := (11301/100000 : ℝ)) (hi := (14027/100000 : ℝ)) (c := (13625278001250645413/13630000000000000000 : ℝ)) (alpha := (504879377691/272600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13625278001250645413/13630000000000000000 : ℝ)*(X 0 2+X 1 2)+(504879377691/272600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8295/2048 : ℝ)) (lo := (11301/100000 : ℝ)) (hi := (14027/100000 : ℝ)) (c := (13625278001250645413/13630000000000000000 : ℝ)) (alpha := (504879377691/272600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1092839227/5000000000 : ℝ)*X 0 0+(1078738317/2000000000 : ℝ)*X 0 1+(2632563519/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344878181/10000000000 : ℝ)*X 1 0+(-450179603/2000000000 : ℝ)*X 1 1+(526512709/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336219541/2500000000 : ℝ)*X 2 0+(210605083/400000000 : ℝ)*X 2 1+(-1125449029/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((437019851/1000000000 : ℝ)*X 0 0+(4245138699/10000000000 : ℝ)*X 0 1+(2249479703/5000000000 : ℝ)*X 0 2+(437019851/1000000000 : ℝ)*X 1 0+(4245138699/10000000000 : ℝ)*X 1 1+(2249479703/5000000000 : ℝ)*X 1 2+(437019851/1000000000 : ℝ)*X 2 0+(4245138699/10000000000 : ℝ)*X 2 1+(2249479703/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1092841691/5000000000 : ℝ)*X 0 0+(5265449513/10000000000 : ℝ)*X 0 1+(2696683989/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312401573/10000000000 : ℝ)*X 1 0+(-2122656989/10000000000 : ℝ)*X 1 1+(5393367971/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656200717/5000000000 : ℝ)*X 2 0+(5393368109/10000000000 : ℝ)*X 2 1+(-212265699/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((546276027/1250000000 : ℝ)*X 0 0+(1124580739/2500000000 : ℝ)*X 0 1+(84915551/200000000 : ℝ)*X 0 2+(546276027/1250000000 : ℝ)*X 1 0+(1124580739/2500000000 : ℝ)*X 1 1+(84915551/200000000 : ℝ)*X 1 2+(546276027/1250000000 : ℝ)*X 2 0+(1124580739/2500000000 : ℝ)*X 2 1+(84915551/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (55364072918746704628925469/6815000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1658428859/100000000000000 : ℝ)*(base19) + (777866041/50000000000000 : ℝ)*(base23) + (2604193/6250000000000 : ℝ)*(lower2) + (126265097/50000000000000 : ℝ)*(upper3) + (61042943/50000000000000 : ℝ)*(upper5) + (117181256997429/2000000000000 : ℝ)*(major0) + (117181256997429/2000000000000 : ℝ)*(major1) + (117181256997429/2000000000000 : ℝ)*(major2) + (7778244018693533/100000000000000 : ℝ)*(sp0) + (1944571763602011/25000000000000 : ℝ)*(sp1) + (388914357855241/5000000000000 : ℝ)*(sp2) + (1969905640414717/50000000000000 : ℝ)*(sp3) + (44694143369/100000000000000 : ℝ)*(sp4) + (3179410173/12500000000000 : ℝ)*(sp7) + (1969918358055409/50000000000000 : ℝ)*(f.failure) + (7778288712836903/100000000000000 : ℝ)*(f.sum) + (2972679307323/1363000000000000000000000000 : ℝ)*base65 + (40201408199126823/27260000000000000000000000000000 : ℝ)*base68 + (124149078153193177/27260000000000000000000000000000 : ℝ)*base69 + (261470954473113177/27260000000000000000000000000000 : ℝ)*base71 + (445466522767/272600000000000000000000000 : ℝ)*base74 + (183068056410953177/27260000000000000000000000000000 : ℝ)*base75 + (380579094286953177/27260000000000000000000000000000 : ℝ)*base77 + (531781431393177/27260000000000000000000000000000 : ℝ)*base79 + (4458510503177/1363000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (3216561/2500000000000000000000 : ℝ)*base90 + (3216561/2500000000000000000000 : ℝ)*base92 + (3216561/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27120813209693845304559/13630000000000000000000000000 : ℝ) := by norm_num
    linear_combination (629617459/100000000000000 : ℝ)*(base19) + (45624609/10000000000000 : ℝ)*(base23) + (29032243/12500000000000 : ℝ)*(lower1) + (6147963/50000000000000 : ℝ)*(upper2) + (26155717/50000000000000 : ℝ)*(upper3) + (5888566207772827/100000000000000 : ℝ)*(major0) + (5888566207772827/100000000000000 : ℝ)*(major1) + (5888566207772827/100000000000000 : ℝ)*(major2) + (656605297/50000000000000 : ℝ)*(sp2) + (271628881/50000000000000 : ℝ)*(sp3) + (122147758652709/1562500000000 : ℝ)*(sp4) + (7817455924155917/100000000000000 : ℝ)*(sp5) + (1954363696079173/25000000000000 : ℝ)*(sp6) + (989918813047059/25000000000000 : ℝ)*(sp7) + (1979837897722999/50000000000000 : ℝ)*(f.failure) + (122147758652709/1562500000000 : ℝ)*(f.sum) + (94663776573137/13630000000000000000000000000 : ℝ)*base65 + (4447629321389557449/1363000000000000000000000000000000 : ℝ)*base68 + (8363285377543557449/1363000000000000000000000000000000 : ℝ)*base70 + (18536545826274557449/1363000000000000000000000000000000 : ℝ)*base72 + (48080806664627/13630000000000000000000000000 : ℝ)*base73 + (23298413156979442551/1363000000000000000000000000000000 : ℝ)*base75 + (6369623636736442551/1363000000000000000000000000000000 : ℝ)*base77 + (5551553909940442551/1363000000000000000000000000000000 : ℝ)*base79 + (26934410330743/13630000000000000000000000000 : ℝ)*base82 + (10776329/2500000000000000000000 : ℝ)*base89 + (10776329/2500000000000000000000 : ℝ)*base91 + (10776329/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1103_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74356671/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14027/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11301/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5651/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (561/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1103_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1103_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74356671/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14073/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11257/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5651/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (561/4000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1103_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1103_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1103_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74356671/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14073/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11257/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5651/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (561/4000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1103_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1628_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:59:15.013027+00:00
-- url     : https://prove2.me/submissions/d31cc195-1e2d-4113-9e7a-f55e56459038

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
theorem support_rectangle_w1628_s3_0 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-829967679/5000000000 : ℝ)*x 0 + (545430753/1000000000 : ℝ)*x 1 + (1036424351/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (829967679/5000000000 : ℝ)^4831 ≤ (10240300607789/100000000000000 : ℝ)^3807 := by
    have hnat : (829967679 : ℕ)^4831*100000000000000^3807 ≤ 10240300607789^3807*5000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      829967679 5000000000 10240300607789 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (545430753/1000000000 : ℝ)^4831 ≤ (46337043314561/100000000000000 : ℝ)^3807 := by
    have hnat : (545430753 : ℕ)^4831*100000000000000^3807 ≤ 46337043314561^3807*1000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545430753 1000000000 46337043314561 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036424351/2000000000 : ℝ)^4831 ≤ (43422656060113/100000000000000 : ℝ)^3807 := by
    have hnat : (1036424351 : ℕ)^4831*100000000000000^3807 ≤ 43422656060113^3807*2000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036424351 2000000000 43422656060113 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-829967679/5000000000 : ℝ), (545430753/1000000000 : ℝ), (1036424351/2000000000 : ℝ)] ![(10240300607789/100000000000000 : ℝ), (46337043314561/100000000000000 : ℝ), (43422656060113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-829967679/5000000000 : ℝ)|^4831 ≤ (10240300607789/100000000000000 : ℝ)^3807
        have hw : |(-829967679/5000000000 : ℝ)|=(829967679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(545430753/1000000000 : ℝ)|^4831 ≤ (46337043314561/100000000000000 : ℝ)^3807
        have hw : |(545430753/1000000000 : ℝ)|=(545430753/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1036424351/2000000000 : ℝ)|^4831 ≤ (43422656060113/100000000000000 : ℝ)^3807
        have hw : |(1036424351/2000000000 : ℝ)|=(1036424351/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_s3_1 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351064297/10000000000 : ℝ)*x 0 + (-1800186511/10000000000 : ℝ)*x 1 + (5182121747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351064297/10000000000 : ℝ)^4831 ≤ (22613433060327/50000000000000 : ℝ)^3807 := by
    have hnat : (5351064297 : ℕ)^4831*50000000000000^3807 ≤ 22613433060327^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351064297 10000000000 22613433060327 50000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1800186511/10000000000 : ℝ)^4831 ≤ (454019115589/4000000000000 : ℝ)^3807 := by
    have hnat : (1800186511 : ℕ)^4831*4000000000000^3807 ≤ 454019115589^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1800186511 10000000000 454019115589 4000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5182121747/10000000000 : ℝ)^4831 ≤ (5427831996881/12500000000000 : ℝ)^3807 := by
    have hnat : (5182121747 : ℕ)^4831*12500000000000^3807 ≤ 5427831996881^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182121747 10000000000 5427831996881 12500000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351064297/10000000000 : ℝ), (-1800186511/10000000000 : ℝ), (5182121747/10000000000 : ℝ)] ![(22613433060327/50000000000000 : ℝ), (454019115589/4000000000000 : ℝ), (5427831996881/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351064297/10000000000 : ℝ)|^4831 ≤ (22613433060327/50000000000000 : ℝ)^3807
        have hw : |(5351064297/10000000000 : ℝ)|=(5351064297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1800186511/10000000000 : ℝ)|^4831 ≤ (454019115589/4000000000000 : ℝ)^3807
        have hw : |(-1800186511/10000000000 : ℝ)|=(1800186511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5182121747/10000000000 : ℝ)|^4831 ≤ (5427831996881/12500000000000 : ℝ)^3807
        have hw : |(5182121747/10000000000 : ℝ)|=(5182121747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_s3_2 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351064299/10000000000 : ℝ)*x 0 + (259106087/500000000 : ℝ)*x 1 + (-1800186517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351064299/10000000000 : ℝ)^4831 ≤ (9045373228421/20000000000000 : ℝ)^3807 := by
    have hnat : (5351064299 : ℕ)^4831*20000000000000^3807 ≤ 9045373228421^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351064299 10000000000 9045373228421 20000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (259106087/500000000 : ℝ)^4831 ≤ (5427831987577/12500000000000 : ℝ)^3807 := by
    have hnat : (259106087 : ℕ)^4831*12500000000000^3807 ≤ 5427831987577^3807*500000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259106087 500000000 5427831987577 12500000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1800186517/10000000000 : ℝ)^4831 ≤ (2837619484433/25000000000000 : ℝ)^3807 := by
    have hnat : (1800186517 : ℕ)^4831*25000000000000^3807 ≤ 2837619484433^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1800186517 10000000000 2837619484433 25000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351064299/10000000000 : ℝ), (259106087/500000000 : ℝ), (-1800186517/10000000000 : ℝ)] ![(9045373228421/20000000000000 : ℝ), (5427831987577/12500000000000 : ℝ), (2837619484433/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351064299/10000000000 : ℝ)|^4831 ≤ (9045373228421/20000000000000 : ℝ)^3807
        have hw : |(5351064299/10000000000 : ℝ)|=(5351064299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(259106087/500000000 : ℝ)|^4831 ≤ (5427831987577/12500000000000 : ℝ)^3807
        have hw : |(259106087/500000000 : ℝ)|=(259106087/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1800186517/10000000000 : ℝ)|^4831 ≤ (2837619484433/25000000000000 : ℝ)^3807
        have hw : |(-1800186517/10000000000 : ℝ)|=(1800186517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_s3_3 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167916131/400000000 : ℝ)*x 0 + (773199507/2000000000 : ℝ)*x 1 + (4550730771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167916131/400000000 : ℝ)^4831 ≤ (16619056858439/50000000000000 : ℝ)^3807 := by
    have hnat : (167916131 : ℕ)^4831*50000000000000^3807 ≤ 16619056858439^3807*400000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167916131 400000000 16619056858439 50000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (773199507/2000000000 : ℝ)^4831 ≤ (7484864506929/25000000000000 : ℝ)^3807 := by
    have hnat : (773199507 : ℕ)^4831*25000000000000^3807 ≤ 7484864506929^3807*2000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      773199507 2000000000 7484864506929 25000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4550730771/10000000000 : ℝ)^4831 ≤ (9205607061083/25000000000000 : ℝ)^3807 := by
    have hnat : (4550730771 : ℕ)^4831*25000000000000^3807 ≤ 9205607061083^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4550730771 10000000000 9205607061083 25000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167916131/400000000 : ℝ), (773199507/2000000000 : ℝ), (4550730771/10000000000 : ℝ)] ![(16619056858439/50000000000000 : ℝ), (7484864506929/25000000000000 : ℝ), (9205607061083/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167916131/400000000 : ℝ)|^4831 ≤ (16619056858439/50000000000000 : ℝ)^3807
        have hw : |(167916131/400000000 : ℝ)|=(167916131/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(773199507/2000000000 : ℝ)|^4831 ≤ (7484864506929/25000000000000 : ℝ)^3807
        have hw : |(773199507/2000000000 : ℝ)|=(773199507/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4550730771/10000000000 : ℝ)|^4831 ≤ (9205607061083/25000000000000 : ℝ)^3807
        have hw : |(4550730771/10000000000 : ℝ)|=(4550730771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_s3_4 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-830001683/5000000000 : ℝ)*x 0 + (1036833019/2000000000 : ℝ)*x 1 + (1090448507/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (830001683/5000000000 : ℝ)^4831 ≤ (5120416503919/50000000000000 : ℝ)^3807 := by
    have hnat : (830001683 : ℕ)^4831*50000000000000^3807 ≤ 5120416503919^3807*5000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      830001683 5000000000 5120416503919 50000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036833019/2000000000 : ℝ)^4831 ≤ (43444384402557/100000000000000 : ℝ)^3807 := by
    have hnat : (1036833019 : ℕ)^4831*100000000000000^3807 ≤ 43444384402557^3807*2000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036833019 2000000000 43444384402557 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1090448507/2000000000 : ℝ)^4831 ≤ (11578695641721/25000000000000 : ℝ)^3807 := by
    have hnat : (1090448507 : ℕ)^4831*25000000000000^3807 ≤ 11578695641721^3807*2000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090448507 2000000000 11578695641721 25000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-830001683/5000000000 : ℝ), (1036833019/2000000000 : ℝ), (1090448507/2000000000 : ℝ)] ![(5120416503919/50000000000000 : ℝ), (43444384402557/100000000000000 : ℝ), (11578695641721/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-830001683/5000000000 : ℝ)|^4831 ≤ (5120416503919/50000000000000 : ℝ)^3807
        have hw : |(-830001683/5000000000 : ℝ)|=(830001683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036833019/2000000000 : ℝ)|^4831 ≤ (43444384402557/100000000000000 : ℝ)^3807
        have hw : |(1036833019/2000000000 : ℝ)|=(1036833019/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1090448507/2000000000 : ℝ)|^4831 ≤ (11578695641721/25000000000000 : ℝ)^3807
        have hw : |(1090448507/2000000000 : ℝ)|=(1090448507/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_s3_5 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319640677/2500000000 : ℝ)*x 0 + (-1530065549/10000000000 : ℝ)*x 1 + (2726121383/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319640677/2500000000 : ℝ)^4831 ≤ (11112671154653/25000000000000 : ℝ)^3807 := by
    have hnat : (1319640677 : ℕ)^4831*25000000000000^3807 ≤ 11112671154653^3807*2500000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319640677 2500000000 11112671154653 25000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1530065549/10000000000 : ℝ)^4831 ≤ (9234530317409/100000000000000 : ℝ)^3807 := by
    have hnat : (1530065549 : ℕ)^4831*100000000000000^3807 ≤ 9234530317409^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1530065549 10000000000 9234530317409 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2726121383/5000000000 : ℝ)^4831 ≤ (46314785056949/100000000000000 : ℝ)^3807 := by
    have hnat : (2726121383 : ℕ)^4831*100000000000000^3807 ≤ 46314785056949^3807*5000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2726121383 5000000000 46314785056949 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319640677/2500000000 : ℝ), (-1530065549/10000000000 : ℝ), (2726121383/5000000000 : ℝ)] ![(11112671154653/25000000000000 : ℝ), (9234530317409/100000000000000 : ℝ), (46314785056949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319640677/2500000000 : ℝ)|^4831 ≤ (11112671154653/25000000000000 : ℝ)^3807
        have hw : |(1319640677/2500000000 : ℝ)|=(1319640677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1530065549/10000000000 : ℝ)|^4831 ≤ (9234530317409/100000000000000 : ℝ)^3807
        have hw : |(-1530065549/10000000000 : ℝ)|=(1530065549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2726121383/5000000000 : ℝ)|^4831 ≤ (46314785056949/100000000000000 : ℝ)^3807
        have hw : |(2726121383/5000000000 : ℝ)|=(2726121383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_s3_6 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (659820327/1250000000 : ℝ)*x 0 + (681530337/1250000000 : ℝ)*x 1 + (-765032887/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (659820327/1250000000 : ℝ)^4831 ≤ (5556335454437/12500000000000 : ℝ)^3807 := by
    have hnat : (659820327 : ℕ)^4831*12500000000000^3807 ≤ 5556335454437^3807*1250000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659820327 1250000000 5556335454437 12500000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (681530337/1250000000 : ℝ)^4831 ≤ (46314784302383/100000000000000 : ℝ)^3807 := by
    have hnat : (681530337 : ℕ)^4831*100000000000000^3807 ≤ 46314784302383^3807*1250000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681530337 1250000000 46314784302383 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (765032887/5000000000 : ℝ)^4831 ≤ (1154316505079/12500000000000 : ℝ)^3807 := by
    have hnat : (765032887 : ℕ)^4831*12500000000000^3807 ≤ 1154316505079^3807*5000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      765032887 5000000000 1154316505079 12500000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(659820327/1250000000 : ℝ), (681530337/1250000000 : ℝ), (-765032887/5000000000 : ℝ)] ![(5556335454437/12500000000000 : ℝ), (46314784302383/100000000000000 : ℝ), (1154316505079/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(659820327/1250000000 : ℝ)|^4831 ≤ (5556335454437/12500000000000 : ℝ)^3807
        have hw : |(659820327/1250000000 : ℝ)|=(659820327/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(681530337/1250000000 : ℝ)|^4831 ≤ (46314784302383/100000000000000 : ℝ)^3807
        have hw : |(681530337/1250000000 : ℝ)|=(681530337/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-765032887/5000000000 : ℝ)|^4831 ≤ (1154316505079/12500000000000 : ℝ)^3807
        have hw : |(-765032887/5000000000 : ℝ)|=(765032887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_s3_7 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (83961481/200000000 : ℝ)*x 0 + (1136397527/2500000000 : ℝ)*x 1 + (1935596169/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83961481/200000000 : ℝ)^4831 ≤ (33239829588423/100000000000000 : ℝ)^3807 := by
    have hnat : (83961481 : ℕ)^4831*100000000000000^3807 ≤ 33239829588423^3807*200000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83961481 200000000 33239829588423 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1136397527/2500000000 : ℝ)^4831 ≤ (1149051624649/3125000000000 : ℝ)^3807 := by
    have hnat : (1136397527 : ℕ)^4831*3125000000000^3807 ≤ 1149051624649^3807*2500000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136397527 2500000000 1149051624649 3125000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1935596169/5000000000 : ℝ)^4831 ≤ (5998103681853/20000000000000 : ℝ)^3807 := by
    have hnat : (1935596169 : ℕ)^4831*20000000000000^3807 ≤ 5998103681853^3807*5000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1935596169 5000000000 5998103681853 20000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83961481/200000000 : ℝ), (1136397527/2500000000 : ℝ), (1935596169/5000000000 : ℝ)] ![(33239829588423/100000000000000 : ℝ), (1149051624649/3125000000000 : ℝ), (5998103681853/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83961481/200000000 : ℝ)|^4831 ≤ (33239829588423/100000000000000 : ℝ)^3807
        have hw : |(83961481/200000000 : ℝ)|=(83961481/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1136397527/2500000000 : ℝ)|^4831 ≤ (1149051624649/3125000000000 : ℝ)^3807
        have hw : |(1136397527/2500000000 : ℝ)|=(1136397527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1935596169/5000000000 : ℝ)|^4831 ≤ (5998103681853/20000000000000 : ℝ)^3807
        have hw : |(1935596169/5000000000 : ℝ)|=(1935596169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1628_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175784159/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8211/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10447/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (527/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8159/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8211/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10447/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8211/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10447/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8211/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10447/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8211/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10447/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8211/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10447/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8211/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10447/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10447/100000 : ℝ) ^ (4827/1024 : ℝ) ≤ (474992402654977/20000000000000000000 : ℝ) := by
    have hpowers : (10447/100000 : ℝ)^4827 ≤ (474992402654977/20000000000000000000 : ℝ)^1024 := by
      have hnat : (10447 : ℕ)^4827*20000000000000000000^1024 ≤ 474992402654977^1024*100000^4827 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10447 100000 474992402654977 20000000000000000000 4827 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10447/100000 : ℝ)) (X := (474992402654977/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4827 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8211/50000 : ℝ) ^ (4827/1024 : ℝ) ≤ (20027308629070887/100000000000000000000 : ℝ) := by
    have hpowers : (8211/50000 : ℝ)^4827 ≤ (20027308629070887/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8211 : ℕ)^4827*100000000000000000000^1024 ≤ 20027308629070887^1024*50000^4827 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8211 50000 20027308629070887 100000000000000000000 4827 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8211/50000 : ℝ)) (X := (20027308629070887/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4827 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000474992402654977/10000000000000000000 : ℝ) ≤ (1250012595378069/1250000000000000 : ℝ) ^ (4827/1024 : ℝ) := by
    have hpowers : (10000474992402654977/10000000000000000000 : ℝ)^1024 ≤ (1250012595378069/1250000000000000 : ℝ)^4827 := by
      have hnat : (10000474992402654977 : ℕ)^1024*1250000000000000^4827 ≤ 1250012595378069^4827*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000474992402654977 10000000000000000000 1250012595378069 1250000000000000 1024 4827 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250012595378069/1250000000000000 : ℝ)) (X := (10000474992402654977/10000000000000000000 : ℝ)) (by norm_num) 4827 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25005600567660586443/25000000000000000000 : ℝ) ≤ (2000095039987473/2000000000000000 : ℝ) ^ (4827/1024 : ℝ) := by
    have hpowers : (25005600567660586443/25000000000000000000 : ℝ)^1024 ≤ (2000095039987473/2000000000000000 : ℝ)^4827 := by
      have hnat : (25005600567660586443 : ℕ)^1024*2000000000000000^4827 ≤ 2000095039987473^4827*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005600567660586443 25000000000000000000 2000095039987473 2000000000000000 1024 4827 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000095039987473/2000000000000000 : ℝ)) (X := (25005600567660586443/25000000000000000000 : ℝ)) (by norm_num) 4827 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50020027308629070887/50000000000000000000 : ℝ) ≤ (5000424818425089/5000000000000000 : ℝ) ^ (4827/1024 : ℝ) := by
    have hpowers : (50020027308629070887/50000000000000000000 : ℝ)^1024 ≤ (5000424818425089/5000000000000000 : ℝ)^4827 := by
      have hnat : (50020027308629070887 : ℕ)^1024*5000000000000000^4827 ≤ 5000424818425089^4827*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020027308629070887 50000000000000000000 5000424818425089 5000000000000000 1024 4827 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000424818425089/5000000000000000 : ℝ)) (X := (50020027308629070887/50000000000000000000 : ℝ)) (by norm_num) 4827 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(474992402654977/20000000000000000000 : ℝ) ≤ ((29871389287107691689/29875000000000000000 : ℝ)+2*(374436912813/597500000000000 : ℝ)*(10447/100000 : ℝ))^(4827/1024 : ℝ) := by
    rw [show (29871389287107691689/29875000000000000000 : ℝ)+2*(374436912813/597500000000000 : ℝ)*(10447/100000 : ℝ)=(1250012595378069/1250000000000000 : ℝ) by norm_num, show 1+2*(474992402654977/20000000000000000000 : ℝ)=(10000474992402654977/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(20027308629070887/100000000000000000000 : ℝ)+(474992402654977/20000000000000000000 : ℝ) ≤ ((29871389287107691689/29875000000000000000 : ℝ)+(374436912813/597500000000000 : ℝ)*((8211/50000 : ℝ)+(10447/100000 : ℝ)))^(4827/1024 : ℝ) := by
    rw [show (29871389287107691689/29875000000000000000 : ℝ)+(374436912813/597500000000000 : ℝ)*((8211/50000 : ℝ)+(10447/100000 : ℝ))=(2000095039987473/2000000000000000 : ℝ) by norm_num, show 1+(20027308629070887/100000000000000000000 : ℝ)+(474992402654977/20000000000000000000 : ℝ)=(25005600567660586443/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(20027308629070887/100000000000000000000 : ℝ) ≤ ((29871389287107691689/29875000000000000000 : ℝ)+2*(374436912813/597500000000000 : ℝ)*(8211/50000 : ℝ))^(4827/1024 : ℝ) := by
    rw [show (29871389287107691689/29875000000000000000 : ℝ)+2*(374436912813/597500000000000 : ℝ)*(8211/50000 : ℝ)=(5000424818425089/5000000000000000 : ℝ) by norm_num, show 1+2*(20027308629070887/100000000000000000000 : ℝ)=(50020027308629070887/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (29871389287107691689/29875000000000000000 : ℝ)*(X 1 0+X 2 0)+(374436912813/597500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4827/1024 : ℝ)) (lo := (10447/100000 : ℝ)) (hi := (8211/50000 : ℝ)) (c := (29871389287107691689/29875000000000000000 : ℝ)) (alpha := (374436912813/597500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (29871389287107691689/29875000000000000000 : ℝ)*(X 0 1+X 2 1)+(374436912813/597500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4827/1024 : ℝ)) (lo := (10447/100000 : ℝ)) (hi := (8211/50000 : ℝ)) (c := (29871389287107691689/29875000000000000000 : ℝ)) (alpha := (374436912813/597500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (29871389287107691689/29875000000000000000 : ℝ)*(X 0 2+X 1 2)+(374436912813/597500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4827/1024 : ℝ)) (lo := (10447/100000 : ℝ)) (hi := (8211/50000 : ℝ)) (c := (29871389287107691689/29875000000000000000 : ℝ)) (alpha := (374436912813/597500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-829967679/5000000000 : ℝ)*X 0 0+(545430753/1000000000 : ℝ)*X 0 1+(1036424351/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351064297/10000000000 : ℝ)*X 1 0+(-1800186511/10000000000 : ℝ)*X 1 1+(5182121747/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351064299/10000000000 : ℝ)*X 2 0+(259106087/500000000 : ℝ)*X 2 1+(-1800186517/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((167916131/400000000 : ℝ)*X 0 0+(773199507/2000000000 : ℝ)*X 0 1+(4550730771/10000000000 : ℝ)*X 0 2+(167916131/400000000 : ℝ)*X 1 0+(773199507/2000000000 : ℝ)*X 1 1+(4550730771/10000000000 : ℝ)*X 1 2+(167916131/400000000 : ℝ)*X 2 0+(773199507/2000000000 : ℝ)*X 2 1+(4550730771/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-830001683/5000000000 : ℝ)*X 0 0+(1036833019/2000000000 : ℝ)*X 0 1+(1090448507/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1319640677/2500000000 : ℝ)*X 1 0+(-1530065549/10000000000 : ℝ)*X 1 1+(2726121383/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((659820327/1250000000 : ℝ)*X 2 0+(681530337/1250000000 : ℝ)*X 2 1+(-765032887/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((83961481/200000000 : ℝ)*X 0 0+(1136397527/2500000000 : ℝ)*X 0 1+(1935596169/5000000000 : ℝ)*X 0 2+(83961481/200000000 : ℝ)*X 1 0+(1136397527/2500000000 : ℝ)*X 1 1+(1935596169/5000000000 : ℝ)*X 1 2+(83961481/200000000 : ℝ)*X 2 0+(1136397527/2500000000 : ℝ)*X 2 1+(1935596169/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4447895465268759493694375439/373437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1927159403/100000000000000 : ℝ)*(base19) + (452033717/25000000000000 : ℝ)*(base23) + (12885119/20000000000000 : ℝ)*(lower2) + (11757837/4000000000000 : ℝ)*(upper3) + (202035521/100000000000000 : ℝ)*(upper5) + (641806403502361/25000000000000 : ℝ)*(major0) + (641806403502361/25000000000000 : ℝ)*(major1) + (641806403502361/25000000000000 : ℝ)*(major2) + (73479709814439/2000000000000 : ℝ)*(sp0) + (1837003472788657/50000000000000 : ℝ)*(sp1) + (3674007064601849/100000000000000 : ℝ)*(sp2) + (730215891002547/50000000000000 : ℝ)*(sp3) + (11691007383/50000000000000 : ℝ)*(sp4) + (10176254321/100000000000000 : ℝ)*(sp7) + (292088391651883/20000000000000 : ℝ)*(f.failure) + (918502218184179/25000000000000 : ℝ)*(f.sum) + (1109837880717/1867187500000000000000000000 : ℝ)*base65 + (14260314316558727729/746875000000000000000000000000000 : ℝ)*base67 + (5939112706696227729/746875000000000000000000000000000 : ℝ)*base69 + (6184776978214977729/746875000000000000000000000000000 : ℝ)*base71 + (28081335637243/7468750000000000000000000000 : ℝ)*base73 + (9363569312877477729/746875000000000000000000000000000 : ℝ)*base75 + (3320712566568102729/746875000000000000000000000000000 : ℝ)*base77 + (477467389652477729/746875000000000000000000000000000 : ℝ)*base79 + (149833205809153/29875000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (6078603/2000000000000000000000 : ℝ)*base90 + (6078603/2000000000000000000000 : ℝ)*base92 + (6078603/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8213844875683512546668605653/746875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1734033169/100000000000000 : ℝ)*(base19) + (330103467/20000000000000 : ℝ)*(base23) + (64162589/25000000000000 : ℝ)*(upper3) + (1642113/12500000000000 : ℝ)*(lower4) + (53360909/20000000000000 : ℝ)*(upper5) + (2606534733185159/100000000000000 : ℝ)*(major0) + (2606534733185159/100000000000000 : ℝ)*(major1) + (2606534733185159/100000000000000 : ℝ)*(major2) + (5720722471/25000000000000 : ℝ)*(sp1) + (3944784291/20000000000000 : ℝ)*(sp2) + (233141561903959/6250000000000 : ℝ)*(sp4) + (932560093385073/25000000000000 : ℝ)*(sp5) + (746048723204911/20000000000000 : ℝ)*(sp6) + (370701027329937/25000000000000 : ℝ)*(sp7) + (370701027329937/25000000000000 : ℝ)*(f.failure) + (233141561903959/6250000000000 : ℝ)*(f.sum) + (64883029099267/29875000000000000000000000000 : ℝ)*base65 + (20457327076964206449/2987500000000000000000000000000000 : ℝ)*base68 + (15876058190535793551/2987500000000000000000000000000000 : ℝ)*base69 + (4433605596714206449/2987500000000000000000000000000000 : ℝ)*base72 + (84443401798733/29875000000000000000000000000 : ℝ)*base74 + (24258309524714206449/2987500000000000000000000000000000 : ℝ)*base76 + (13247234411701706449/2987500000000000000000000000000000 : ℝ)*base78 + (28587970548214206449/2987500000000000000000000000000000 : ℝ)*base80 + (42137975737321/14937500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (16067983/2500000000000000000000 : ℝ)*base89 + (16067983/2500000000000000000000 : ℝ)*base91 + (16067983/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1628_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175784159/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8211/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10447/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (527/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8159/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1628_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1628_s4_0 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1660011547/10000000000 : ℝ)*x 0 + (27269631/50000000 : ℝ)*x 1 + (5182452273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1660011547/10000000000 : ℝ)^4831 ≤ (5120448526561/50000000000000 : ℝ)^3807 := by
    have hnat : (1660011547 : ℕ)^4831*50000000000000^3807 ≤ 5120448526561^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1660011547 10000000000 5120448526561 50000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27269631/50000000 : ℝ)^4831 ≤ (46332932387719/100000000000000 : ℝ)^3807 := by
    have hnat : (27269631 : ℕ)^4831*100000000000000^3807 ≤ 46332932387719^3807*50000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27269631 50000000 46332932387719 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5182452273/10000000000 : ℝ)^4831 ≤ (43426170545761/100000000000000 : ℝ)^3807 := by
    have hnat : (5182452273 : ℕ)^4831*100000000000000^3807 ≤ 43426170545761^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182452273 10000000000 43426170545761 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1660011547/10000000000 : ℝ), (27269631/50000000 : ℝ), (5182452273/10000000000 : ℝ)] ![(5120448526561/50000000000000 : ℝ), (46332932387719/100000000000000 : ℝ), (43426170545761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1660011547/10000000000 : ℝ)|^4831 ≤ (5120448526561/50000000000000 : ℝ)^3807
        have hw : |(-1660011547/10000000000 : ℝ)|=(1660011547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(27269631/50000000 : ℝ)|^4831 ≤ (46332932387719/100000000000000 : ℝ)^3807
        have hw : |(27269631/50000000 : ℝ)|=(27269631/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5182452273/10000000000 : ℝ)|^4831 ≤ (43426170545761/100000000000000 : ℝ)^3807
        have hw : |(5182452273/10000000000 : ℝ)|=(5182452273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_s4_1 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350961483/10000000000 : ℝ)*x 0 + (-224985633/1250000000 : ℝ)*x 1 + (5182452273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350961483/10000000000 : ℝ)^4831 ≤ (22612881704937/50000000000000 : ℝ)^3807 := by
    have hnat : (5350961483 : ℕ)^4831*50000000000000^3807 ≤ 22612881704937^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350961483 10000000000 22612881704937 50000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (224985633/1250000000 : ℝ)^4831 ≤ (1134806603031/10000000000000 : ℝ)^3807 := by
    have hnat : (224985633 : ℕ)^4831*10000000000000^3807 ≤ 1134806603031^3807*1250000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224985633 1250000000 1134806603031 10000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5182452273/10000000000 : ℝ)^4831 ≤ (43426170545761/100000000000000 : ℝ)^3807 := by
    have hnat : (5182452273 : ℕ)^4831*100000000000000^3807 ≤ 43426170545761^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182452273 10000000000 43426170545761 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350961483/10000000000 : ℝ), (-224985633/1250000000 : ℝ), (5182452273/10000000000 : ℝ)] ![(22612881704937/50000000000000 : ℝ), (1134806603031/10000000000000 : ℝ), (43426170545761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350961483/10000000000 : ℝ)|^4831 ≤ (22612881704937/50000000000000 : ℝ)^3807
        have hw : |(5350961483/10000000000 : ℝ)|=(5350961483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-224985633/1250000000 : ℝ)|^4831 ≤ (1134806603031/10000000000000 : ℝ)^3807
        have hw : |(-224985633/1250000000 : ℝ)|=(224985633/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5182452273/10000000000 : ℝ)|^4831 ≤ (43426170545761/100000000000000 : ℝ)^3807
        have hw : |(5182452273/10000000000 : ℝ)|=(5182452273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_s4_2 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350961483/10000000000 : ℝ)*x 0 + (5182452273/10000000000 : ℝ)*x 1 + (-359977013/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350961483/10000000000 : ℝ)^4831 ≤ (22612881704937/50000000000000 : ℝ)^3807 := by
    have hnat : (5350961483 : ℕ)^4831*50000000000000^3807 ≤ 22612881704937^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350961483 10000000000 22612881704937 50000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5182452273/10000000000 : ℝ)^4831 ≤ (43426170545761/100000000000000 : ℝ)^3807 := by
    have hnat : (5182452273 : ℕ)^4831*100000000000000^3807 ≤ 43426170545761^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182452273 10000000000 43426170545761 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (359977013/2000000000 : ℝ)^4831 ≤ (11348066038311/100000000000000 : ℝ)^3807 := by
    have hnat : (359977013 : ℕ)^4831*100000000000000^3807 ≤ 11348066038311^3807*2000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      359977013 2000000000 11348066038311 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350961483/10000000000 : ℝ), (5182452273/10000000000 : ℝ), (-359977013/2000000000 : ℝ)] ![(22612881704937/50000000000000 : ℝ), (43426170545761/100000000000000 : ℝ), (11348066038311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350961483/10000000000 : ℝ)|^4831 ≤ (22612881704937/50000000000000 : ℝ)^3807
        have hw : |(5350961483/10000000000 : ℝ)|=(5350961483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5182452273/10000000000 : ℝ)|^4831 ≤ (43426170545761/100000000000000 : ℝ)^3807
        have hw : |(5182452273/10000000000 : ℝ)|=(5182452273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-359977013/2000000000 : ℝ)|^4831 ≤ (11348066038311/100000000000000 : ℝ)^3807
        have hw : |(-359977013/2000000000 : ℝ)|=(359977013/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_s4_3 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (104948819/250000000 : ℝ)*x 0 + (3866887823/10000000000 : ℝ)*x 1 + (568728777/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (104948819/250000000 : ℝ)^4831 ≤ (33238610918303/100000000000000 : ℝ)^3807 := by
    have hnat : (104948819 : ℕ)^4831*100000000000000^3807 ≤ 33238610918303^3807*250000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104948819 250000000 33238610918303 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3866887823/10000000000 : ℝ)^4831 ≤ (5989641494487/20000000000000 : ℝ)^3807 := by
    have hnat : (3866887823 : ℕ)^4831*20000000000000^3807 ≤ 5989641494487^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3866887823 10000000000 5989641494487 20000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (568728777/1250000000 : ℝ)^4831 ≤ (2300823850037/6250000000000 : ℝ)^3807 := by
    have hnat : (568728777 : ℕ)^4831*6250000000000^3807 ≤ 2300823850037^3807*1250000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      568728777 1250000000 2300823850037 6250000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(104948819/250000000 : ℝ), (3866887823/10000000000 : ℝ), (568728777/1250000000 : ℝ)] ![(33238610918303/100000000000000 : ℝ), (5989641494487/20000000000000 : ℝ), (2300823850037/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(104948819/250000000 : ℝ)|^4831 ≤ (33238610918303/100000000000000 : ℝ)^3807
        have hw : |(104948819/250000000 : ℝ)|=(104948819/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3866887823/10000000000 : ℝ)|^4831 ≤ (5989641494487/20000000000000 : ℝ)^3807
        have hw : |(3866887823/10000000000 : ℝ)|=(3866887823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(568728777/1250000000 : ℝ)|^4831 ≤ (2300823850037/6250000000000 : ℝ)^3807
        have hw : |(568728777/1250000000 : ℝ)|=(568728777/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_s4_4 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1660079057/10000000000 : ℝ)*x 0 + (5184485063/10000000000 : ℝ)*x 1 + (5451871901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1660079057/10000000000 : ℝ)^4831 ≤ (2048285112217/20000000000000 : ℝ)^3807 := by
    have hnat : (1660079057 : ℕ)^4831*20000000000000^3807 ≤ 2048285112217^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1660079057 10000000000 2048285112217 20000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184485063/10000000000 : ℝ)^4831 ≤ (21723893533553/50000000000000 : ℝ)^3807 := by
    have hnat : (5184485063 : ℕ)^4831*50000000000000^3807 ≤ 21723893533553^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184485063 10000000000 21723893533553 50000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5451871901/10000000000 : ℝ)^4831 ≤ (9262157470829/20000000000000 : ℝ)^3807 := by
    have hnat : (5451871901 : ℕ)^4831*20000000000000^3807 ≤ 9262157470829^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5451871901 10000000000 9262157470829 20000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1660079057/10000000000 : ℝ), (5184485063/10000000000 : ℝ), (5451871901/10000000000 : ℝ)] ![(2048285112217/20000000000000 : ℝ), (21723893533553/50000000000000 : ℝ), (9262157470829/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1660079057/10000000000 : ℝ)|^4831 ≤ (2048285112217/20000000000000 : ℝ)^3807
        have hw : |(-1660079057/10000000000 : ℝ)|=(1660079057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184485063/10000000000 : ℝ)|^4831 ≤ (21723893533553/50000000000000 : ℝ)^3807
        have hw : |(5184485063/10000000000 : ℝ)|=(5184485063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5451871901/10000000000 : ℝ)|^4831 ≤ (9262157470829/20000000000000 : ℝ)^3807
        have hw : |(5451871901/10000000000 : ℝ)|=(5451871901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_s4_5 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278650163/10000000000 : ℝ)*x 0 + (-765232717/5000000000 : ℝ)*x 1 + (272593597/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278650163/10000000000 : ℝ)^4831 ≤ (44451619168611/100000000000000 : ℝ)^3807 := by
    have hnat : (5278650163 : ℕ)^4831*100000000000000^3807 ≤ 44451619168611^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278650163 10000000000 44451619168611 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (765232717/5000000000 : ℝ)^4831 ≤ (4618796525821/50000000000000 : ℝ)^3807 := by
    have hnat : (765232717 : ℕ)^4831*50000000000000^3807 ≤ 4618796525821^3807*5000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      765232717 5000000000 4618796525821 50000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (272593597/500000000 : ℝ)^4831 ≤ (23155393887269/50000000000000 : ℝ)^3807 := by
    have hnat : (272593597 : ℕ)^4831*50000000000000^3807 ≤ 23155393887269^3807*500000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272593597 500000000 23155393887269 50000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278650163/10000000000 : ℝ), (-765232717/5000000000 : ℝ), (272593597/500000000 : ℝ)] ![(44451619168611/100000000000000 : ℝ), (4618796525821/50000000000000 : ℝ), (23155393887269/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278650163/10000000000 : ℝ)|^4831 ≤ (44451619168611/100000000000000 : ℝ)^3807
        have hw : |(5278650163/10000000000 : ℝ)|=(5278650163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-765232717/5000000000 : ℝ)|^4831 ≤ (4618796525821/50000000000000 : ℝ)^3807
        have hw : |(-765232717/5000000000 : ℝ)|=(765232717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(272593597/500000000 : ℝ)|^4831 ≤ (23155393887269/50000000000000 : ℝ)^3807
        have hw : |(272593597/500000000 : ℝ)|=(272593597/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_s4_6 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278650101/10000000000 : ℝ)*x 0 + (2725936037/5000000000 : ℝ)*x 1 + (-1530465331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278650101/10000000000 : ℝ)^4831 ≤ (44451618506073/100000000000000 : ℝ)^3807 := by
    have hnat : (5278650101 : ℕ)^4831*100000000000000^3807 ≤ 44451618506073^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278650101 10000000000 44451618506073 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2725936037/5000000000 : ℝ)^4831 ≤ (11577697304741/25000000000000 : ℝ)^3807 := by
    have hnat : (2725936037 : ℕ)^4831*25000000000000^3807 ≤ 11577697304741^3807*5000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725936037 5000000000 11577697304741 25000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1530465331/10000000000 : ℝ)^4831 ≤ (4618796131367/50000000000000 : ℝ)^3807 := by
    have hnat : (1530465331 : ℕ)^4831*50000000000000^3807 ≤ 4618796131367^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1530465331 10000000000 4618796131367 50000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278650101/10000000000 : ℝ), (2725936037/5000000000 : ℝ), (-1530465331/10000000000 : ℝ)] ![(44451618506073/100000000000000 : ℝ), (11577697304741/25000000000000 : ℝ), (4618796131367/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278650101/10000000000 : ℝ)|^4831 ≤ (44451618506073/100000000000000 : ℝ)^3807
        have hw : |(5278650101/10000000000 : ℝ)|=(5278650101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2725936037/5000000000 : ℝ)|^4831 ≤ (11577697304741/25000000000000 : ℝ)^3807
        have hw : |(2725936037/5000000000 : ℝ)|=(2725936037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1530465331/10000000000 : ℝ)|^4831 ≤ (4618796131367/50000000000000 : ℝ)^3807
        have hw : |(-1530465331/10000000000 : ℝ)|=(1530465331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_s4_7 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (52476527/125000000 : ℝ)*x 0 + (227235833/500000000 : ℝ)*x 1 + (3872055123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52476527/125000000 : ℝ)^4831 ≤ (1662015648989/5000000000000 : ℝ)^3807 := by
    have hnat : (52476527 : ℕ)^4831*5000000000000^3807 ≤ 1662015648989^3807*125000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52476527 125000000 1662015648989 5000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (227235833/500000000 : ℝ)^4831 ≤ (3676068639123/10000000000000 : ℝ)^3807 := by
    have hnat : (227235833 : ℕ)^4831*10000000000000^3807 ≤ 3676068639123^3807*500000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227235833 500000000 3676068639123 10000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3872055123/10000000000 : ℝ)^4831 ≤ (1874937538663/6250000000000 : ℝ)^3807 := by
    have hnat : (3872055123 : ℕ)^4831*6250000000000^3807 ≤ 1874937538663^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3872055123 10000000000 1874937538663 6250000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(52476527/125000000 : ℝ), (227235833/500000000 : ℝ), (3872055123/10000000000 : ℝ)] ![(1662015648989/5000000000000 : ℝ), (3676068639123/10000000000000 : ℝ), (1874937538663/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(52476527/125000000 : ℝ)|^4831 ≤ (1662015648989/5000000000000 : ℝ)^3807
        have hw : |(52476527/125000000 : ℝ)|=(52476527/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(227235833/500000000 : ℝ)|^4831 ≤ (3676068639123/10000000000000 : ℝ)^3807
        have hw : |(227235833/500000000 : ℝ)|=(227235833/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3872055123/10000000000 : ℝ)|^4831 ≤ (1874937538663/6250000000000 : ℝ)^3807
        have hw : |(3872055123/10000000000 : ℝ)|=(3872055123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1628_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175784159/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8159/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (527/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (2637/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1631/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8159/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (527/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8159/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (527/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8159/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (527/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8159/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (527/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8159/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (527/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8159/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (527/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (527/5000 : ℝ) ^ (4827/1024 : ℝ) ≤ (619070953093249/25000000000000000000 : ℝ) := by
    have hpowers : (527/5000 : ℝ)^4827 ≤ (619070953093249/25000000000000000000 : ℝ)^1024 := by
      have hnat : (527 : ℕ)^4827*25000000000000000000^1024 ≤ 619070953093249^1024*5000^4827 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        527 5000 619070953093249 25000000000000000000 4827 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (527/5000 : ℝ)) (X := (619070953093249/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4827 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8159/50000 : ℝ) ^ (4827/1024 : ℝ) ≤ (9718214360823703/50000000000000000000 : ℝ) := by
    have hpowers : (8159/50000 : ℝ)^4827 ≤ (9718214360823703/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8159 : ℕ)^4827*50000000000000000000^1024 ≤ 9718214360823703^1024*50000^4827 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8159 50000 9718214360823703 50000000000000000000 4827 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8159/50000 : ℝ)) (X := (9718214360823703/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4827 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500619070953093249/12500000000000000000 : ℝ) ≤ (10000105061742467/10000000000000000 : ℝ) ^ (4827/1024 : ℝ) := by
    have hpowers : (12500619070953093249/12500000000000000000 : ℝ)^1024 ≤ (10000105061742467/10000000000000000 : ℝ)^4827 := by
      have hnat : (12500619070953093249 : ℕ)^1024*10000000000000000^4827 ≤ 10000105061742467^4827*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500619070953093249 12500000000000000000 10000105061742467 10000000000000000 1024 4827 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000105061742467/10000000000000000 : ℝ)) (X := (12500619070953093249/12500000000000000000 : ℝ)) (by norm_num) 4827 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50010956356267010201/50000000000000000000 : ℝ) ≤ (10000464816262059/10000000000000000 : ℝ) ^ (4827/1024 : ℝ) := by
    have hpowers : (50010956356267010201/50000000000000000000 : ℝ)^1024 ≤ (10000464816262059/10000000000000000 : ℝ)^4827 := by
      have hnat : (50010956356267010201 : ℕ)^1024*10000000000000000^4827 ≤ 10000464816262059^4827*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010956356267010201 50000000000000000000 10000464816262059 10000000000000000 1024 4827 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000464816262059/10000000000000000 : ℝ)) (X := (50010956356267010201/50000000000000000000 : ℝ)) (by norm_num) 4827 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25009718214360823703/25000000000000000000 : ℝ) ≤ (10000824570781651/10000000000000000 : ℝ) ^ (4827/1024 : ℝ) := by
    have hpowers : (25009718214360823703/25000000000000000000 : ℝ)^1024 ≤ (10000824570781651/10000000000000000 : ℝ)^4827 := by
      have hnat : (25009718214360823703 : ℕ)^1024*10000000000000000^4827 ≤ 10000824570781651^4827*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009718214360823703 25000000000000000000 10000824570781651 10000000000000000 1024 4827 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000824570781651/10000000000000000 : ℝ)) (X := (25009718214360823703/25000000000000000000 : ℝ)) (by norm_num) 4827 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(619070953093249/25000000000000000000 : ℝ) ≤ ((28886511710737487483/28890000000000000000 : ℝ)+2*(44969314949/72225000000000 : ℝ)*(527/5000 : ℝ))^(4827/1024 : ℝ) := by
    rw [show (28886511710737487483/28890000000000000000 : ℝ)+2*(44969314949/72225000000000 : ℝ)*(527/5000 : ℝ)=(10000105061742467/10000000000000000 : ℝ) by norm_num, show 1+2*(619070953093249/25000000000000000000 : ℝ)=(12500619070953093249/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9718214360823703/50000000000000000000 : ℝ)+(619070953093249/25000000000000000000 : ℝ) ≤ ((28886511710737487483/28890000000000000000 : ℝ)+(44969314949/72225000000000 : ℝ)*((8159/50000 : ℝ)+(527/5000 : ℝ)))^(4827/1024 : ℝ) := by
    rw [show (28886511710737487483/28890000000000000000 : ℝ)+(44969314949/72225000000000 : ℝ)*((8159/50000 : ℝ)+(527/5000 : ℝ))=(10000464816262059/10000000000000000 : ℝ) by norm_num, show 1+(9718214360823703/50000000000000000000 : ℝ)+(619070953093249/25000000000000000000 : ℝ)=(50010956356267010201/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9718214360823703/50000000000000000000 : ℝ) ≤ ((28886511710737487483/28890000000000000000 : ℝ)+2*(44969314949/72225000000000 : ℝ)*(8159/50000 : ℝ))^(4827/1024 : ℝ) := by
    rw [show (28886511710737487483/28890000000000000000 : ℝ)+2*(44969314949/72225000000000 : ℝ)*(8159/50000 : ℝ)=(10000824570781651/10000000000000000 : ℝ) by norm_num, show 1+2*(9718214360823703/50000000000000000000 : ℝ)=(25009718214360823703/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28886511710737487483/28890000000000000000 : ℝ)*(X 1 0+X 2 0)+(44969314949/72225000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4827/1024 : ℝ)) (lo := (527/5000 : ℝ)) (hi := (8159/50000 : ℝ)) (c := (28886511710737487483/28890000000000000000 : ℝ)) (alpha := (44969314949/72225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28886511710737487483/28890000000000000000 : ℝ)*(X 0 1+X 2 1)+(44969314949/72225000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4827/1024 : ℝ)) (lo := (527/5000 : ℝ)) (hi := (8159/50000 : ℝ)) (c := (28886511710737487483/28890000000000000000 : ℝ)) (alpha := (44969314949/72225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28886511710737487483/28890000000000000000 : ℝ)*(X 0 2+X 1 2)+(44969314949/72225000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4827/1024 : ℝ)) (lo := (527/5000 : ℝ)) (hi := (8159/50000 : ℝ)) (c := (28886511710737487483/28890000000000000000 : ℝ)) (alpha := (44969314949/72225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1660011547/10000000000 : ℝ)*X 0 0+(27269631/50000000 : ℝ)*X 0 1+(5182452273/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350961483/10000000000 : ℝ)*X 1 0+(-224985633/1250000000 : ℝ)*X 1 1+(5182452273/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350961483/10000000000 : ℝ)*X 2 0+(5182452273/10000000000 : ℝ)*X 2 1+(-359977013/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((104948819/250000000 : ℝ)*X 0 0+(3866887823/10000000000 : ℝ)*X 0 1+(568728777/1250000000 : ℝ)*X 0 2+(104948819/250000000 : ℝ)*X 1 0+(3866887823/10000000000 : ℝ)*X 1 1+(568728777/1250000000 : ℝ)*X 1 2+(104948819/250000000 : ℝ)*X 2 0+(3866887823/10000000000 : ℝ)*X 2 1+(568728777/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1660079057/10000000000 : ℝ)*X 0 0+(5184485063/10000000000 : ℝ)*X 0 1+(5451871901/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5278650163/10000000000 : ℝ)*X 1 0+(-765232717/5000000000 : ℝ)*X 1 1+(272593597/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5278650101/10000000000 : ℝ)*X 2 0+(2725936037/5000000000 : ℝ)*X 2 1+(-1530465331/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((52476527/125000000 : ℝ)*X 0 0+(227235833/500000000 : ℝ)*X 0 1+(3872055123/10000000000 : ℝ)*X 0 2+(52476527/125000000 : ℝ)*X 1 0+(227235833/500000000 : ℝ)*X 1 1+(3872055123/10000000000 : ℝ)*X 1 2+(52476527/125000000 : ℝ)*X 2 0+(227235833/500000000 : ℝ)*X 2 1+(3872055123/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16486350665480270553554843/6687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (79993489/20000000000000 : ℝ)*(base19) + (37419211/10000000000000 : ℝ)*(base23) + (13792283/100000000000000 : ℝ)*(lower2) + (30510807/50000000000000 : ℝ)*(upper3) + (20967949/50000000000000 : ℝ)*(upper5) + (643482670067289/25000000000000 : ℝ)*(major0) + (643482670067289/25000000000000 : ℝ)*(major1) + (643482670067289/25000000000000 : ℝ)*(major2) + (57556250915027/1562500000000 : ℝ)*(sp0) + (1841802272783037/50000000000000 : ℝ)*(sp1) + (368360457134141/10000000000000 : ℝ)*(sp2) + (183031777451249/12500000000000 : ℝ)*(sp3) + (305435737/6250000000000 : ℝ)*(sp4) + (1056609919/50000000000000 : ℝ)*(sp7) + (1464256332829829/100000000000000 : ℝ)*(f.failure) + (46045061819169/1250000000000 : ℝ)*(f.sum) + (12482227537/12539062500000000000000000 : ℝ)*base66 + (370310629973595157/80250000000000000000000000000000 : ℝ)*base68 + (1083574852096095157/80250000000000000000000000000000 : ℝ)*base70 + (7645142338904843/80250000000000000000000000000000 : ℝ)*base71 + (270304318271/100312500000000000000000000 : ℝ)*base74 + (128933841842595157/80250000000000000000000000000000 : ℝ)*base76 + (4182366523095157/80250000000000000000000000000000 : ℝ)*base78 + (316599981802095157/80250000000000000000000000000000 : ℝ)*base80 + (1414911709327/200625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (19121189/10000000000000000000000 : ℝ)*base90 + (19121189/10000000000000000000000 : ℝ)*base92 + (19121189/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17225051461987483007686927/1671875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (845552421/50000000000000 : ℝ)*(base19) + (857324469/50000000000000 : ℝ)*(base23) + (233480341/50000000000000 : ℝ)*(lower1) + (29293/400000000000 : ℝ)*(upper2) + (316760983/100000000000000 : ℝ)*(upper3) + (186420681/100000000000000 : ℝ)*(upper5) + (163328292124329/6250000000000 : ℝ)*(major0) + (163328292124329/6250000000000 : ℝ)*(major1) + (163328292124329/6250000000000 : ℝ)*(major2) + (1956268483/50000000000000 : ℝ)*(sp2) + (934969799149123/25000000000000 : ℝ)*(sp4) + (74797550109833/2000000000000 : ℝ)*(sp5) + (934968392352647/25000000000000 : ℝ)*(sp6) + (148662580795421/10000000000000 : ℝ)*(sp7) + (148662580795421/10000000000000 : ℝ)*(f.failure) + (934969799149123/25000000000000 : ℝ)*(f.sum) + (900289110523/1203750000000000000000000000 : ℝ)*base66 + (88626117290692031/60187500000000000000000000000000 : ℝ)*base68 + (1428872200238182969/60187500000000000000000000000000 : ℝ)*base69 + (317338873915432969/60187500000000000000000000000000 : ℝ)*base71 + (3291041269363/1203750000000000000000000000 : ℝ)*base74 + (46405668437932969/60187500000000000000000000000000 : ℝ)*base75 + (12265829639932969/60187500000000000000000000000000 : ℝ)*base77 + (225062451625432969/60187500000000000000000000000000 : ℝ)*base79 + (7092183731567/1203750000000000000000000000 : ℝ)*base81 + (8464061/1000000000000000000000 : ℝ)*base90 + (8464061/1000000000000000000000 : ℝ)*base92 + (8464061/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1628_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175784159/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8159/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (527/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2637/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1631/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1628_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1628_s5_0 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-332003393/2000000000 : ℝ)*x 0 + (5453896527/10000000000 : ℝ)*x 1 + (5182478367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332003393/2000000000 : ℝ)^4831 ≤ (10240939468197/100000000000000 : ℝ)^3807 := by
    have hnat : (332003393 : ℕ)^4831*100000000000000^3807 ≤ 10240939468197^3807*2000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332003393 2000000000 10240939468197 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5453896527/10000000000 : ℝ)^4831 ≤ (289578828133/625000000000 : ℝ)^3807 := by
    have hnat : (5453896527 : ℕ)^4831*625000000000^3807 ≤ 289578828133^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5453896527 10000000000 289578828133 625000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5182478367/10000000000 : ℝ)^4831 ≤ (43426448012759/100000000000000 : ℝ)^3807 := by
    have hnat : (5182478367 : ℕ)^4831*100000000000000^3807 ≤ 43426448012759^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182478367 10000000000 43426448012759 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-332003393/2000000000 : ℝ), (5453896527/10000000000 : ℝ), (5182478367/10000000000 : ℝ)] ![(10240939468197/100000000000000 : ℝ), (289578828133/625000000000 : ℝ), (43426448012759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-332003393/2000000000 : ℝ)|^4831 ≤ (10240939468197/100000000000000 : ℝ)^3807
        have hw : |(-332003393/2000000000 : ℝ)|=(332003393/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5453896527/10000000000 : ℝ)|^4831 ≤ (289578828133/625000000000 : ℝ)^3807
        have hw : |(5453896527/10000000000 : ℝ)|=(5453896527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5182478367/10000000000 : ℝ)|^4831 ≤ (43426448012759/100000000000000 : ℝ)^3807
        have hw : |(5182478367/10000000000 : ℝ)|=(5182478367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_s5_1 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070190541/2000000000 : ℝ)*x 0 + (-1799859847/10000000000 : ℝ)*x 1 + (5182480101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070190541/2000000000 : ℝ)^4831 ≤ (45225669263473/100000000000000 : ℝ)^3807 := by
    have hnat : (1070190541 : ℕ)^4831*100000000000000^3807 ≤ 45225669263473^3807*2000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070190541 2000000000 45225669263473 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1799859847/10000000000 : ℝ)^4831 ≤ (5673932137763/50000000000000 : ℝ)^3807 := by
    have hnat : (1799859847 : ℕ)^4831*50000000000000^3807 ≤ 5673932137763^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1799859847 10000000000 5673932137763 50000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5182480101/10000000000 : ℝ)^4831 ≤ (1737058658041/4000000000000 : ℝ)^3807 := by
    have hnat : (5182480101 : ℕ)^4831*4000000000000^3807 ≤ 1737058658041^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182480101 10000000000 1737058658041 4000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070190541/2000000000 : ℝ), (-1799859847/10000000000 : ℝ), (5182480101/10000000000 : ℝ)] ![(45225669263473/100000000000000 : ℝ), (5673932137763/50000000000000 : ℝ), (1737058658041/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070190541/2000000000 : ℝ)|^4831 ≤ (45225669263473/100000000000000 : ℝ)^3807
        have hw : |(1070190541/2000000000 : ℝ)|=(1070190541/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1799859847/10000000000 : ℝ)|^4831 ≤ (5673932137763/50000000000000 : ℝ)^3807
        have hw : |(-1799859847/10000000000 : ℝ)|=(1799859847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5182480101/10000000000 : ℝ)|^4831 ≤ (1737058658041/4000000000000 : ℝ)^3807
        have hw : |(5182480101/10000000000 : ℝ)|=(5182480101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_s5_2 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-103755261/625000000 : ℝ)*x 0 + (5184509803/10000000000 : ℝ)*x 1 + (85185059/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (103755261/625000000 : ℝ)^4831 ≤ (5120732817931/50000000000000 : ℝ)^3807 := by
    have hnat : (103755261 : ℕ)^4831*50000000000000^3807 ≤ 5120732817931^3807*625000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103755261 625000000 5120732817931 50000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184509803/10000000000 : ℝ)^4831 ≤ (43448050164271/100000000000000 : ℝ)^3807 := by
    have hnat : (5184509803 : ℕ)^4831*100000000000000^3807 ≤ 43448050164271^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184509803 10000000000 43448050164271 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (85185059/156250000 : ℝ)^4831 ≤ (46310484186457/100000000000000 : ℝ)^3807 := by
    have hnat : (85185059 : ℕ)^4831*100000000000000^3807 ≤ 46310484186457^3807*156250000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85185059 156250000 46310484186457 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-103755261/625000000 : ℝ), (5184509803/10000000000 : ℝ), (85185059/156250000 : ℝ)] ![(5120732817931/50000000000000 : ℝ), (43448050164271/100000000000000 : ℝ), (46310484186457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-103755261/625000000 : ℝ)|^4831 ≤ (5120732817931/50000000000000 : ℝ)^3807
        have hw : |(-103755261/625000000 : ℝ)|=(103755261/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184509803/10000000000 : ℝ)|^4831 ≤ (43448050164271/100000000000000 : ℝ)^3807
        have hw : |(5184509803/10000000000 : ℝ)|=(5184509803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(85185059/156250000 : ℝ)|^4831 ≤ (46310484186457/100000000000000 : ℝ)^3807
        have hw : |(85185059/156250000 : ℝ)|=(85185059/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_s5_3 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639328667/5000000000 : ℝ)*x 0 + (-1530495789/10000000000 : ℝ)*x 1 + (5451843261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639328667/5000000000 : ℝ)^4831 ≤ (44451695798583/100000000000000 : ℝ)^3807 := by
    have hnat : (2639328667 : ℕ)^4831*100000000000000^3807 ≤ 44451695798583^3807*5000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639328667 5000000000 44451695798583 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1530495789/10000000000 : ℝ)^4831 ≤ (4618912775259/50000000000000 : ℝ)^3807 := by
    have hnat : (1530495789 : ℕ)^4831*50000000000000^3807 ≤ 4618912775259^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1530495789 10000000000 4618912775259 50000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5451843261/10000000000 : ℝ)^4831 ≤ (46310478635123/100000000000000 : ℝ)^3807 := by
    have hnat : (5451843261 : ℕ)^4831*100000000000000^3807 ≤ 46310478635123^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5451843261 10000000000 46310478635123 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639328667/5000000000 : ℝ), (-1530495789/10000000000 : ℝ), (5451843261/10000000000 : ℝ)] ![(44451695798583/100000000000000 : ℝ), (4618912775259/50000000000000 : ℝ), (46310478635123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639328667/5000000000 : ℝ)|^4831 ≤ (44451695798583/100000000000000 : ℝ)^3807
        have hw : |(2639328667/5000000000 : ℝ)|=(2639328667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1530495789/10000000000 : ℝ)|^4831 ≤ (4618912775259/50000000000000 : ℝ)^3807
        have hw : |(-1530495789/10000000000 : ℝ)|=(1530495789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5451843261/10000000000 : ℝ)|^4831 ≤ (46310478635123/100000000000000 : ℝ)^3807
        have hw : |(5451843261/10000000000 : ℝ)|=(5451843261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_s5_4 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639328481/5000000000 : ℝ)*x 0 + (2725921703/5000000000 : ℝ)*x 1 + (-191312013/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639328481/5000000000 : ℝ)^4831 ≤ (11112922955839/25000000000000 : ℝ)^3807 := by
    have hnat : (2639328481 : ℕ)^4831*25000000000000^3807 ≤ 11112922955839^3807*5000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639328481 5000000000 11112922955839 25000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2725921703/5000000000 : ℝ)^4831 ≤ (1157762004953/2500000000000 : ℝ)^3807 := by
    have hnat : (2725921703 : ℕ)^4831*2500000000000^3807 ≤ 1157762004953^3807*5000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725921703 5000000000 1157762004953 2500000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (191312013/1250000000 : ℝ)^4831 ≤ (9237827963213/100000000000000 : ℝ)^3807 := by
    have hnat : (191312013 : ℕ)^4831*100000000000000^3807 ≤ 9237827963213^3807*1250000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191312013 1250000000 9237827963213 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639328481/5000000000 : ℝ), (2725921703/5000000000 : ℝ), (-191312013/1250000000 : ℝ)] ![(11112922955839/25000000000000 : ℝ), (1157762004953/2500000000000 : ℝ), (9237827963213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639328481/5000000000 : ℝ)|^4831 ≤ (11112922955839/25000000000000 : ℝ)^3807
        have hw : |(2639328481/5000000000 : ℝ)|=(2639328481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2725921703/5000000000 : ℝ)|^4831 ≤ (1157762004953/2500000000000 : ℝ)^3807
        have hw : |(2725921703/5000000000 : ℝ)|=(2725921703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-191312013/1250000000 : ℝ)|^4831 ≤ (9237827963213/100000000000000 : ℝ)^3807
        have hw : |(-191312013/1250000000 : ℝ)|=(191312013/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_s5_5 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (524765699/1250000000 : ℝ)*x 0 + (4544647221/10000000000 : ℝ)*x 1 + (387212411/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (524765699/1250000000 : ℝ)^4831 ≤ (16620173731647/50000000000000 : ℝ)^3807 := by
    have hnat : (524765699 : ℕ)^4831*50000000000000^3807 ≤ 16620173731647^3807*1250000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524765699 1250000000 16620173731647 50000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4544647221/10000000000 : ℝ)^4831 ≤ (36759973647303/100000000000000 : ℝ)^3807 := by
    have hnat : (4544647221 : ℕ)^4831*100000000000000^3807 ≤ 36759973647303^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4544647221 10000000000 36759973647303 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (387212411/1000000000 : ℝ)^4831 ≤ (599993577307/2000000000000 : ℝ)^3807 := by
    have hnat : (387212411 : ℕ)^4831*2000000000000^3807 ≤ 599993577307^3807*1000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387212411 1000000000 599993577307 2000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(524765699/1250000000 : ℝ), (4544647221/10000000000 : ℝ), (387212411/1000000000 : ℝ)] ![(16620173731647/50000000000000 : ℝ), (36759973647303/100000000000000 : ℝ), (599993577307/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(524765699/1250000000 : ℝ)|^4831 ≤ (16620173731647/50000000000000 : ℝ)^3807
        have hw : |(524765699/1250000000 : ℝ)|=(524765699/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4544647221/10000000000 : ℝ)|^4831 ≤ (36759973647303/100000000000000 : ℝ)^3807
        have hw : |(4544647221/10000000000 : ℝ)|=(4544647221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(387212411/1000000000 : ℝ)|^4831 ≤ (599993577307/2000000000000 : ℝ)^3807
        have hw : |(387212411/1000000000 : ℝ)|=(387212411/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1628_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175784159/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1631/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2637/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2637/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16309/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1631/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2637/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1631/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2637/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1631/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2637/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1631/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2637/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1631/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2637/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1631/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2637/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2637/25000 : ℝ) ^ (4827/1024 : ℝ) ≤ (497031234807403/20000000000000000000 : ℝ) := by
    have hpowers : (2637/25000 : ℝ)^4827 ≤ (497031234807403/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2637 : ℕ)^4827*20000000000000000000^1024 ≤ 497031234807403^1024*25000^4827 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2637 25000 497031234807403 20000000000000000000 4827 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2637/25000 : ℝ)) (X := (497031234807403/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4827 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1631/10000 : ℝ) ^ (4827/1024 : ℝ) ≤ (19391551961498451/100000000000000000000 : ℝ) := by
    have hpowers : (1631/10000 : ℝ)^4827 ≤ (19391551961498451/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1631 : ℕ)^4827*100000000000000000000^1024 ≤ 19391551961498451^1024*10000^4827 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1631 10000 19391551961498451 100000000000000000000 4827 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1631/10000 : ℝ)) (X := (19391551961498451/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4827 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000497031234807403/10000000000000000000 : ℝ) ≤ (2000021087632879/2000000000000000 : ℝ) ^ (4827/1024 : ℝ) := by
    have hpowers : (10000497031234807403/10000000000000000000 : ℝ)^1024 ≤ (2000021087632879/2000000000000000 : ℝ)^4827 := by
      have hnat : (10000497031234807403 : ℕ)^1024*2000000000000000^4827 ≤ 2000021087632879^4827*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000497031234807403 10000000000000000000 2000021087632879 2000000000000000 1024 4827 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000021087632879/2000000000000000 : ℝ)) (X := (10000497031234807403/10000000000000000000 : ℝ)) (by norm_num) 4827 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50010938354067767733/50000000000000000000 : ℝ) ≤ (2000092810519263/2000000000000000 : ℝ) ^ (4827/1024 : ℝ) := by
    have hpowers : (50010938354067767733/50000000000000000000 : ℝ)^1024 ≤ (2000092810519263/2000000000000000 : ℝ)^4827 := by
      have hnat : (50010938354067767733 : ℕ)^1024*2000000000000000^4827 ≤ 2000092810519263^4827*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010938354067767733 50000000000000000000 2000092810519263 2000000000000000 1024 4827 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000092810519263/2000000000000000 : ℝ)) (X := (50010938354067767733/50000000000000000000 : ℝ)) (by norm_num) 4827 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50019391551961498451/50000000000000000000 : ℝ) ≤ (2000164533405647/2000000000000000 : ℝ) ^ (4827/1024 : ℝ) := by
    have hpowers : (50019391551961498451/50000000000000000000 : ℝ)^1024 ≤ (2000164533405647/2000000000000000 : ℝ)^4827 := by
      have hnat : (50019391551961498451 : ℕ)^1024*2000000000000000^4827 ≤ 2000164533405647^4827*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50019391551961498451 50000000000000000000 2000164533405647 2000000000000000 1024 4827 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000164533405647/2000000000000000 : ℝ)) (X := (50019391551961498451/50000000000000000000 : ℝ)) (by norm_num) 4827 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(497031234807403/20000000000000000000 : ℝ) ≤ ((5761304220464745967/5762000000000000000 : ℝ)+2*(4482680399/7202500000000 : ℝ)*(2637/25000 : ℝ))^(4827/1024 : ℝ) := by
    rw [show (5761304220464745967/5762000000000000000 : ℝ)+2*(4482680399/7202500000000 : ℝ)*(2637/25000 : ℝ)=(2000021087632879/2000000000000000 : ℝ) by norm_num, show 1+2*(497031234807403/20000000000000000000 : ℝ)=(10000497031234807403/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(19391551961498451/100000000000000000000 : ℝ)+(497031234807403/20000000000000000000 : ℝ) ≤ ((5761304220464745967/5762000000000000000 : ℝ)+(4482680399/7202500000000 : ℝ)*((1631/10000 : ℝ)+(2637/25000 : ℝ)))^(4827/1024 : ℝ) := by
    rw [show (5761304220464745967/5762000000000000000 : ℝ)+(4482680399/7202500000000 : ℝ)*((1631/10000 : ℝ)+(2637/25000 : ℝ))=(2000092810519263/2000000000000000 : ℝ) by norm_num, show 1+(19391551961498451/100000000000000000000 : ℝ)+(497031234807403/20000000000000000000 : ℝ)=(50010938354067767733/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(19391551961498451/100000000000000000000 : ℝ) ≤ ((5761304220464745967/5762000000000000000 : ℝ)+2*(4482680399/7202500000000 : ℝ)*(1631/10000 : ℝ))^(4827/1024 : ℝ) := by
    rw [show (5761304220464745967/5762000000000000000 : ℝ)+2*(4482680399/7202500000000 : ℝ)*(1631/10000 : ℝ)=(2000164533405647/2000000000000000 : ℝ) by norm_num, show 1+2*(19391551961498451/100000000000000000000 : ℝ)=(50019391551961498451/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5761304220464745967/5762000000000000000 : ℝ)*(X 1 0+X 2 0)+(4482680399/7202500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4827/1024 : ℝ)) (lo := (2637/25000 : ℝ)) (hi := (1631/10000 : ℝ)) (c := (5761304220464745967/5762000000000000000 : ℝ)) (alpha := (4482680399/7202500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5761304220464745967/5762000000000000000 : ℝ)*(X 0 1+X 2 1)+(4482680399/7202500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4827/1024 : ℝ)) (lo := (2637/25000 : ℝ)) (hi := (1631/10000 : ℝ)) (c := (5761304220464745967/5762000000000000000 : ℝ)) (alpha := (4482680399/7202500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5761304220464745967/5762000000000000000 : ℝ)*(X 0 2+X 1 2)+(4482680399/7202500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4827/1024 : ℝ)) (lo := (2637/25000 : ℝ)) (hi := (1631/10000 : ℝ)) (c := (5761304220464745967/5762000000000000000 : ℝ)) (alpha := (4482680399/7202500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-332003393/2000000000 : ℝ)*X 0 0+(5453896527/10000000000 : ℝ)*X 0 1+(5182478367/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070190541/2000000000 : ℝ)*X 1 0+(-1799859847/10000000000 : ℝ)*X 1 1+(5182480101/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-103755261/625000000 : ℝ)*X 0 0+(5184509803/10000000000 : ℝ)*X 0 1+(85185059/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s5_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2639328667/5000000000 : ℝ)*X 1 0+(-1530495789/10000000000 : ℝ)*X 1 1+(5451843261/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s5_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((2639328481/5000000000 : ℝ)*X 2 0+(2725921703/5000000000 : ℝ)*X 2 1+(-191312013/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s5_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((524765699/1250000000 : ℝ)*X 0 0+(4544647221/10000000000 : ℝ)*X 0 1+(387212411/1000000000 : ℝ)*X 0 2+(524765699/1250000000 : ℝ)*X 1 0+(4544647221/10000000000 : ℝ)*X 1 1+(387212411/1000000000 : ℝ)*X 1 2+(524765699/1250000000 : ℝ)*X 2 0+(4544647221/10000000000 : ℝ)*X 2 1+(387212411/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_s5_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (945213151672787445185834097/144050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (473491121/50000000000000 : ℝ)*(base19) + (202077697/25000000000000 : ℝ)*(base23) + (74989173/50000000000000 : ℝ)*(lower1) + (63574649/50000000000000 : ℝ)*(upper2) + (85853447/25000000000000 : ℝ)*(upper5) + (1306895221857401/50000000000000 : ℝ)*(major0) + (1306895221857401/50000000000000 : ℝ)*(major1) + (1306895221857401/50000000000000 : ℝ)*(major2) + (5194870151/100000000000000 : ℝ)*(sp0) + (8464870739/100000000000000 : ℝ)*(sp1) + (1870321869861481/50000000000000 : ℝ)*(sp2) + (935159880685033/25000000000000 : ℝ)*(sp3) + (149625925051293/4000000000000 : ℝ)*(sp4) + (371732933528271/25000000000000 : ℝ)*(sp5) + (371732933528271/25000000000000 : ℝ)*(f.failure) + (3740648934593113/100000000000000 : ℝ)*(f.sum) + (117462304403/2881000000000000000000000000 : ℝ)*base65 + (3013573935024351767/288100000000000000000000000000000 : ℝ)*base67 + (2938679014774151767/288100000000000000000000000000000 : ℝ)*base69 + (766920816913951767/288100000000000000000000000000000 : ℝ)*base71 + (2216461578461/2881000000000000000000000000 : ℝ)*base73 + (4083125391401951767/288100000000000000000000000000000 : ℝ)*base75 + (2451306234661251767/288100000000000000000000000000000 : ℝ)*base77 + (3849773557879651767/288100000000000000000000000000000 : ℝ)*base79 + (58477570459/180062500000000000000000000 : ℝ)*base81 + (29540911/2500000000000000000000 : ℝ)*base90 + (29540911/2500000000000000000000 : ℝ)*base92 + (29540911/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1628_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175784159/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1631/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2637/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2637/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16309/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1628_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1628_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175784159/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8211/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10447/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2637/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16309/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1628_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1628_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1628_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175784159/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8211/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10447/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2637/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16309/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1628_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

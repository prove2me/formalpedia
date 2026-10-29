-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1614_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:51:52.865773+00:00
-- url     : https://prove2.me/submissions/890ad94c-1b5c-46c1-8a86-24f9d11c8ef5

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
theorem support_rectangle_w1614_s0_0 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-194748171/1250000000 : ℝ)*x 0 + (5831729319/10000000000 : ℝ)*x 1 + (305999537/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (194748171/1250000000 : ℝ)^4775 ≤ (4689301224339/50000000000000 : ℝ)^3751 := by
    have hnat : (194748171 : ℕ)^4775*50000000000000^3751 ≤ 4689301224339^3751*1250000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194748171 1250000000 4689301224339 50000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5831729319/10000000000 : ℝ)^4775 ≤ (25167001616271/50000000000000 : ℝ)^3751 := by
    have hnat : (5831729319 : ℕ)^4775*50000000000000^3751 ≤ 25167001616271^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5831729319 10000000000 25167001616271 50000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (305999537/625000000 : ℝ)^4775 ≤ (20143697151703/50000000000000 : ℝ)^3751 := by
    have hnat : (305999537 : ℕ)^4775*50000000000000^3751 ≤ 20143697151703^3751*625000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      305999537 625000000 20143697151703 50000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-194748171/1250000000 : ℝ), (5831729319/10000000000 : ℝ), (305999537/625000000 : ℝ)] ![(4689301224339/50000000000000 : ℝ), (25167001616271/50000000000000 : ℝ), (20143697151703/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-194748171/1250000000 : ℝ)|^4775 ≤ (4689301224339/50000000000000 : ℝ)^3751
        have hw : |(-194748171/1250000000 : ℝ)|=(194748171/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5831729319/10000000000 : ℝ)|^4775 ≤ (25167001616271/50000000000000 : ℝ)^3751
        have hw : |(5831729319/10000000000 : ℝ)|=(5831729319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(305999537/625000000 : ℝ)|^4775 ≤ (20143697151703/50000000000000 : ℝ)^3751
        have hw : |(305999537/625000000 : ℝ)|=(305999537/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1614_s0_1 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2726035933/5000000000 : ℝ)*x 0 + (-2075609187/10000000000 : ℝ)*x 1 + (4895992501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2726035933/5000000000 : ℝ)^4775 ≤ (9240053630039/20000000000000 : ℝ)^3751 := by
    have hnat : (2726035933 : ℕ)^4775*20000000000000^3751 ≤ 9240053630039^3751*5000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2726035933 5000000000 9240053630039 20000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2075609187/10000000000 : ℝ)^4775 ≤ (2702467697317/20000000000000 : ℝ)^3751 := by
    have hnat : (2075609187 : ℕ)^4775*20000000000000^3751 ≤ 2702467697317^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2075609187 10000000000 2702467697317 20000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4895992501/10000000000 : ℝ)^4775 ≤ (40287393350179/100000000000000 : ℝ)^3751 := by
    have hnat : (4895992501 : ℕ)^4775*100000000000000^3751 ≤ 40287393350179^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4895992501 10000000000 40287393350179 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2726035933/5000000000 : ℝ), (-2075609187/10000000000 : ℝ), (4895992501/10000000000 : ℝ)] ![(9240053630039/20000000000000 : ℝ), (2702467697317/20000000000000 : ℝ), (40287393350179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2726035933/5000000000 : ℝ)|^4775 ≤ (9240053630039/20000000000000 : ℝ)^3751
        have hw : |(2726035933/5000000000 : ℝ)|=(2726035933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2075609187/10000000000 : ℝ)|^4775 ≤ (2702467697317/20000000000000 : ℝ)^3751
        have hw : |(-2075609187/10000000000 : ℝ)|=(2075609187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4895992501/10000000000 : ℝ)|^4775 ≤ (40287393350179/100000000000000 : ℝ)^3751
        have hw : |(4895992501/10000000000 : ℝ)|=(4895992501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1614_s0_2 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5452071693/10000000000 : ℝ)*x 0 + (305999539/625000000 : ℝ)*x 1 + (-259451157/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5452071693/10000000000 : ℝ)^4775 ≤ (5775033285501/12500000000000 : ℝ)^3751 := by
    have hnat : (5452071693 : ℕ)^4775*12500000000000^3751 ≤ 5775033285501^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5452071693 10000000000 5775033285501 12500000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (305999539/625000000 : ℝ)^4775 ≤ (40287394638607/100000000000000 : ℝ)^3751 := by
    have hnat : (305999539 : ℕ)^4775*100000000000000^3751 ≤ 40287394638607^3751*625000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      305999539 625000000 40287394638607 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (259451157/1250000000 : ℝ)^4775 ≤ (6756169529203/50000000000000 : ℝ)^3751 := by
    have hnat : (259451157 : ℕ)^4775*50000000000000^3751 ≤ 6756169529203^3751*1250000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259451157 1250000000 6756169529203 50000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5452071693/10000000000 : ℝ), (305999539/625000000 : ℝ), (-259451157/1250000000 : ℝ)] ![(5775033285501/12500000000000 : ℝ), (40287394638607/100000000000000 : ℝ), (6756169529203/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5452071693/10000000000 : ℝ)|^4775 ≤ (5775033285501/12500000000000 : ℝ)^3751
        have hw : |(5452071693/10000000000 : ℝ)|=(5452071693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(305999539/625000000 : ℝ)|^4775 ≤ (40287394638607/100000000000000 : ℝ)^3751
        have hw : |(305999539/625000000 : ℝ)|=(305999539/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-259451157/1250000000 : ℝ)|^4775 ≤ (6756169529203/50000000000000 : ℝ)^3751
        have hw : |(-259451157/1250000000 : ℝ)|=(259451157/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1614_s0_3 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4107822107/10000000000 : ℝ)*x 0 + (24599697/80000000 : ℝ)*x 1 + (5386503301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4107822107/10000000000 : ℝ)^4775 ≤ (6444065811259/20000000000000 : ℝ)^3751 := by
    have hnat : (4107822107 : ℕ)^4775*20000000000000^3751 ≤ 6444065811259^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4107822107 10000000000 6444065811259 20000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (24599697/80000000 : ℝ)^4775 ≤ (11142770173749/50000000000000 : ℝ)^3751 := by
    have hnat : (24599697 : ℕ)^4775*50000000000000^3751 ≤ 11142770173749^3751*80000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24599697 80000000 11142770173749 50000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386503301/10000000000 : ℝ)^4775 ≤ (22747065291869/50000000000000 : ℝ)^3751 := by
    have hnat : (5386503301 : ℕ)^4775*50000000000000^3751 ≤ 22747065291869^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386503301 10000000000 22747065291869 50000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4107822107/10000000000 : ℝ), (24599697/80000000 : ℝ), (5386503301/10000000000 : ℝ)] ![(6444065811259/20000000000000 : ℝ), (11142770173749/50000000000000 : ℝ), (22747065291869/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4107822107/10000000000 : ℝ)|^4775 ≤ (6444065811259/20000000000000 : ℝ)^3751
        have hw : |(4107822107/10000000000 : ℝ)|=(4107822107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(24599697/80000000 : ℝ)|^4775 ≤ (11142770173749/50000000000000 : ℝ)^3751
        have hw : |(24599697/80000000 : ℝ)|=(24599697/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386503301/10000000000 : ℝ)|^4775 ≤ (22747065291869/50000000000000 : ℝ)^3751
        have hw : |(5386503301/10000000000 : ℝ)|=(5386503301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1614_s0_4 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1560725331/10000000000 : ℝ)*x 0 + (2459816387/5000000000 : ℝ)*x 1 + (5807251021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1560725331/10000000000 : ℝ)^4775 ≤ (4699801965723/50000000000000 : ℝ)^3751 := by
    have hnat : (1560725331 : ℕ)^4775*50000000000000^3751 ≤ 4699801965723^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1560725331 10000000000 4699801965723 50000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2459816387/5000000000 : ℝ)^4775 ≤ (20267594314721/50000000000000 : ℝ)^3751 := by
    have hnat : (2459816387 : ℕ)^4775*50000000000000^3751 ≤ 20267594314721^3751*5000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2459816387 5000000000 20267594314721 50000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5807251021/10000000000 : ℝ)^4775 ≤ (12516301855453/25000000000000 : ℝ)^3751 := by
    have hnat : (5807251021 : ℕ)^4775*25000000000000^3751 ≤ 12516301855453^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5807251021 10000000000 12516301855453 25000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1560725331/10000000000 : ℝ), (2459816387/5000000000 : ℝ), (5807251021/10000000000 : ℝ)] ![(4699801965723/50000000000000 : ℝ), (20267594314721/50000000000000 : ℝ), (12516301855453/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1560725331/10000000000 : ℝ)|^4775 ≤ (4699801965723/50000000000000 : ℝ)^3751
        have hw : |(-1560725331/10000000000 : ℝ)|=(1560725331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2459816387/5000000000 : ℝ)|^4775 ≤ (20267594314721/50000000000000 : ℝ)^3751
        have hw : |(2459816387/5000000000 : ℝ)|=(2459816387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5807251021/10000000000 : ℝ)|^4775 ≤ (12516301855453/25000000000000 : ℝ)^3751
        have hw : |(5807251021/10000000000 : ℝ)|=(5807251021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1614_s0_5 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (8119563/15625000 : ℝ)*x 0 + (-232870161/2000000000 : ℝ)*x 1 + (1451812781/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8119563/15625000 : ℝ)^4775 ≤ (2716338807509/6250000000000 : ℝ)^3751 := by
    have hnat : (8119563 : ℕ)^4775*6250000000000^3751 ≤ 2716338807509^3751*15625000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8119563 15625000 2716338807509 6250000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (232870161/2000000000 : ℝ)^4775 ≤ (50573207073/781250000000 : ℝ)^3751 := by
    have hnat : (232870161 : ℕ)^4775*781250000000^3751 ≤ 50573207073^3751*2000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      232870161 2000000000 50573207073 781250000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1451812781/2500000000 : ℝ)^4775 ≤ (50065208552203/100000000000000 : ℝ)^3751 := by
    have hnat : (1451812781 : ℕ)^4775*100000000000000^3751 ≤ 50065208552203^3751*2500000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1451812781 2500000000 50065208552203 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8119563/15625000 : ℝ), (-232870161/2000000000 : ℝ), (1451812781/2500000000 : ℝ)] ![(2716338807509/6250000000000 : ℝ), (50573207073/781250000000 : ℝ), (50065208552203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8119563/15625000 : ℝ)|^4775 ≤ (2716338807509/6250000000000 : ℝ)^3751
        have hw : |(8119563/15625000 : ℝ)|=(8119563/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-232870161/2000000000 : ℝ)|^4775 ≤ (50573207073/781250000000 : ℝ)^3751
        have hw : |(-232870161/2000000000 : ℝ)|=(232870161/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1451812781/2500000000 : ℝ)|^4775 ≤ (50065208552203/100000000000000 : ℝ)^3751
        have hw : |(1451812781/2500000000 : ℝ)|=(1451812781/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1614_s0_6 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2598260187/5000000000 : ℝ)*x 0 + (725906439/1250000000 : ℝ)*x 1 + (-9314801/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2598260187/5000000000 : ℝ)^4775 ≤ (43461421495069/100000000000000 : ℝ)^3751 := by
    have hnat : (2598260187 : ℕ)^4775*100000000000000^3751 ≤ 43461421495069^3751*5000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598260187 5000000000 43461421495069 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (725906439/1250000000 : ℝ)^4775 ≤ (25032606405189/50000000000000 : ℝ)^3751 := by
    have hnat : (725906439 : ℕ)^4775*50000000000000^3751 ≤ 25032606405189^3751*1250000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      725906439 1250000000 25032606405189 50000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9314801/80000000 : ℝ)^4775 ≤ (3236682846361/50000000000000 : ℝ)^3751 := by
    have hnat : (9314801 : ℕ)^4775*50000000000000^3751 ≤ 3236682846361^3751*80000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9314801 80000000 3236682846361 50000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2598260187/5000000000 : ℝ), (725906439/1250000000 : ℝ), (-9314801/80000000 : ℝ)] ![(43461421495069/100000000000000 : ℝ), (25032606405189/50000000000000 : ℝ), (3236682846361/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2598260187/5000000000 : ℝ)|^4775 ≤ (43461421495069/100000000000000 : ℝ)^3751
        have hw : |(2598260187/5000000000 : ℝ)|=(2598260187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(725906439/1250000000 : ℝ)|^4775 ≤ (25032606405189/50000000000000 : ℝ)^3751
        have hw : |(725906439/1250000000 : ℝ)|=(725906439/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-9314801/80000000 : ℝ)|^4775 ≤ (3236682846361/50000000000000 : ℝ)^3751
        have hw : |(-9314801/80000000 : ℝ)|=(9314801/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1614_s0_7 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (822917819/2000000000 : ℝ)*x 0 + (532810451/1000000000 : ℝ)*x 1 + (391928831/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (822917819/2000000000 : ℝ)^4775 ≤ (16143956043699/50000000000000 : ℝ)^3751 := by
    have hnat : (822917819 : ℕ)^4775*50000000000000^3751 ≤ 16143956043699^3751*2000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      822917819 2000000000 16143956043699 50000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (532810451/1000000000 : ℝ)^4775 ≤ (44867179382769/100000000000000 : ℝ)^3751 := by
    have hnat : (532810451 : ℕ)^4775*100000000000000^3751 ≤ 44867179382769^3751*1000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532810451 1000000000 44867179382769 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (391928831/1250000000 : ℝ)^4775 ≤ (2855613563351/12500000000000 : ℝ)^3751 := by
    have hnat : (391928831 : ℕ)^4775*12500000000000^3751 ≤ 2855613563351^3751*1250000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      391928831 1250000000 2855613563351 12500000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(822917819/2000000000 : ℝ), (532810451/1000000000 : ℝ), (391928831/1250000000 : ℝ)] ![(16143956043699/50000000000000 : ℝ), (44867179382769/100000000000000 : ℝ), (2855613563351/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(822917819/2000000000 : ℝ)|^4775 ≤ (16143956043699/50000000000000 : ℝ)^3751
        have hw : |(822917819/2000000000 : ℝ)|=(822917819/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(532810451/1000000000 : ℝ)|^4775 ≤ (44867179382769/100000000000000 : ℝ)^3751
        have hw : |(532810451/1000000000 : ℝ)|=(532810451/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(391928831/1250000000 : ℝ)|^4775 ≤ (2855613563351/12500000000000 : ℝ)^3751
        have hw : |(391928831/1250000000 : ℝ)|=(391928831/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1614_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43378611/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (4109/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (483/2000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4771/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4771 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4771*1^1024 ≤ 0^1024*1^4771 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4771 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4771 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4771/1024 : ℝ) ≤ (699674424239482177/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4771 ≤ (699674424239482177/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4771*50000000000000000000^1024 ≤ 699674424239482177^1024*5^4771 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 699674424239482177 50000000000000000000 4771 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (699674424239482177/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4771 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4771/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4771 := by
      have hnat : (1 : ℕ)^1024*1^4771 ≤ 1^4771*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4771 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4771 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50699674424239482177/50000000000000000000 : ℝ) ≤ (5014935277168203/5000000000000000 : ℝ) ^ (4771/1024 : ℝ) := by
    have hpowers : (50699674424239482177/50000000000000000000 : ℝ)^1024 ≤ (5014935277168203/5000000000000000 : ℝ)^4771 := by
      have hnat : (50699674424239482177 : ℕ)^1024*5000000000000000^4771 ≤ 5014935277168203^4771*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50699674424239482177 50000000000000000000 5014935277168203 5000000000000000 1024 4771 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5014935277168203/5000000000000000 : ℝ)) (X := (50699674424239482177/50000000000000000000 : ℝ)) (by norm_num) 4771 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25699674424239482177/25000000000000000000 : ℝ) ≤ (2514935277168203/2500000000000000 : ℝ) ^ (4771/1024 : ℝ) := by
    have hpowers : (25699674424239482177/25000000000000000000 : ℝ)^1024 ≤ (2514935277168203/2500000000000000 : ℝ)^4771 := by
      have hnat : (25699674424239482177 : ℕ)^1024*2500000000000000^4771 ≤ 2514935277168203^4771*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25699674424239482177 25000000000000000000 2514935277168203 2500000000000000 1024 4771 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2514935277168203/2500000000000000 : ℝ)) (X := (25699674424239482177/25000000000000000000 : ℝ)) (by norm_num) 4771 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(14935277168203/2000000000000000 : ℝ)*(0 : ℝ))^(4771/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(14935277168203/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(699674424239482177/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(14935277168203/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4771/1024 : ℝ) := by
    rw [show (1 : ℝ)+(14935277168203/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5014935277168203/5000000000000000 : ℝ) by norm_num, show 1+(699674424239482177/50000000000000000000 : ℝ)+(0 : ℝ)=(50699674424239482177/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(699674424239482177/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(14935277168203/2000000000000000 : ℝ)*(2/5 : ℝ))^(4771/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(14935277168203/2000000000000000 : ℝ)*(2/5 : ℝ)=(2514935277168203/2500000000000000 : ℝ) by norm_num, show 1+2*(699674424239482177/50000000000000000000 : ℝ)=(25699674424239482177/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(14935277168203/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4771/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14935277168203/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(14935277168203/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4771/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14935277168203/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(14935277168203/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4771/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14935277168203/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-194748171/1250000000 : ℝ)*X 0 0+(5831729319/10000000000 : ℝ)*X 0 1+(305999537/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2726035933/5000000000 : ℝ)*X 1 0+(-2075609187/10000000000 : ℝ)*X 1 1+(4895992501/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5452071693/10000000000 : ℝ)*X 2 0+(305999539/625000000 : ℝ)*X 2 1+(-259451157/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4107822107/10000000000 : ℝ)*X 0 0+(24599697/80000000 : ℝ)*X 0 1+(5386503301/10000000000 : ℝ)*X 0 2+(4107822107/10000000000 : ℝ)*X 1 0+(24599697/80000000 : ℝ)*X 1 1+(5386503301/10000000000 : ℝ)*X 1 2+(4107822107/10000000000 : ℝ)*X 2 0+(24599697/80000000 : ℝ)*X 2 1+(5386503301/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1560725331/10000000000 : ℝ)*X 0 0+(2459816387/5000000000 : ℝ)*X 0 1+(5807251021/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((8119563/15625000 : ℝ)*X 1 0+(-232870161/2000000000 : ℝ)*X 1 1+(1451812781/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2598260187/5000000000 : ℝ)*X 2 0+(725906439/1250000000 : ℝ)*X 2 1+(-9314801/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((822917819/2000000000 : ℝ)*X 0 0+(532810451/1000000000 : ℝ)*X 0 1+(391928831/1250000000 : ℝ)*X 0 2+(822917819/2000000000 : ℝ)*X 1 0+(532810451/1000000000 : ℝ)*X 1 1+(391928831/1250000000 : ℝ)*X 1 2+(822917819/2000000000 : ℝ)*X 2 0+(532810451/1000000000 : ℝ)*X 2 1+(391928831/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (32141482336863268764981/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6368789/50000000000000 : ℝ)*(base1) + (522876843/50000000000000 : ℝ)*(base19) + (252960807/25000000000000 : ℝ)*(base23) + (40316539/25000000000000 : ℝ)*(upper3) + (1628837/1250000000000 : ℝ)*(upper5) + (187662501758491/25000000000000 : ℝ)*(major0) + (187662501758491/25000000000000 : ℝ)*(major1) + (187662501758491/25000000000000 : ℝ)*(major2) + (1068680657577003/100000000000000 : ℝ)*(sp0) + (66792719471441/6250000000000 : ℝ)*(sp1) + (534341772726757/50000000000000 : ℝ)*(sp2) + (432613456207549/100000000000000 : ℝ)*(sp3) + (978114329/25000000000000 : ℝ)*(sp4) + (908202407/50000000000000 : ℝ)*(sp7) + (432615285349941/100000000000000 : ℝ)*(f.failure) + (534342278648371/50000000000000 : ℝ)*(f.sum) + (10779656136673/25000000000000000000000000000 : ℝ)*base65 + (279064375161673/50000000000000000000000000000 : ℝ)*base67 + (299098283811673/50000000000000000000000000000 : ℝ)*base69 + (55087712011673/50000000000000000000000000000 : ℝ)*base71 + (116131858136673/25000000000000000000000000000 : ℝ)*base73 + (240758798388327/50000000000000000000000000000 : ℝ)*base76 + (22011876711673/50000000000000000000000000000 : ℝ)*base77 + (56633384588327/50000000000000000000000000000 : ℝ)*base80 + (89874462036673/25000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (10488049/2500000000000000000000 : ℝ)*base90 + (10488049/2500000000000000000000 : ℝ)*base92 + (10488049/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (130476463964858058118221/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (324912621/100000000000000 : ℝ)*(base19) + (186800419/25000000000000 : ℝ)*(base23) + (201642747/50000000000000 : ℝ)*(base39) + (10145891/100000000000000 : ℝ)*(upper2) + (30681499/12500000000000 : ℝ)*(upper5) + (3165343890607/400000000000 : ℝ)*(major0) + (3165343890607/400000000000 : ℝ)*(major1) + (49458473085391/6250000000000 : ℝ)*(major2) + (1622281109/100000000000000 : ℝ)*(sp1) + (1491477397/100000000000000 : ℝ)*(sp2) + (1126607997485599/100000000000000 : ℝ)*(sp4) + (1126606050291869/100000000000000 : ℝ)*(sp5) + (56330308104601/5000000000000 : ℝ)*(sp6) + (456063457548093/100000000000000 : ℝ)*(sp7) + (456063457548093/100000000000000 : ℝ)*(f.failure) + (1126608400771093/100000000000000 : ℝ)*(f.sum) + (57106101731609/100000000000000000000000000000 : ℝ)*base65 + (94178925822373/12500000000000000000000000000 : ℝ)*base67 + (2379789905179/800000000000000000000000000 : ℝ)*base70 + (32695397659873/12500000000000000000000000000 : ℝ)*base71 + (483675208131609/100000000000000000000000000000 : ℝ)*base73 + (2964372133979/800000000000000000000000000 : ℝ)*base76 + (2204223220421/800000000000000000000000000 : ℝ)*base77 + (1344871949179/800000000000000000000000000 : ℝ)*base80 + (121704716421/400000000000000000000000000 : ℝ)*base81 + (9961177/2500000000000000000000 : ℝ)*base90 + (9961177/2500000000000000000000 : ℝ)*base92 + (9961177/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1614_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43378611/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4109/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (483/2000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1614_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1614_s1_0 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-419887597/2500000000 : ℝ)*x 0 + (345386611/625000000 : ℝ)*x 1 + (2561438073/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (419887597/2500000000 : ℝ)^4775 ≤ (10319899970219/100000000000000 : ℝ)^3751 := by
    have hnat : (419887597 : ℕ)^4775*100000000000000^3751 ≤ 10319899970219^3751*2500000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419887597 2500000000 10319899970219 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (345386611/625000000 : ℝ)^4775 ≤ (47001229232209/100000000000000 : ℝ)^3751 := by
    have hnat : (345386611 : ℕ)^4775*100000000000000^3751 ≤ 47001229232209^3751*625000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345386611 625000000 47001229232209 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2561438073/5000000000 : ℝ)^4775 ≤ (5334858847793/12500000000000 : ℝ)^3751 := by
    have hnat : (2561438073 : ℕ)^4775*12500000000000^3751 ≤ 5334858847793^3751*5000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2561438073 5000000000 5334858847793 12500000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-419887597/2500000000 : ℝ), (345386611/625000000 : ℝ), (2561438073/5000000000 : ℝ)] ![(10319899970219/100000000000000 : ℝ), (47001229232209/100000000000000 : ℝ), (5334858847793/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-419887597/2500000000 : ℝ)|^4775 ≤ (10319899970219/100000000000000 : ℝ)^3751
        have hw : |(-419887597/2500000000 : ℝ)|=(419887597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(345386611/625000000 : ℝ)|^4775 ≤ (47001229232209/100000000000000 : ℝ)^3751
        have hw : |(345386611/625000000 : ℝ)|=(345386611/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2561438073/5000000000 : ℝ)|^4775 ≤ (5334858847793/12500000000000 : ℝ)^3751
        have hw : |(2561438073/5000000000 : ℝ)|=(2561438073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1614_s1_1 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (268538697/500000000 : ℝ)*x 0 + (-472583703/2500000000 : ℝ)*x 1 + (320179749/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268538697/500000000 : ℝ)^4775 ≤ (45325081598437/100000000000000 : ℝ)^3751 := by
    have hnat : (268538697 : ℕ)^4775*100000000000000^3751 ≤ 45325081598437^3751*500000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268538697 500000000 45325081598437 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (472583703/2500000000 : ℝ)^4775 ≤ (11996049309291/100000000000000 : ℝ)^3751 := by
    have hnat : (472583703 : ℕ)^4775*100000000000000^3751 ≤ 11996049309291^3751*2500000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      472583703 2500000000 11996049309291 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (320179749/625000000 : ℝ)^4775 ≤ (10669717266069/25000000000000 : ℝ)^3751 := by
    have hnat : (320179749 : ℕ)^4775*25000000000000^3751 ≤ 10669717266069^3751*625000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      320179749 625000000 10669717266069 25000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268538697/500000000 : ℝ), (-472583703/2500000000 : ℝ), (320179749/625000000 : ℝ)] ![(45325081598437/100000000000000 : ℝ), (11996049309291/100000000000000 : ℝ), (10669717266069/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268538697/500000000 : ℝ)|^4775 ≤ (45325081598437/100000000000000 : ℝ)^3751
        have hw : |(268538697/500000000 : ℝ)|=(268538697/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-472583703/2500000000 : ℝ)|^4775 ≤ (11996049309291/100000000000000 : ℝ)^3751
        have hw : |(-472583703/2500000000 : ℝ)|=(472583703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(320179749/625000000 : ℝ)|^4775 ≤ (10669717266069/25000000000000 : ℝ)^3751
        have hw : |(320179749/625000000 : ℝ)|=(320179749/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1614_s1_2 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1342693459/2500000000 : ℝ)*x 0 + (512287601/1000000000 : ℝ)*x 1 + (-1890334919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342693459/2500000000 : ℝ)^4775 ≤ (45325080481159/100000000000000 : ℝ)^3751 := by
    have hnat : (1342693459 : ℕ)^4775*100000000000000^3751 ≤ 45325080481159^3751*2500000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342693459 2500000000 45325080481159 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (512287601/1000000000 : ℝ)^4775 ≤ (8535773868003/20000000000000 : ℝ)^3751 := by
    have hnat : (512287601 : ℕ)^4775*20000000000000^3751 ≤ 8535773868003^3751*1000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512287601 1000000000 8535773868003 20000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1890334919/10000000000 : ℝ)^4775 ≤ (11996050173681/100000000000000 : ℝ)^3751 := by
    have hnat : (1890334919 : ℕ)^4775*100000000000000^3751 ≤ 11996050173681^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1890334919 10000000000 11996050173681 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342693459/2500000000 : ℝ), (512287601/1000000000 : ℝ), (-1890334919/10000000000 : ℝ)] ![(45325080481159/100000000000000 : ℝ), (8535773868003/20000000000000 : ℝ), (11996050173681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342693459/2500000000 : ℝ)|^4775 ≤ (45325080481159/100000000000000 : ℝ)^3751
        have hw : |(1342693459/2500000000 : ℝ)|=(1342693459/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(512287601/1000000000 : ℝ)|^4775 ≤ (8535773868003/20000000000000 : ℝ)^3751
        have hw : |(512287601/1000000000 : ℝ)|=(512287601/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1890334919/10000000000 : ℝ)|^4775 ≤ (11996050173681/100000000000000 : ℝ)^3751
        have hw : |(-1890334919/10000000000 : ℝ)|=(1890334919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1614_s1_3 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4198485757/10000000000 : ℝ)*x 0 + (186144599/500000000 : ℝ)*x 1 + (2359592001/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4198485757/10000000000 : ℝ)^4775 ≤ (6625662253911/20000000000000 : ℝ)^3751 := by
    have hnat : (4198485757 : ℕ)^4775*20000000000000^3751 ≤ 6625662253911^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4198485757 10000000000 6625662253911 20000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (186144599/500000000 : ℝ)^4775 ≤ (28427156824223/100000000000000 : ℝ)^3751 := by
    have hnat : (186144599 : ℕ)^4775*100000000000000^3751 ≤ 28427156824223^3751*500000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      186144599 500000000 28427156824223 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2359592001/5000000000 : ℝ)^4775 ≤ (2402783243897/6250000000000 : ℝ)^3751 := by
    have hnat : (2359592001 : ℕ)^4775*6250000000000^3751 ≤ 2402783243897^3751*5000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2359592001 5000000000 2402783243897 6250000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4198485757/10000000000 : ℝ), (186144599/500000000 : ℝ), (2359592001/5000000000 : ℝ)] ![(6625662253911/20000000000000 : ℝ), (28427156824223/100000000000000 : ℝ), (2402783243897/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4198485757/10000000000 : ℝ)|^4775 ≤ (6625662253911/20000000000000 : ℝ)^3751
        have hw : |(4198485757/10000000000 : ℝ)|=(4198485757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(186144599/500000000 : ℝ)|^4775 ≤ (28427156824223/100000000000000 : ℝ)^3751
        have hw : |(186144599/500000000 : ℝ)|=(186144599/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2359592001/5000000000 : ℝ)|^4775 ≤ (2402783243897/6250000000000 : ℝ)^3751
        have hw : |(2359592001/5000000000 : ℝ)|=(2359592001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1614_s1_4 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-419941249/2500000000 : ℝ)*x 0 + (205089273/400000000 : ℝ)*x 1 + (276088163/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (419941249/2500000000 : ℝ)^4775 ≤ (2580394657073/25000000000000 : ℝ)^3751 := by
    have hnat : (419941249 : ℕ)^4775*25000000000000^3751 ≤ 2580394657073^3751*2500000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419941249 2500000000 2580394657073 25000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (205089273/400000000 : ℝ)^4775 ≤ (42725069681873/100000000000000 : ℝ)^3751 := by
    have hnat : (205089273 : ℕ)^4775*100000000000000^3751 ≤ 42725069681873^3751*400000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205089273 400000000 42725069681873 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (276088163/500000000 : ℝ)^4775 ≤ (46953351672379/100000000000000 : ℝ)^3751 := by
    have hnat : (276088163 : ℕ)^4775*100000000000000^3751 ≤ 46953351672379^3751*500000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276088163 500000000 46953351672379 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-419941249/2500000000 : ℝ), (205089273/400000000 : ℝ), (276088163/500000000 : ℝ)] ![(2580394657073/25000000000000 : ℝ), (42725069681873/100000000000000 : ℝ), (46953351672379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-419941249/2500000000 : ℝ)|^4775 ≤ (2580394657073/25000000000000 : ℝ)^3751
        have hw : |(-419941249/2500000000 : ℝ)|=(419941249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(205089273/400000000 : ℝ)|^4775 ≤ (42725069681873/100000000000000 : ℝ)^3751
        have hw : |(205089273/400000000 : ℝ)|=(205089273/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(276088163/500000000 : ℝ)|^4775 ≤ (46953351672379/100000000000000 : ℝ)^3751
        have hw : |(276088163/500000000 : ℝ)|=(276088163/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1614_s1_5 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5263419081/10000000000 : ℝ)*x 0 + (-1491447097/10000000000 : ℝ)*x 1 + (1104352719/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5263419081/10000000000 : ℝ)^4775 ≤ (22087461956279/50000000000000 : ℝ)^3751 := by
    have hnat : (5263419081 : ℕ)^4775*50000000000000^3751 ≤ 22087461956279^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263419081 10000000000 22087461956279 50000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1491447097/10000000000 : ℝ)^4775 ≤ (8871720768831/100000000000000 : ℝ)^3751 := by
    have hnat : (1491447097 : ℕ)^4775*100000000000000^3751 ≤ 8871720768831^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1491447097 10000000000 8871720768831 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1104352719/2000000000 : ℝ)^4775 ≤ (5869169412331/12500000000000 : ℝ)^3751 := by
    have hnat : (1104352719 : ℕ)^4775*12500000000000^3751 ≤ 5869169412331^3751*2000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104352719 2000000000 5869169412331 12500000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5263419081/10000000000 : ℝ), (-1491447097/10000000000 : ℝ), (1104352719/2000000000 : ℝ)] ![(22087461956279/50000000000000 : ℝ), (8871720768831/100000000000000 : ℝ), (5869169412331/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5263419081/10000000000 : ℝ)|^4775 ≤ (22087461956279/50000000000000 : ℝ)^3751
        have hw : |(5263419081/10000000000 : ℝ)|=(5263419081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1491447097/10000000000 : ℝ)|^4775 ≤ (8871720768831/100000000000000 : ℝ)^3751
        have hw : |(-1491447097/10000000000 : ℝ)|=(1491447097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1104352719/2000000000 : ℝ)|^4775 ≤ (5869169412331/12500000000000 : ℝ)^3751
        have hw : |(1104352719/2000000000 : ℝ)|=(1104352719/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1614_s1_6 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1052683687/2000000000 : ℝ)*x 0 + (5521763841/10000000000 : ℝ)*x 1 + (-1491447659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1052683687/2000000000 : ℝ)^4775 ≤ (44174917010689/100000000000000 : ℝ)^3751 := by
    have hnat : (1052683687 : ℕ)^4775*100000000000000^3751 ≤ 44174917010689^3751*2000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052683687 2000000000 44174917010689 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5521763841/10000000000 : ℝ)^4775 ≤ (46953357961519/100000000000000 : ℝ)^3751 := by
    have hnat : (5521763841 : ℕ)^4775*100000000000000^3751 ≤ 46953357961519^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5521763841 10000000000 46953357961519 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1491447659/10000000000 : ℝ)^4775 ≤ (8871725024449/100000000000000 : ℝ)^3751 := by
    have hnat : (1491447659 : ℕ)^4775*100000000000000^3751 ≤ 8871725024449^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1491447659 10000000000 8871725024449 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1052683687/2000000000 : ℝ), (5521763841/10000000000 : ℝ), (-1491447659/10000000000 : ℝ)] ![(44174917010689/100000000000000 : ℝ), (46953357961519/100000000000000 : ℝ), (8871725024449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1052683687/2000000000 : ℝ)|^4775 ≤ (44174917010689/100000000000000 : ℝ)^3751
        have hw : |(1052683687/2000000000 : ℝ)|=(1052683687/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5521763841/10000000000 : ℝ)|^4775 ≤ (46953357961519/100000000000000 : ℝ)^3751
        have hw : |(5521763841/10000000000 : ℝ)|=(5521763841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1491447659/10000000000 : ℝ)|^4775 ≤ (8871725024449/100000000000000 : ℝ)^3751
        have hw : |(-1491447659/10000000000 : ℝ)|=(1491447659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1614_s1_7 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2099507173/5000000000 : ℝ)*x 0 + (23542127/50000000 : ℝ)*x 1 + (466726989/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2099507173/5000000000 : ℝ)^4775 ≤ (16566810414637/50000000000000 : ℝ)^3751 := by
    have hnat : (2099507173 : ℕ)^4775*50000000000000^3751 ≤ 16566810414637^3751*5000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099507173 5000000000 16566810414637 50000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (23542127/50000000 : ℝ)^4775 ≤ (1916649801347/5000000000000 : ℝ)^3751 := by
    have hnat : (23542127 : ℕ)^4775*5000000000000^3751 ≤ 1916649801347^3751*50000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23542127 50000000 1916649801347 5000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (466726989/1250000000 : ℝ)^4775 ≤ (28533383128971/100000000000000 : ℝ)^3751 := by
    have hnat : (466726989 : ℕ)^4775*100000000000000^3751 ≤ 28533383128971^3751*1250000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466726989 1250000000 28533383128971 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2099507173/5000000000 : ℝ), (23542127/50000000 : ℝ), (466726989/1250000000 : ℝ)] ![(16566810414637/50000000000000 : ℝ), (1916649801347/5000000000000 : ℝ), (28533383128971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2099507173/5000000000 : ℝ)|^4775 ≤ (16566810414637/50000000000000 : ℝ)^3751
        have hw : |(2099507173/5000000000 : ℝ)|=(2099507173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(23542127/50000000 : ℝ)|^4775 ≤ (1916649801347/5000000000000 : ℝ)^3751
        have hw : |(23542127/50000000 : ℝ)|=(23542127/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(466726989/1250000000 : ℝ)|^4775 ≤ (28533383128971/100000000000000 : ℝ)^3751
        have hw : |(466726989/1250000000 : ℝ)|=(466726989/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1614_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43378611/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (483/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4109/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9201/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (71/400 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (483/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4109/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (483/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4109/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (483/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4109/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (483/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4109/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (483/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4109/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (483/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4109/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4109/100000 : ℝ) ^ (4771/1024 : ℝ) ≤ (8691357149351/25000000000000000000 : ℝ) := by
    have hpowers : (4109/100000 : ℝ)^4771 ≤ (8691357149351/25000000000000000000 : ℝ)^1024 := by
      have hnat : (4109 : ℕ)^4771*25000000000000000000^1024 ≤ 8691357149351^1024*100000^4771 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4109 100000 8691357149351 25000000000000000000 4771 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4109/100000 : ℝ)) (X := (8691357149351/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4771 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (483/2000 : ℝ) ^ (4771/1024 : ℝ) ≤ (16665182090670983/12500000000000000000 : ℝ) := by
    have hpowers : (483/2000 : ℝ)^4771 ≤ (16665182090670983/12500000000000000000 : ℝ)^1024 := by
      have hnat : (483 : ℕ)^4771*12500000000000000000^1024 ≤ 16665182090670983^1024*2000^4771 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        483 2000 16665182090670983 12500000000000000000 4771 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (483/2000 : ℝ)) (X := (16665182090670983/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4771 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500008691357149351/12500000000000000000 : ℝ) ≤ (5000000746170387/5000000000000000 : ℝ) ^ (4771/1024 : ℝ) := by
    have hpowers : (12500008691357149351/12500000000000000000 : ℝ)^1024 ≤ (5000000746170387/5000000000000000 : ℝ)^4771 := by
      have hnat : (12500008691357149351 : ℕ)^1024*5000000000000000^4771 ≤ 5000000746170387^4771*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500008691357149351 12500000000000000000 5000000746170387 5000000000000000 1024 4771 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000746170387/5000000000000000 : ℝ)) (X := (12500008691357149351/12500000000000000000 : ℝ)) (by norm_num) 4771 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25033339055538491317/25000000000000000000 : ℝ) ≤ (5001430363839061/5000000000000000 : ℝ) ^ (4771/1024 : ℝ) := by
    have hpowers : (25033339055538491317/25000000000000000000 : ℝ)^1024 ≤ (5001430363839061/5000000000000000 : ℝ)^4771 := by
      have hnat : (25033339055538491317 : ℕ)^1024*5000000000000000^4771 ≤ 5001430363839061^4771*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25033339055538491317 25000000000000000000 5001430363839061 5000000000000000 1024 4771 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001430363839061/5000000000000000 : ℝ)) (X := (25033339055538491317/25000000000000000000 : ℝ)) (by norm_num) 4771 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6266665182090670983/6250000000000000000 : ℝ) ≤ (1000571996301547/1000000000000000 : ℝ) ^ (4771/1024 : ℝ) := by
    have hpowers : (6266665182090670983/6250000000000000000 : ℝ)^1024 ≤ (1000571996301547/1000000000000000 : ℝ)^4771 := by
      have hnat : (6266665182090670983 : ℕ)^1024*1000000000000000^4771 ≤ 1000571996301547^4771*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6266665182090670983 6250000000000000000 1000571996301547 1000000000000000 1024 4771 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000571996301547/1000000000000000 : ℝ)) (X := (6266665182090670983/6250000000000000000 : ℝ)) (by norm_num) 4771 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8691357149351/25000000000000000000 : ℝ) ≤ ((2862664753028558941/2863000000000000000 : ℝ)+2*(714808834337/501025000000000 : ℝ)*(4109/100000 : ℝ))^(4771/1024 : ℝ) := by
    rw [show (2862664753028558941/2863000000000000000 : ℝ)+2*(714808834337/501025000000000 : ℝ)*(4109/100000 : ℝ)=(5000000746170387/5000000000000000 : ℝ) by norm_num, show 1+2*(8691357149351/25000000000000000000 : ℝ)=(12500008691357149351/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16665182090670983/12500000000000000000 : ℝ)+(8691357149351/25000000000000000000 : ℝ) ≤ ((2862664753028558941/2863000000000000000 : ℝ)+(714808834337/501025000000000 : ℝ)*((483/2000 : ℝ)+(4109/100000 : ℝ)))^(4771/1024 : ℝ) := by
    rw [show (2862664753028558941/2863000000000000000 : ℝ)+(714808834337/501025000000000 : ℝ)*((483/2000 : ℝ)+(4109/100000 : ℝ))=(5001430363839061/5000000000000000 : ℝ) by norm_num, show 1+(16665182090670983/12500000000000000000 : ℝ)+(8691357149351/25000000000000000000 : ℝ)=(25033339055538491317/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16665182090670983/12500000000000000000 : ℝ) ≤ ((2862664753028558941/2863000000000000000 : ℝ)+2*(714808834337/501025000000000 : ℝ)*(483/2000 : ℝ))^(4771/1024 : ℝ) := by
    rw [show (2862664753028558941/2863000000000000000 : ℝ)+2*(714808834337/501025000000000 : ℝ)*(483/2000 : ℝ)=(1000571996301547/1000000000000000 : ℝ) by norm_num, show 1+2*(16665182090670983/12500000000000000000 : ℝ)=(6266665182090670983/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2862664753028558941/2863000000000000000 : ℝ)*(X 1 0+X 2 0)+(714808834337/501025000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4771/1024 : ℝ)) (lo := (4109/100000 : ℝ)) (hi := (483/2000 : ℝ)) (c := (2862664753028558941/2863000000000000000 : ℝ)) (alpha := (714808834337/501025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2862664753028558941/2863000000000000000 : ℝ)*(X 0 1+X 2 1)+(714808834337/501025000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4771/1024 : ℝ)) (lo := (4109/100000 : ℝ)) (hi := (483/2000 : ℝ)) (c := (2862664753028558941/2863000000000000000 : ℝ)) (alpha := (714808834337/501025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2862664753028558941/2863000000000000000 : ℝ)*(X 0 2+X 1 2)+(714808834337/501025000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4771/1024 : ℝ)) (lo := (4109/100000 : ℝ)) (hi := (483/2000 : ℝ)) (c := (2862664753028558941/2863000000000000000 : ℝ)) (alpha := (714808834337/501025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-419887597/2500000000 : ℝ)*X 0 0+(345386611/625000000 : ℝ)*X 0 1+(2561438073/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((268538697/500000000 : ℝ)*X 1 0+(-472583703/2500000000 : ℝ)*X 1 1+(320179749/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1342693459/2500000000 : ℝ)*X 2 0+(512287601/1000000000 : ℝ)*X 2 1+(-1890334919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4198485757/10000000000 : ℝ)*X 0 0+(186144599/500000000 : ℝ)*X 0 1+(2359592001/5000000000 : ℝ)*X 0 2+(4198485757/10000000000 : ℝ)*X 1 0+(186144599/500000000 : ℝ)*X 1 1+(2359592001/5000000000 : ℝ)*X 1 2+(4198485757/10000000000 : ℝ)*X 2 0+(186144599/500000000 : ℝ)*X 2 1+(2359592001/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-419941249/2500000000 : ℝ)*X 0 0+(205089273/400000000 : ℝ)*X 0 1+(276088163/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5263419081/10000000000 : ℝ)*X 1 0+(-1491447097/10000000000 : ℝ)*X 1 1+(1104352719/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1052683687/2000000000 : ℝ)*X 2 0+(5521763841/10000000000 : ℝ)*X 2 1+(-1491447659/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2099507173/5000000000 : ℝ)*X 0 0+(23542127/50000000 : ℝ)*X 0 1+(466726989/1250000000 : ℝ)*X 0 2+(2099507173/5000000000 : ℝ)*X 1 0+(23542127/50000000 : ℝ)*X 1 1+(466726989/1250000000 : ℝ)*X 1 2+(2099507173/5000000000 : ℝ)*X 2 0+(23542127/50000000 : ℝ)*X 2 1+(466726989/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (36620213871581537387649/3578750000000000000000000000 : ℝ) := by norm_num
    linear_combination (44893113/20000000000000 : ℝ)*(base1) + (497342611/25000000000000 : ℝ)*(base19) + (1941357039/100000000000000 : ℝ)*(base23) + (52961859/20000000000000 : ℝ)*(upper3) + (195492337/100000000000000 : ℝ)*(upper5) + (870811848739959/50000000000000 : ℝ)*(major0) + (870811848739959/50000000000000 : ℝ)*(major1) + (870811848739959/50000000000000 : ℝ)*(major2) + (1239749675832393/50000000000000 : ℝ)*(sp0) + (619877733254389/25000000000000 : ℝ)*(sp1) + (30993887262887/1250000000000 : ℝ)*(sp2) + (125465950611189/12500000000000 : ℝ)*(sp3) + (6897594389/50000000000000 : ℝ)*(sp4) + (252085093/4000000000000 : ℝ)*(sp7) + (501867065741201/50000000000000 : ℝ)*(f.failure) + (619878230597/25000000000 : ℝ)*(f.sum) + (619047341141/7157500000000000000000000000 : ℝ)*base65 + (325324240419716581/143150000000000000000000000000000 : ℝ)*base68 + (105190664741183419/143150000000000000000000000000000 : ℝ)*base69 + (268617247192916581/143150000000000000000000000000000 : ℝ)*base72 + (2020997770773/894687500000000000000000000 : ℝ)*base74 + (405924129593016581/143150000000000000000000000000000 : ℝ)*base76 + (168466667459083419/143150000000000000000000000000000 : ℝ)*base77 + (634707539306183419/143150000000000000000000000000000 : ℝ)*base79 + (1550285584913/894687500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (9851811/1250000000000000000000 : ℝ)*base89 + (9851811/1250000000000000000000 : ℝ)*base91 + (9851811/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (228909544932297312793069893/50102500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (255234601/25000000000000 : ℝ)*(base19) + (807598991/100000000000000 : ℝ)*(base23) + (28834131/50000000000000 : ℝ)*(upper2) + (60085627/25000000000000 : ℝ)*(upper3) + (1883553/20000000000000 : ℝ)*(upper5) + (178034981754013/10000000000000 : ℝ)*(major0) + (178034981754013/10000000000000 : ℝ)*(major1) + (178034981754013/10000000000000 : ℝ)*(major2) + (3782625731/50000000000000 : ℝ)*(sp1) + (1746466353/25000000000000 : ℝ)*(sp2) + (1267323339527583/50000000000000 : ℝ)*(sp4) + (25346380928653/1000000000000 : ℝ)*(sp5) + (633659721397691/25000000000000 : ℝ)*(sp6) + (64128300233183/6250000000000 : ℝ)*(sp7) + (64128300233183/6250000000000 : ℝ)*(f.failure) + (1267323339527583/50000000000000 : ℝ)*(f.sum) + (699054696231/313140625000000000000000000 : ℝ)*base66 + (1397381504639798369/200410000000000000000000000000000 : ℝ)*base68 + (219266173838341631/200410000000000000000000000000000 : ℝ)*base69 + (591443415182178369/200410000000000000000000000000000 : ℝ)*base72 + (26792396121287/5010250000000000000000000000 : ℝ)*base74 + (431553466550338369/200410000000000000000000000000000 : ℝ)*base76 + (2204945365710898369/200410000000000000000000000000000 : ℝ)*base78 + (747346197244338369/200410000000000000000000000000000 : ℝ)*base80 + (5432468550317/2505125000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1523813/156250000000000000000 : ℝ)*base89 + (1523813/156250000000000000000 : ℝ)*base91 + (1523813/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1614_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43378611/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (483/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4109/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9201/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (71/400 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1614_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1614_s2_0 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1692913591/10000000000 : ℝ)*x 0 + (27325099/50000000 : ℝ)*x 1 + (646910821/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1692913591/10000000000 : ℝ)^4775 ≤ (10424538064579/100000000000000 : ℝ)^3751 := by
    have hnat : (1692913591 : ℕ)^4775*100000000000000^3751 ≤ 10424538064579^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1692913591 10000000000 10424538064579 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27325099/50000000 : ℝ)^4775 ≤ (23169992758349/50000000000000 : ℝ)^3751 := by
    have hnat : (27325099 : ℕ)^4775*50000000000000^3751 ≤ 23169992758349^3751*50000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27325099 50000000 23169992758349 50000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (646910821/1250000000 : ℝ)^4775 ≤ (8647095280367/20000000000000 : ℝ)^3751 := by
    have hnat : (646910821 : ℕ)^4775*20000000000000^3751 ≤ 8647095280367^3751*1250000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646910821 1250000000 8647095280367 20000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1692913591/10000000000 : ℝ), (27325099/50000000 : ℝ), (646910821/1250000000 : ℝ)] ![(10424538064579/100000000000000 : ℝ), (23169992758349/50000000000000 : ℝ), (8647095280367/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1692913591/10000000000 : ℝ)|^4775 ≤ (10424538064579/100000000000000 : ℝ)^3751
        have hw : |(-1692913591/10000000000 : ℝ)|=(1692913591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(27325099/50000000 : ℝ)|^4775 ≤ (23169992758349/50000000000000 : ℝ)^3751
        have hw : |(27325099/50000000 : ℝ)|=(27325099/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(646910821/1250000000 : ℝ)|^4775 ≤ (8647095280367/20000000000000 : ℝ)^3751
        have hw : |(646910821/1250000000 : ℝ)|=(646910821/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1614_s2_1 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677403457/5000000000 : ℝ)*x 0 + (-460623269/2500000000 : ℝ)*x 1 + (1035057303/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677403457/5000000000 : ℝ)^4775 ≤ (45153616526089/100000000000000 : ℝ)^3751 := by
    have hnat : (2677403457 : ℕ)^4775*100000000000000^3751 ≤ 45153616526089^3751*5000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677403457 5000000000 45153616526089 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (460623269/2500000000 : ℝ)^4775 ≤ (2902726905647/25000000000000 : ℝ)^3751 := by
    have hnat : (460623269 : ℕ)^4775*25000000000000^3751 ≤ 2902726905647^3751*2500000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      460623269 2500000000 2902726905647 25000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1035057303/2000000000 : ℝ)^4775 ≤ (43235475838187/100000000000000 : ℝ)^3751 := by
    have hnat : (1035057303 : ℕ)^4775*100000000000000^3751 ≤ 43235475838187^3751*2000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035057303 2000000000 43235475838187 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677403457/5000000000 : ℝ), (-460623269/2500000000 : ℝ), (1035057303/2000000000 : ℝ)] ![(45153616526089/100000000000000 : ℝ), (2902726905647/25000000000000 : ℝ), (43235475838187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677403457/5000000000 : ℝ)|^4775 ≤ (45153616526089/100000000000000 : ℝ)^3751
        have hw : |(2677403457/5000000000 : ℝ)|=(2677403457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-460623269/2500000000 : ℝ)|^4775 ≤ (2902726905647/25000000000000 : ℝ)^3751
        have hw : |(-460623269/2500000000 : ℝ)|=(460623269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1035057303/2000000000 : ℝ)|^4775 ≤ (43235475838187/100000000000000 : ℝ)^3751
        have hw : |(1035057303/2000000000 : ℝ)|=(1035057303/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1614_s2_2 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354806867/10000000000 : ℝ)*x 0 + (5175286499/10000000000 : ℝ)*x 1 + (-46062329/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354806867/10000000000 : ℝ)^4775 ≤ (1806144640863/4000000000000 : ℝ)^3751 := by
    have hnat : (5354806867 : ℕ)^4775*4000000000000^3751 ≤ 1806144640863^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354806867 10000000000 1806144640863 4000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5175286499/10000000000 : ℝ)^4775 ≤ (43235475668029/100000000000000 : ℝ)^3751 := by
    have hnat : (5175286499 : ℕ)^4775*100000000000000^3751 ≤ 43235475668029^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175286499 10000000000 43235475668029 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (46062329/250000000 : ℝ)^4775 ≤ (11610908296443/100000000000000 : ℝ)^3751 := by
    have hnat : (46062329 : ℕ)^4775*100000000000000^3751 ≤ 11610908296443^3751*250000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46062329 250000000 11610908296443 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354806867/10000000000 : ℝ), (5175286499/10000000000 : ℝ), (-46062329/250000000 : ℝ)] ![(1806144640863/4000000000000 : ℝ), (43235475668029/100000000000000 : ℝ), (11610908296443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354806867/10000000000 : ℝ)|^4775 ≤ (1806144640863/4000000000000 : ℝ)^3751
        have hw : |(5354806867/10000000000 : ℝ)|=(5354806867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5175286499/10000000000 : ℝ)|^4775 ≤ (43235475668029/100000000000000 : ℝ)^3751
        have hw : |(5175286499/10000000000 : ℝ)|=(5175286499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-46062329/250000000 : ℝ)|^4775 ≤ (11610908296443/100000000000000 : ℝ)^3751
        have hw : |(-46062329/250000000 : ℝ)|=(46062329/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1614_s2_3 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4208356853/10000000000 : ℝ)*x 0 + (965534163/2500000000 : ℝ)*x 1 + (4577861571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4208356853/10000000000 : ℝ)^4775 ≤ (3322749434553/10000000000000 : ℝ)^3751 := by
    have hnat : (4208356853 : ℕ)^4775*10000000000000^3751 ≤ 3322749434553^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4208356853 10000000000 3322749434553 10000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (965534163/2500000000 : ℝ)^4775 ≤ (29787504039331/100000000000000 : ℝ)^3751 := by
    have hnat : (965534163 : ℕ)^4775*100000000000000^3751 ≤ 29787504039331^3751*2500000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      965534163 2500000000 29787504039331 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4577861571/10000000000 : ℝ)^4775 ≤ (18492500798827/50000000000000 : ℝ)^3751 := by
    have hnat : (4577861571 : ℕ)^4775*50000000000000^3751 ≤ 18492500798827^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4577861571 10000000000 18492500798827 50000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4208356853/10000000000 : ℝ), (965534163/2500000000 : ℝ), (4577861571/10000000000 : ℝ)] ![(3322749434553/10000000000000 : ℝ), (29787504039331/100000000000000 : ℝ), (18492500798827/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4208356853/10000000000 : ℝ)|^4775 ≤ (3322749434553/10000000000000 : ℝ)^3751
        have hw : |(4208356853/10000000000 : ℝ)|=(4208356853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(965534163/2500000000 : ℝ)|^4775 ≤ (29787504039331/100000000000000 : ℝ)^3751
        have hw : |(965534163/2500000000 : ℝ)|=(965534163/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4577861571/10000000000 : ℝ)|^4775 ≤ (18492500798827/50000000000000 : ℝ)^3751
        have hw : |(4577861571/10000000000 : ℝ)|=(4577861571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1614_s2_4 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-846496607/5000000000 : ℝ)*x 0 + (5177541377/10000000000 : ℝ)*x 1 + (5462740189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (846496607/5000000000 : ℝ)^4775 ≤ (1042516221557/10000000000000 : ℝ)^3751 := by
    have hnat : (846496607 : ℕ)^4775*10000000000000^3751 ≤ 1042516221557^3751*5000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846496607 5000000000 1042516221557 10000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5177541377/10000000000 : ℝ)^4775 ≤ (10814864356703/25000000000000 : ℝ)^3751 := by
    have hnat : (5177541377 : ℕ)^4775*25000000000000^3751 ≤ 10814864356703^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177541377 10000000000 10814864356703 25000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5462740189/10000000000 : ℝ)^4775 ≤ (46315380340509/100000000000000 : ℝ)^3751 := by
    have hnat : (5462740189 : ℕ)^4775*100000000000000^3751 ≤ 46315380340509^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462740189 10000000000 46315380340509 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-846496607/5000000000 : ℝ), (5177541377/10000000000 : ℝ), (5462740189/10000000000 : ℝ)] ![(1042516221557/10000000000000 : ℝ), (10814864356703/25000000000000 : ℝ), (46315380340509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-846496607/5000000000 : ℝ)|^4775 ≤ (1042516221557/10000000000000 : ℝ)^3751
        have hw : |(-846496607/5000000000 : ℝ)|=(846496607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5177541377/10000000000 : ℝ)|^4775 ≤ (10814864356703/25000000000000 : ℝ)^3751
        have hw : |(5177541377/10000000000 : ℝ)|=(5177541377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5462740189/10000000000 : ℝ)|^4775 ≤ (46315380340509/100000000000000 : ℝ)^3751
        have hw : |(5462740189/10000000000 : ℝ)|=(5462740189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1614_s2_5 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (329862259/625000000 : ℝ)*x 0 + (-388759943/2500000000 : ℝ)*x 1 + (341421249/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (329862259/625000000 : ℝ)^4775 ≤ (4432858578937/10000000000000 : ℝ)^3751 := by
    have hnat : (329862259 : ℕ)^4775*10000000000000^3751 ≤ 4432858578937^3751*625000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329862259 625000000 4432858578937 10000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (388759943/2500000000 : ℝ)^4775 ≤ (9356036058007/100000000000000 : ℝ)^3751 := by
    have hnat : (388759943 : ℕ)^4775*100000000000000^3751 ≤ 9356036058007^3751*2500000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      388759943 2500000000 9356036058007 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (341421249/625000000 : ℝ)^4775 ≤ (926307562559/2000000000000 : ℝ)^3751 := by
    have hnat : (341421249 : ℕ)^4775*2000000000000^3751 ≤ 926307562559^3751*625000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341421249 625000000 926307562559 2000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(329862259/625000000 : ℝ), (-388759943/2500000000 : ℝ), (341421249/625000000 : ℝ)] ![(4432858578937/10000000000000 : ℝ), (9356036058007/100000000000000 : ℝ), (926307562559/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(329862259/625000000 : ℝ)|^4775 ≤ (4432858578937/10000000000000 : ℝ)^3751
        have hw : |(329862259/625000000 : ℝ)|=(329862259/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-388759943/2500000000 : ℝ)|^4775 ≤ (9356036058007/100000000000000 : ℝ)^3751
        have hw : |(-388759943/2500000000 : ℝ)|=(388759943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(341421249/625000000 : ℝ)|^4775 ≤ (926307562559/2000000000000 : ℝ)^3751
        have hw : |(341421249/625000000 : ℝ)|=(341421249/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1614_s2_6 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277796007/10000000000 : ℝ)*x 0 + (5462740327/10000000000 : ℝ)*x 1 + (-38875987/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277796007/10000000000 : ℝ)^4775 ≤ (44328584324571/100000000000000 : ℝ)^3751 := by
    have hnat : (5277796007 : ℕ)^4775*100000000000000^3751 ≤ 44328584324571^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277796007 10000000000 44328584324571 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5462740327/10000000000 : ℝ)^4775 ≤ (46315381829939/100000000000000 : ℝ)^3751 := by
    have hnat : (5462740327 : ℕ)^4775*100000000000000^3751 ≤ 46315381829939^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462740327 10000000000 46315381829939 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (38875987/250000000 : ℝ)^4775 ≤ (2339008455389/25000000000000 : ℝ)^3751 := by
    have hnat : (38875987 : ℕ)^4775*25000000000000^3751 ≤ 2339008455389^3751*250000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38875987 250000000 2339008455389 25000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277796007/10000000000 : ℝ), (5462740327/10000000000 : ℝ), (-38875987/250000000 : ℝ)] ![(44328584324571/100000000000000 : ℝ), (46315381829939/100000000000000 : ℝ), (2339008455389/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277796007/10000000000 : ℝ)|^4775 ≤ (44328584324571/100000000000000 : ℝ)^3751
        have hw : |(5277796007/10000000000 : ℝ)|=(5277796007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5462740327/10000000000 : ℝ)|^4775 ≤ (46315381829939/100000000000000 : ℝ)^3751
        have hw : |(5462740327/10000000000 : ℝ)|=(5462740327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-38875987/250000000 : ℝ)|^4775 ≤ (2339008455389/25000000000000 : ℝ)^3751
        have hw : |(-38875987/250000000 : ℝ)|=(38875987/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1614_s2_7 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (526069183/1250000000 : ℝ)*x 0 + (182891651/400000000 : ℝ)*x 1 + (773553641/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (526069183/1250000000 : ℝ)^4775 ≤ (16614735252361/50000000000000 : ℝ)^3751 := by
    have hnat : (526069183 : ℕ)^4775*50000000000000^3751 ≤ 16614735252361^3751*1250000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526069183 1250000000 16614735252361 50000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (182891651/400000000 : ℝ)^4775 ≤ (9231930649887/25000000000000 : ℝ)^3751 := by
    have hnat : (182891651 : ℕ)^4775*25000000000000^3751 ≤ 9231930649887^3751*400000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182891651 400000000 9231930649887 25000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (773553641/2000000000 : ℝ)^4775 ≤ (14921403435249/50000000000000 : ℝ)^3751 := by
    have hnat : (773553641 : ℕ)^4775*50000000000000^3751 ≤ 14921403435249^3751*2000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      773553641 2000000000 14921403435249 50000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(526069183/1250000000 : ℝ), (182891651/400000000 : ℝ), (773553641/2000000000 : ℝ)] ![(16614735252361/50000000000000 : ℝ), (9231930649887/25000000000000 : ℝ), (14921403435249/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(526069183/1250000000 : ℝ)|^4775 ≤ (16614735252361/50000000000000 : ℝ)^3751
        have hw : |(526069183/1250000000 : ℝ)|=(526069183/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(182891651/400000000 : ℝ)|^4775 ≤ (9231930649887/25000000000000 : ℝ)^3751
        have hw : |(182891651/400000000 : ℝ)|=(182891651/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(773553641/2000000000 : ℝ)|^4775 ≤ (14921403435249/50000000000000 : ℝ)^3751
        have hw : |(773553641/2000000000 : ℝ)|=(773553641/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1614_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43378611/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (71/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9201/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10333/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16477/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (71/400 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9201/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (71/400 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9201/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (71/400 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9201/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (71/400 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9201/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (71/400 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9201/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (71/400 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9201/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9201/100000 : ℝ) ^ (4771/1024 : ℝ) ≤ (371758777064373/25000000000000000000 : ℝ) := by
    have hpowers : (9201/100000 : ℝ)^4771 ≤ (371758777064373/25000000000000000000 : ℝ)^1024 := by
      have hnat : (9201 : ℕ)^4771*25000000000000000000^1024 ≤ 371758777064373^1024*100000^4771 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9201 100000 371758777064373 25000000000000000000 4771 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9201/100000 : ℝ)) (X := (371758777064373/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4771 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (71/400 : ℝ) ^ (4771/1024 : ℝ) ≤ (6351996250766717/20000000000000000000 : ℝ) := by
    have hpowers : (71/400 : ℝ)^4771 ≤ (6351996250766717/20000000000000000000 : ℝ)^1024 := by
      have hnat : (71 : ℕ)^4771*20000000000000000000^1024 ≤ 6351996250766717^1024*400^4771 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        71 400 6351996250766717 20000000000000000000 4771 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (71/400 : ℝ)) (X := (6351996250766717/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4771 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500371758777064373/12500000000000000000 : ℝ) ≤ (10000063831740419/10000000000000000 : ℝ) ^ (4771/1024 : ℝ) := by
    have hpowers : (12500371758777064373/12500000000000000000 : ℝ)^1024 ≤ (10000063831740419/10000000000000000 : ℝ)^4771 := by
      have hnat : (12500371758777064373 : ℕ)^1024*10000000000000000^4771 ≤ 10000063831740419^4771*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500371758777064373 12500000000000000000 10000063831740419 10000000000000000 1024 4771 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000063831740419/10000000000000000 : ℝ)) (X := (12500371758777064373/12500000000000000000 : ℝ)) (by norm_num) 4771 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100033247016362091077/100000000000000000000 : ℝ) ≤ (5000356743878233/5000000000000000 : ℝ) ^ (4771/1024 : ℝ) := by
    have hpowers : (100033247016362091077/100000000000000000000 : ℝ)^1024 ≤ (5000356743878233/5000000000000000 : ℝ)^4771 := by
      have hnat : (100033247016362091077 : ℕ)^1024*5000000000000000^4771 ≤ 5000356743878233^4771*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100033247016362091077 100000000000000000000 5000356743878233 5000000000000000 1024 4771 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000356743878233/5000000000000000 : ℝ)) (X := (100033247016362091077/100000000000000000000 : ℝ)) (by norm_num) 4771 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006351996250766717/10000000000000000000 : ℝ) ≤ (10001363143772513/10000000000000000 : ℝ) ^ (4771/1024 : ℝ) := by
    have hpowers : (10006351996250766717/10000000000000000000 : ℝ)^1024 ≤ (10001363143772513/10000000000000000 : ℝ)^4771 := by
      have hnat : (10006351996250766717 : ℕ)^1024*10000000000000000^4771 ≤ 10001363143772513^4771*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006351996250766717 10000000000000000000 10001363143772513 10000000000000000 1024 4771 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001363143772513/10000000000000000 : ℝ)) (X := (10006351996250766717/10000000000000000000 : ℝ)) (by norm_num) 4771 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(371758777064373/25000000000000000000 : ℝ) ≤ ((85478590727541545137/85490000000000000000 : ℝ)+2*(649656016047/854900000000000 : ℝ)*(9201/100000 : ℝ))^(4771/1024 : ℝ) := by
    rw [show (85478590727541545137/85490000000000000000 : ℝ)+2*(649656016047/854900000000000 : ℝ)*(9201/100000 : ℝ)=(10000063831740419/10000000000000000 : ℝ) by norm_num, show 1+2*(371758777064373/25000000000000000000 : ℝ)=(12500371758777064373/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6351996250766717/20000000000000000000 : ℝ)+(371758777064373/25000000000000000000 : ℝ) ≤ ((85478590727541545137/85490000000000000000 : ℝ)+(649656016047/854900000000000 : ℝ)*((71/400 : ℝ)+(9201/100000 : ℝ)))^(4771/1024 : ℝ) := by
    rw [show (85478590727541545137/85490000000000000000 : ℝ)+(649656016047/854900000000000 : ℝ)*((71/400 : ℝ)+(9201/100000 : ℝ))=(5000356743878233/5000000000000000 : ℝ) by norm_num, show 1+(6351996250766717/20000000000000000000 : ℝ)+(371758777064373/25000000000000000000 : ℝ)=(100033247016362091077/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6351996250766717/20000000000000000000 : ℝ) ≤ ((85478590727541545137/85490000000000000000 : ℝ)+2*(649656016047/854900000000000 : ℝ)*(71/400 : ℝ))^(4771/1024 : ℝ) := by
    rw [show (85478590727541545137/85490000000000000000 : ℝ)+2*(649656016047/854900000000000 : ℝ)*(71/400 : ℝ)=(10001363143772513/10000000000000000 : ℝ) by norm_num, show 1+2*(6351996250766717/20000000000000000000 : ℝ)=(10006351996250766717/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (85478590727541545137/85490000000000000000 : ℝ)*(X 1 0+X 2 0)+(649656016047/854900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4771/1024 : ℝ)) (lo := (9201/100000 : ℝ)) (hi := (71/400 : ℝ)) (c := (85478590727541545137/85490000000000000000 : ℝ)) (alpha := (649656016047/854900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (85478590727541545137/85490000000000000000 : ℝ)*(X 0 1+X 2 1)+(649656016047/854900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4771/1024 : ℝ)) (lo := (9201/100000 : ℝ)) (hi := (71/400 : ℝ)) (c := (85478590727541545137/85490000000000000000 : ℝ)) (alpha := (649656016047/854900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (85478590727541545137/85490000000000000000 : ℝ)*(X 0 2+X 1 2)+(649656016047/854900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4771/1024 : ℝ)) (lo := (9201/100000 : ℝ)) (hi := (71/400 : ℝ)) (c := (85478590727541545137/85490000000000000000 : ℝ)) (alpha := (649656016047/854900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1692913591/10000000000 : ℝ)*X 0 0+(27325099/50000000 : ℝ)*X 0 1+(646910821/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677403457/5000000000 : ℝ)*X 1 0+(-460623269/2500000000 : ℝ)*X 1 1+(1035057303/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354806867/10000000000 : ℝ)*X 2 0+(5175286499/10000000000 : ℝ)*X 2 1+(-46062329/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4208356853/10000000000 : ℝ)*X 0 0+(965534163/2500000000 : ℝ)*X 0 1+(4577861571/10000000000 : ℝ)*X 0 2+(4208356853/10000000000 : ℝ)*X 1 0+(965534163/2500000000 : ℝ)*X 1 1+(4577861571/10000000000 : ℝ)*X 1 2+(4208356853/10000000000 : ℝ)*X 2 0+(965534163/2500000000 : ℝ)*X 2 1+(4577861571/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-846496607/5000000000 : ℝ)*X 0 0+(5177541377/10000000000 : ℝ)*X 0 1+(5462740189/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((329862259/625000000 : ℝ)*X 1 0+(-388759943/2500000000 : ℝ)*X 1 1+(341421249/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5277796007/10000000000 : ℝ)*X 2 0+(5462740327/10000000000 : ℝ)*X 2 1+(-38875987/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((526069183/1250000000 : ℝ)*X 0 0+(182891651/400000000 : ℝ)*X 0 1+(773553641/2000000000 : ℝ)*X 0 2+(526069183/1250000000 : ℝ)*X 1 0+(182891651/400000000 : ℝ)*X 1 1+(773553641/2000000000 : ℝ)*X 1 2+(526069183/1250000000 : ℝ)*X 2 0+(182891651/400000000 : ℝ)*X 2 1+(773553641/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1971388311854836498402236213/213725000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (321010039/20000000000000 : ℝ)*(base19) + (1530082491/100000000000000 : ℝ)*(base23) + (1495111/6250000000000 : ℝ)*(lower2) + (260738039/100000000000000 : ℝ)*(upper3) + (10042607/6250000000000 : ℝ)*(upper5) + (121217180407061/5000000000000 : ℝ)*(major0) + (121217180407061/5000000000000 : ℝ)*(major1) + (121217180407061/5000000000000 : ℝ)*(major2) + (1725734896685079/50000000000000 : ℝ)*(sp0) + (3451485421006403/100000000000000 : ℝ)*(sp1) + (1725742747987053/50000000000000 : ℝ)*(sp2) + (223550703107/16000000000 : ℝ)*(sp3) + (430817161/2500000000000 : ℝ)*(sp4) + (3994171073/50000000000000 : ℝ)*(sp7) + (21831248168139/1562500000000 : ℝ)*(f.failure) + (1725743513028299/50000000000000 : ℝ)*(f.sum) + (4597687992547/1068625000000000000000000000 : ℝ)*base66 + (4579196840101787643/427450000000000000000000000000000 : ℝ)*base68 + (4587635410104087643/427450000000000000000000000000000 : ℝ)*base70 + (5982173403646487643/427450000000000000000000000000000 : ℝ)*base72 + (1031878884611/854900000000000000000000000 : ℝ)*base74 + (4930356545099537643/427450000000000000000000000000000 : ℝ)*base76 + (4289606289768487643/427450000000000000000000000000000 : ℝ)*base78 + (3497508375656087643/427450000000000000000000000000000 : ℝ)*base80 + (716416076211/1068625000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (212429/39062500000000000000 : ℝ)*base89 + (212429/39062500000000000000 : ℝ)*base91 + (212429/39062500000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (30840786731259565907272376643/4274500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1093260149/100000000000000 : ℝ)*(base19) + (1043880473/100000000000000 : ℝ)*(base23) + (37404891/25000000000000 : ℝ)*(upper3) + (324989/50000000000000 : ℝ)*(lower4) + (19011859/10000000000000 : ℝ)*(upper5) + (2462863280563313/100000000000000 : ℝ)*(major0) + (2462863280563313/100000000000000 : ℝ)*(major1) + (2462863280563313/100000000000000 : ℝ)*(major2) + (1910161629/20000000000000 : ℝ)*(sp1) + (12319899627/100000000000000 : ℝ)*(sp2) + (1753163372851537/50000000000000 : ℝ)*(sp4) + (175315805081739/5000000000000 : ℝ)*(sp5) + (1753156690961487/50000000000000 : ℝ)*(sp6) + (177424946865181/12500000000000 : ℝ)*(sp7) + (177424946865181/12500000000000 : ℝ)*(f.failure) + (1753163372851537/50000000000000 : ℝ)*(f.sum) + (304773106275109/42745000000000000000000000000 : ℝ)*base66 + (11855832799344858881/8549000000000000000000000000000000 : ℝ)*base67 + (12624593982327141119/8549000000000000000000000000000000 : ℝ)*base70 + (61924085746231141119/8549000000000000000000000000000000 : ℝ)*base72 + (60780595588811/42745000000000000000000000000 : ℝ)*base73 + (57430477552068141119/8549000000000000000000000000000000 : ℝ)*base76 + (48718450379004141119/8549000000000000000000000000000000 : ℝ)*base78 + (20962950220667858881/8549000000000000000000000000000000 : ℝ)*base79 + (84915907036289/42745000000000000000000000000 : ℝ)*base82 + (2918591/312500000000000000000 : ℝ)*base89 + (2918591/312500000000000000000 : ℝ)*base91 + (2918591/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1614_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43378611/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (71/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9201/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10333/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16477/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1614_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1614_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43378611/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10333/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16477/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1614_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1614_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1614_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43378611/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10333/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16477/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1614_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

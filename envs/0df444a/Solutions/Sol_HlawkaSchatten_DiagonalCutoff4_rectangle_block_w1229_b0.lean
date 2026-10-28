-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1229_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:14:08.712823+00:00
-- url     : https://prove2.me/submissions/20f5e6ea-3cb7-4bb4-940f-2e7202736182

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
theorem support_rectangle_w1229_s0_0 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1864577969/10000000000 : ℝ)*x 0 + (6034440081/10000000000 : ℝ)*x 1 + (479137581/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1864577969/10000000000 : ℝ)^4211 ≤ (10869616227423/100000000000000 : ℝ)^3187 := by
    have hnat : (1864577969 : ℕ)^4211*100000000000000^3187 ≤ 10869616227423^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1864577969 10000000000 10869616227423 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6034440081/10000000000 : ℝ)^4211 ≤ (25652192002079/50000000000000 : ℝ)^3187 := by
    have hnat : (6034440081 : ℕ)^4211*50000000000000^3187 ≤ 25652192002079^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6034440081 10000000000 25652192002079 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (479137581/1000000000 : ℝ)^4211 ≤ (7565199949013/20000000000000 : ℝ)^3187 := by
    have hnat : (479137581 : ℕ)^4211*20000000000000^3187 ≤ 7565199949013^3187*1000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      479137581 1000000000 7565199949013 20000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1864577969/10000000000 : ℝ), (6034440081/10000000000 : ℝ), (479137581/1000000000 : ℝ)] ![(10869616227423/100000000000000 : ℝ), (25652192002079/50000000000000 : ℝ), (7565199949013/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1864577969/10000000000 : ℝ)|^4211 ≤ (10869616227423/100000000000000 : ℝ)^3187
        have hw : |(-1864577969/10000000000 : ℝ)|=(1864577969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6034440081/10000000000 : ℝ)|^4211 ≤ (25652192002079/50000000000000 : ℝ)^3187
        have hw : |(6034440081/10000000000 : ℝ)|=(6034440081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(479137581/1000000000 : ℝ)|^4211 ≤ (7565199949013/20000000000000 : ℝ)^3187
        have hw : |(479137581/1000000000 : ℝ)|=(479137581/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_s0_1 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2755945947/5000000000 : ℝ)*x 0 + (-2575559477/10000000000 : ℝ)*x 1 + (2395687881/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2755945947/5000000000 : ℝ)^4211 ≤ (22758793515991/50000000000000 : ℝ)^3187 := by
    have hnat : (2755945947 : ℕ)^4211*50000000000000^3187 ≤ 22758793515991^3187*5000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2755945947 5000000000 22758793515991 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2575559477/10000000000 : ℝ)^4211 ≤ (16656413706297/100000000000000 : ℝ)^3187 := by
    have hnat : (2575559477 : ℕ)^4211*100000000000000^3187 ≤ 16656413706297^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2575559477 10000000000 16656413706297 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2395687881/5000000000 : ℝ)^4211 ≤ (2364124952773/6250000000000 : ℝ)^3187 := by
    have hnat : (2395687881 : ℕ)^4211*6250000000000^3187 ≤ 2364124952773^3187*5000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2395687881 5000000000 2364124952773 6250000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2755945947/5000000000 : ℝ), (-2575559477/10000000000 : ℝ), (2395687881/5000000000 : ℝ)] ![(22758793515991/50000000000000 : ℝ), (16656413706297/100000000000000 : ℝ), (2364124952773/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2755945947/5000000000 : ℝ)|^4211 ≤ (22758793515991/50000000000000 : ℝ)^3187
        have hw : |(2755945947/5000000000 : ℝ)|=(2755945947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2575559477/10000000000 : ℝ)|^4211 ≤ (16656413706297/100000000000000 : ℝ)^3187
        have hw : |(-2575559477/10000000000 : ℝ)|=(2575559477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2395687881/5000000000 : ℝ)|^4211 ≤ (2364124952773/6250000000000 : ℝ)^3187
        have hw : |(2395687881/5000000000 : ℝ)|=(2395687881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_s0_2 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (8612331/15625000 : ℝ)*x 0 + (299460989/625000000 : ℝ)*x 1 + (-2575559471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8612331/15625000 : ℝ)^4211 ≤ (11379396610691/25000000000000 : ℝ)^3187 := by
    have hnat : (8612331 : ℕ)^4211*25000000000000^3187 ≤ 11379396610691^3187*15625000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8612331 15625000 11379396610691 25000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (299460989/625000000 : ℝ)^4211 ≤ (37825999891101/100000000000000 : ℝ)^3187 := by
    have hnat : (299460989 : ℕ)^4211*100000000000000^3187 ≤ 37825999891101^3187*625000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299460989 625000000 37825999891101 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2575559471/10000000000 : ℝ)^4211 ≤ (16656413655027/100000000000000 : ℝ)^3187 := by
    have hnat : (2575559471 : ℕ)^4211*100000000000000^3187 ≤ 16656413655027^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2575559471 10000000000 16656413655027 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8612331/15625000 : ℝ), (299460989/625000000 : ℝ), (-2575559471/10000000000 : ℝ)] ![(11379396610691/25000000000000 : ℝ), (37825999891101/100000000000000 : ℝ), (16656413655027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8612331/15625000 : ℝ)|^4211 ≤ (11379396610691/25000000000000 : ℝ)^3187
        have hw : |(8612331/15625000 : ℝ)|=(8612331/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(299460989/625000000 : ℝ)|^4211 ≤ (37825999891101/100000000000000 : ℝ)^3187
        have hw : |(299460989/625000000 : ℝ)|=(299460989/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2575559471/10000000000 : ℝ)|^4211 ≤ (16656413655027/100000000000000 : ℝ)^3187
        have hw : |(-2575559471/10000000000 : ℝ)|=(2575559471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_s0_3 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4194044467/10000000000 : ℝ)*x 0 + (623477169/2000000000 : ℝ)*x 1 + (1126540217/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4194044467/10000000000 : ℝ)^4211 ≤ (31723640696787/100000000000000 : ℝ)^3187 := by
    have hnat : (4194044467 : ℕ)^4211*100000000000000^3187 ≤ 31723640696787^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4194044467 10000000000 31723640696787 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (623477169/2000000000 : ℝ)^4211 ≤ (10717976136049/50000000000000 : ℝ)^3187 := by
    have hnat : (623477169 : ℕ)^4211*50000000000000^3187 ≤ 10717976136049^3187*2000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      623477169 2000000000 10717976136049 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1126540217/2000000000 : ℝ)^4211 ≤ (23420203506291/50000000000000 : ℝ)^3187 := by
    have hnat : (1126540217 : ℕ)^4211*50000000000000^3187 ≤ 23420203506291^3187*2000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126540217 2000000000 23420203506291 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4194044467/10000000000 : ℝ), (623477169/2000000000 : ℝ), (1126540217/2000000000 : ℝ)] ![(31723640696787/100000000000000 : ℝ), (10717976136049/50000000000000 : ℝ), (23420203506291/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4194044467/10000000000 : ℝ)|^4211 ≤ (31723640696787/100000000000000 : ℝ)^3187
        have hw : |(4194044467/10000000000 : ℝ)|=(4194044467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(623477169/2000000000 : ℝ)|^4211 ≤ (10717976136049/50000000000000 : ℝ)^3187
        have hw : |(623477169/2000000000 : ℝ)|=(623477169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1126540217/2000000000 : ℝ)|^4211 ≤ (23420203506291/50000000000000 : ℝ)^3187
        have hw : |(1126540217/2000000000 : ℝ)|=(1126540217/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_s0_4 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-467368127/2500000000 : ℝ)*x 0 + (4823395769/10000000000 : ℝ)*x 1 + (3000644407/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (467368127/2500000000 : ℝ)^4211 ≤ (10907332749171/100000000000000 : ℝ)^3187 := by
    have hnat : (467368127 : ℕ)^4211*100000000000000^3187 ≤ 10907332749171^3187*2500000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467368127 2500000000 10907332749171 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4823395769/10000000000 : ℝ)^4211 ≤ (38160363690657/100000000000000 : ℝ)^3187 := by
    have hnat : (4823395769 : ℕ)^4211*100000000000000^3187 ≤ 38160363690657^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4823395769 10000000000 38160363690657 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3000644407/5000000000 : ℝ)^4211 ≤ (636653794303/1250000000000 : ℝ)^3187 := by
    have hnat : (3000644407 : ℕ)^4211*1250000000000^3187 ≤ 636653794303^3187*5000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3000644407 5000000000 636653794303 1250000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-467368127/2500000000 : ℝ), (4823395769/10000000000 : ℝ), (3000644407/5000000000 : ℝ)] ![(10907332749171/100000000000000 : ℝ), (38160363690657/100000000000000 : ℝ), (636653794303/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-467368127/2500000000 : ℝ)|^4211 ≤ (10907332749171/100000000000000 : ℝ)^3187
        have hw : |(-467368127/2500000000 : ℝ)|=(467368127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4823395769/10000000000 : ℝ)|^4211 ≤ (38160363690657/100000000000000 : ℝ)^3187
        have hw : |(4823395769/10000000000 : ℝ)|=(4823395769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3000644407/5000000000 : ℝ)|^4211 ≤ (636653794303/1250000000000 : ℝ)^3187
        have hw : |(3000644407/5000000000 : ℝ)|=(3000644407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_s0_5 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5173727193/10000000000 : ℝ)*x 0 + (-1365644397/10000000000 : ℝ)*x 1 + (600129093/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5173727193/10000000000 : ℝ)^4211 ≤ (41864612899387/100000000000000 : ℝ)^3187 := by
    have hnat : (5173727193 : ℕ)^4211*100000000000000^3187 ≤ 41864612899387^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173727193 10000000000 41864612899387 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1365644397/10000000000 : ℝ)^4211 ≤ (7203059823251/100000000000000 : ℝ)^3187 := by
    have hnat : (1365644397 : ℕ)^4211*100000000000000^3187 ≤ 7203059823251^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365644397 10000000000 7203059823251 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (600129093/1000000000 : ℝ)^4211 ≤ (50932327272597/100000000000000 : ℝ)^3187 := by
    have hnat : (600129093 : ℕ)^4211*100000000000000^3187 ≤ 50932327272597^3187*1000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      600129093 1000000000 50932327272597 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5173727193/10000000000 : ℝ), (-1365644397/10000000000 : ℝ), (600129093/1000000000 : ℝ)] ![(41864612899387/100000000000000 : ℝ), (7203059823251/100000000000000 : ℝ), (50932327272597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5173727193/10000000000 : ℝ)|^4211 ≤ (41864612899387/100000000000000 : ℝ)^3187
        have hw : |(5173727193/10000000000 : ℝ)|=(5173727193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1365644397/10000000000 : ℝ)|^4211 ≤ (7203059823251/100000000000000 : ℝ)^3187
        have hw : |(-1365644397/10000000000 : ℝ)|=(1365644397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(600129093/1000000000 : ℝ)|^4211 ≤ (50932327272597/100000000000000 : ℝ)^3187
        have hw : |(600129093/1000000000 : ℝ)|=(600129093/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_s0_6 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5173727973/10000000000 : ℝ)*x 0 + (6001289323/10000000000 : ℝ)*x 1 + (-170705723/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5173727973/10000000000 : ℝ)^4211 ≤ (41864621238913/100000000000000 : ℝ)^3187 := by
    have hnat : (5173727973 : ℕ)^4211*100000000000000^3187 ≤ 41864621238913^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173727973 10000000000 41864621238913 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6001289323/10000000000 : ℝ)^4211 ≤ (25466154626027/50000000000000 : ℝ)^3187 := by
    have hnat : (6001289323 : ℕ)^4211*50000000000000^3187 ≤ 25466154626027^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6001289323 10000000000 25466154626027 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (170705723/1250000000 : ℝ)^4211 ≤ (288122779581/4000000000000 : ℝ)^3187 := by
    have hnat : (170705723 : ℕ)^4211*4000000000000^3187 ≤ 288122779581^3187*1250000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170705723 1250000000 288122779581 4000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5173727973/10000000000 : ℝ), (6001289323/10000000000 : ℝ), (-170705723/1250000000 : ℝ)] ![(41864621238913/100000000000000 : ℝ), (25466154626027/50000000000000 : ℝ), (288122779581/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5173727973/10000000000 : ℝ)|^4211 ≤ (41864621238913/100000000000000 : ℝ)^3187
        have hw : |(5173727973/10000000000 : ℝ)|=(5173727973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6001289323/10000000000 : ℝ)|^4211 ≤ (25466154626027/50000000000000 : ℝ)^3187
        have hw : |(6001289323/10000000000 : ℝ)|=(6001289323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-170705723/1250000000 : ℝ)|^4211 ≤ (288122779581/4000000000000 : ℝ)^3187
        have hw : |(-170705723/1250000000 : ℝ)|=(170705723/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_s0_7 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4203948547/10000000000 : ℝ)*x 0 + (5567914101/10000000000 : ℝ)*x 1 + (3184461293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4203948547/10000000000 : ℝ)^4211 ≤ (31822662755383/100000000000000 : ℝ)^3187 := by
    have hnat : (4203948547 : ℕ)^4211*100000000000000^3187 ≤ 31822662755383^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4203948547 10000000000 31822662755383 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5567914101/10000000000 : ℝ)^4211 ≤ (23064932669219/50000000000000 : ℝ)^3187 := by
    have hnat : (5567914101 : ℕ)^4211*50000000000000^3187 ≤ 23064932669219^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5567914101 10000000000 23064932669219 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3184461293/10000000000 : ℝ)^4211 ≤ (22047471897403/100000000000000 : ℝ)^3187 := by
    have hnat : (3184461293 : ℕ)^4211*100000000000000^3187 ≤ 22047471897403^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3184461293 10000000000 22047471897403 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4203948547/10000000000 : ℝ), (5567914101/10000000000 : ℝ), (3184461293/10000000000 : ℝ)] ![(31822662755383/100000000000000 : ℝ), (23064932669219/50000000000000 : ℝ), (22047471897403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4203948547/10000000000 : ℝ)|^4211 ≤ (31822662755383/100000000000000 : ℝ)^3187
        have hw : |(4203948547/10000000000 : ℝ)|=(4203948547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5567914101/10000000000 : ℝ)|^4211 ≤ (23064932669219/50000000000000 : ℝ)^3187
        have hw : |(5567914101/10000000000 : ℝ)|=(5567914101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3184461293/10000000000 : ℝ)|^4211 ≤ (22047471897403/100000000000000 : ℝ)^3187
        have hw : |(3184461293/10000000000 : ℝ)|=(3184461293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1229_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151173987/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (383/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5497/20000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8421/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8421 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8421*1^2048 ≤ 0^2048*1^8421 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8421 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8421 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8421/2048 : ℝ) ≤ (577675238487856739/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8421 ≤ (577675238487856739/25000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8421*25000000000000000000^2048 ≤ 577675238487856739^2048*5^8421 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 577675238487856739 25000000000000000000 8421 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (577675238487856739/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8421 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8421/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8421 := by
      have hnat : (1 : ℕ)^2048*1^8421 ≤ 1^8421*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8421 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25577675238487856739/25000000000000000000 : ℝ) ≤ (10055711778443741/10000000000000000 : ℝ) ^ (8421/2048 : ℝ) := by
    have hpowers : (25577675238487856739/25000000000000000000 : ℝ)^2048 ≤ (10055711778443741/10000000000000000 : ℝ)^8421 := by
      have hnat : (25577675238487856739 : ℕ)^2048*10000000000000000^8421 ≤ 10055711778443741^8421*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25577675238487856739 25000000000000000000 10055711778443741 10000000000000000 2048 8421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10055711778443741/10000000000000000 : ℝ)) (X := (25577675238487856739/25000000000000000000 : ℝ)) (by norm_num) 8421 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (13077675238487856739/12500000000000000000 : ℝ) ≤ (5055711778443741/5000000000000000 : ℝ) ^ (8421/2048 : ℝ) := by
    have hpowers : (13077675238487856739/12500000000000000000 : ℝ)^2048 ≤ (5055711778443741/5000000000000000 : ℝ)^8421 := by
      have hnat : (13077675238487856739 : ℕ)^2048*5000000000000000^8421 ≤ 5055711778443741^8421*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13077675238487856739 12500000000000000000 5055711778443741 5000000000000000 2048 8421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5055711778443741/5000000000000000 : ℝ)) (X := (13077675238487856739/12500000000000000000 : ℝ)) (by norm_num) 8421 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(55711778443741/4000000000000000 : ℝ)*(0 : ℝ))^(8421/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(55711778443741/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(577675238487856739/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(55711778443741/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8421/2048 : ℝ) := by
    rw [show (1 : ℝ)+(55711778443741/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10055711778443741/10000000000000000 : ℝ) by norm_num, show 1+(577675238487856739/25000000000000000000 : ℝ)+(0 : ℝ)=(25577675238487856739/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(577675238487856739/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(55711778443741/4000000000000000 : ℝ)*(2/5 : ℝ))^(8421/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(55711778443741/4000000000000000 : ℝ)*(2/5 : ℝ)=(5055711778443741/5000000000000000 : ℝ) by norm_num, show 1+2*(577675238487856739/25000000000000000000 : ℝ)=(13077675238487856739/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(55711778443741/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8421/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (55711778443741/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(55711778443741/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8421/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (55711778443741/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(55711778443741/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8421/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (55711778443741/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1864577969/10000000000 : ℝ)*X 0 0+(6034440081/10000000000 : ℝ)*X 0 1+(479137581/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2755945947/5000000000 : ℝ)*X 1 0+(-2575559477/10000000000 : ℝ)*X 1 1+(2395687881/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((8612331/15625000 : ℝ)*X 2 0+(299460989/625000000 : ℝ)*X 2 1+(-2575559471/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4194044467/10000000000 : ℝ)*X 0 0+(623477169/2000000000 : ℝ)*X 0 1+(1126540217/2000000000 : ℝ)*X 0 2+(4194044467/10000000000 : ℝ)*X 1 0+(623477169/2000000000 : ℝ)*X 1 1+(1126540217/2000000000 : ℝ)*X 1 2+(4194044467/10000000000 : ℝ)*X 2 0+(623477169/2000000000 : ℝ)*X 2 1+(1126540217/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-467368127/2500000000 : ℝ)*X 0 0+(4823395769/10000000000 : ℝ)*X 0 1+(3000644407/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5173727193/10000000000 : ℝ)*X 1 0+(-1365644397/10000000000 : ℝ)*X 1 1+(600129093/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5173727973/10000000000 : ℝ)*X 2 0+(6001289323/10000000000 : ℝ)*X 2 1+(-170705723/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4203948547/10000000000 : ℝ)*X 0 0+(5567914101/10000000000 : ℝ)*X 0 1+(3184461293/10000000000 : ℝ)*X 0 2+(4203948547/10000000000 : ℝ)*X 1 0+(5567914101/10000000000 : ℝ)*X 1 1+(3184461293/10000000000 : ℝ)*X 1 2+(4203948547/10000000000 : ℝ)*X 2 0+(5567914101/10000000000 : ℝ)*X 2 1+(3184461293/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (327491311059973575739719/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (39008201/50000000000000 : ℝ)*(base1) + (1599359069/100000000000000 : ℝ)*(base19) + (741627127/50000000000000 : ℝ)*(base23) + (21644683/20000000000000 : ℝ)*(base24) + (45231553/12500000000000 : ℝ)*(upper3) + (150255213133647/25000000000000 : ℝ)*(major0) + (150255213133647/25000000000000 : ℝ)*(major1) + (150255213133647/25000000000000 : ℝ)*(major2) + (100558631015299/12500000000000 : ℝ)*(sp0) + (201117731080271/25000000000000 : ℝ)*(sp1) + (160894186440497/20000000000000 : ℝ)*(sp2) + (99391527396941/25000000000000 : ℝ)*(sp3) + (3553574163/100000000000000 : ℝ)*(sp4) + (693864327/25000000000000 : ℝ)*(sp7) + (198784481530737/50000000000000 : ℝ)*(f.failure) + (402236261840077/50000000000000 : ℝ)*(f.sum) + (109266526946573/50000000000000000000000000000 : ℝ)*base66 + (530944424953427/100000000000000000000000000000 : ℝ)*base67 + (428030165053427/100000000000000000000000000000 : ℝ)*base69 + (341012867653427/100000000000000000000000000000 : ℝ)*base71 + (101893877346573/50000000000000000000000000000 : ℝ)*base74 + (517658584453427/100000000000000000000000000000 : ℝ)*base75 + (346379937253427/100000000000000000000000000000 : ℝ)*base77 + (167196829146573/100000000000000000000000000000 : ℝ)*base80 + (36824616203427/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (24661581/5000000000000000000000 : ℝ)*base90 + (24661581/5000000000000000000000 : ℝ)*base92 + (24661581/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1118178831651793875249141/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (72498143/100000000000000 : ℝ)*(base1) + (1445247243/100000000000000 : ℝ)*(base19) + (785727233/50000000000000 : ℝ)*(base23) + (81999359/25000000000000 : ℝ)*(upper3) + (14105171/50000000000000 : ℝ)*(upper5) + (634266048205489/100000000000000 : ℝ)*(major0) + (634266048205489/100000000000000 : ℝ)*(major1) + (634266048205489/100000000000000 : ℝ)*(major2) + (1595355861/50000000000000 : ℝ)*(sp1) + (790852673/25000000000000 : ℝ)*(sp2) + (848971672738513/100000000000000 : ℝ)*(sp4) + (424483482140703/50000000000000 : ℝ)*(sp5) + (848966865375213/100000000000000 : ℝ)*(sp6) + (209780118654659/50000000000000 : ℝ)*(sp7) + (20978015490373/5000000000000 : ℝ)*(f.failure) + (848971600240371/100000000000000 : ℝ)*(f.sum) + (541825874505651/200000000000000000000000000000 : ℝ)*base66 + (4743331652105651/400000000000000000000000000000 : ℝ)*base68 + (770797491494349/400000000000000000000000000000 : ℝ)*base69 + (4289840114905651/400000000000000000000000000000 : ℝ)*base72 + (1204678114505651/200000000000000000000000000000 : ℝ)*base74 + (2149856973305651/400000000000000000000000000000 : ℝ)*base76 + (3463212796105651/400000000000000000000000000000 : ℝ)*base78 + (4323375456105651/400000000000000000000000000000 : ℝ)*base80 + (555163743894349/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1527151/500000000000000000000 : ℝ)*base89 + (1527151/500000000000000000000 : ℝ)*base91 + (1527151/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1229_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151173987/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (383/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5497/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1229_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1229_s1_0 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2062933761/10000000000 : ℝ)*x 0 + (5678884357/10000000000 : ℝ)*x 1 + (1254990339/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2062933761/10000000000 : ℝ)^4211 ≤ (3105744883759/25000000000000 : ℝ)^3187 := by
    have hnat : (2062933761 : ℕ)^4211*25000000000000^3187 ≤ 3105744883759^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062933761 10000000000 3105744883759 25000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5678884357/10000000000 : ℝ)^4211 ≤ (47348522529421/100000000000000 : ℝ)^3187 := by
    have hnat : (5678884357 : ℕ)^4211*100000000000000^3187 ≤ 47348522529421^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5678884357 10000000000 47348522529421 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1254990339/2500000000 : ℝ)^4211 ≤ (20114248963193/50000000000000 : ℝ)^3187 := by
    have hnat : (1254990339 : ℕ)^4211*50000000000000^3187 ≤ 20114248963193^3187*2500000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1254990339 2500000000 20114248963193 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2062933761/10000000000 : ℝ), (5678884357/10000000000 : ℝ), (1254990339/2500000000 : ℝ)] ![(3105744883759/25000000000000 : ℝ), (47348522529421/100000000000000 : ℝ), (20114248963193/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2062933761/10000000000 : ℝ)|^4211 ≤ (3105744883759/25000000000000 : ℝ)^3187
        have hw : |(-2062933761/10000000000 : ℝ)|=(2062933761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5678884357/10000000000 : ℝ)|^4211 ≤ (47348522529421/100000000000000 : ℝ)^3187
        have hw : |(5678884357/10000000000 : ℝ)|=(5678884357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1254990339/2500000000 : ℝ)|^4211 ≤ (20114248963193/50000000000000 : ℝ)^3187
        have hw : |(1254990339/2500000000 : ℝ)|=(1254990339/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_s1_1 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1353591383/2500000000 : ℝ)*x 0 + (-604247543/2500000000 : ℝ)*x 1 + (313747589/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1353591383/2500000000 : ℝ)^4211 ≤ (44456471956811/100000000000000 : ℝ)^3187 := by
    have hnat : (1353591383 : ℕ)^4211*100000000000000^3187 ≤ 44456471956811^3187*2500000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353591383 2500000000 44456471956811 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (604247543/2500000000 : ℝ)^4211 ≤ (7657514693701/50000000000000 : ℝ)^3187 := by
    have hnat : (604247543 : ℕ)^4211*50000000000000^3187 ≤ 7657514693701^3187*2500000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      604247543 2500000000 7657514693701 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (313747589/625000000 : ℝ)^4211 ≤ (40228498646407/100000000000000 : ℝ)^3187 := by
    have hnat : (313747589 : ℕ)^4211*100000000000000^3187 ≤ 40228498646407^3187*625000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      313747589 625000000 40228498646407 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1353591383/2500000000 : ℝ), (-604247543/2500000000 : ℝ), (313747589/625000000 : ℝ)] ![(44456471956811/100000000000000 : ℝ), (7657514693701/50000000000000 : ℝ), (40228498646407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1353591383/2500000000 : ℝ)|^4211 ≤ (44456471956811/100000000000000 : ℝ)^3187
        have hw : |(1353591383/2500000000 : ℝ)|=(1353591383/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-604247543/2500000000 : ℝ)|^4211 ≤ (7657514693701/50000000000000 : ℝ)^3187
        have hw : |(-604247543/2500000000 : ℝ)|=(604247543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(313747589/625000000 : ℝ)|^4211 ≤ (40228498646407/100000000000000 : ℝ)^3187
        have hw : |(313747589/625000000 : ℝ)|=(313747589/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_s1_2 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5414365609/10000000000 : ℝ)*x 0 + (2509980691/5000000000 : ℝ)*x 1 + (-604247531/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5414365609/10000000000 : ℝ)^4211 ≤ (22228236396093/50000000000000 : ℝ)^3187 := by
    have hnat : (5414365609 : ℕ)^4211*50000000000000^3187 ≤ 22228236396093^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414365609 10000000000 22228236396093 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2509980691/5000000000 : ℝ)^4211 ≤ (5028562275211/12500000000000 : ℝ)^3187 := by
    have hnat : (2509980691 : ℕ)^4211*12500000000000^3187 ≤ 5028562275211^3187*5000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2509980691 5000000000 5028562275211 12500000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (604247531/2500000000 : ℝ)^4211 ≤ (15315028985531/100000000000000 : ℝ)^3187 := by
    have hnat : (604247531 : ℕ)^4211*100000000000000^3187 ≤ 15315028985531^3187*2500000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      604247531 2500000000 15315028985531 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5414365609/10000000000 : ℝ), (2509980691/5000000000 : ℝ), (-604247531/2500000000 : ℝ)] ![(22228236396093/50000000000000 : ℝ), (5028562275211/12500000000000 : ℝ), (15315028985531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5414365609/10000000000 : ℝ)|^4211 ≤ (22228236396093/50000000000000 : ℝ)^3187
        have hw : |(5414365609/10000000000 : ℝ)|=(5414365609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2509980691/5000000000 : ℝ)|^4211 ≤ (5028562275211/12500000000000 : ℝ)^3187
        have hw : |(2509980691/5000000000 : ℝ)|=(2509980691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-604247531/2500000000 : ℝ)|^4211 ≤ (15315028985531/100000000000000 : ℝ)^3187
        have hw : |(-604247531/2500000000 : ℝ)|=(604247531/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_s1_3 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1077495529/2500000000 : ℝ)*x 0 + (1846545097/5000000000 : ℝ)*x 1 + (5026408159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077495529/2500000000 : ℝ)^4211 ≤ (1644373624011/5000000000000 : ℝ)^3187 := by
    have hnat : (1077495529 : ℕ)^4211*5000000000000^3187 ≤ 1644373624011^3187*2500000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077495529 2500000000 1644373624011 5000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1846545097/5000000000 : ℝ)^4211 ≤ (3351969148271/12500000000000 : ℝ)^3187 := by
    have hnat : (1846545097 : ℕ)^4211*12500000000000^3187 ≤ 3351969148271^3187*5000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1846545097 5000000000 3351969148271 12500000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5026408159/10000000000 : ℝ)^4211 ≤ (40296774322091/100000000000000 : ℝ)^3187 := by
    have hnat : (5026408159 : ℕ)^4211*100000000000000^3187 ≤ 40296774322091^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5026408159 10000000000 40296774322091 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1077495529/2500000000 : ℝ), (1846545097/5000000000 : ℝ), (5026408159/10000000000 : ℝ)] ![(1644373624011/5000000000000 : ℝ), (3351969148271/12500000000000 : ℝ), (40296774322091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1077495529/2500000000 : ℝ)|^4211 ≤ (1644373624011/5000000000000 : ℝ)^3187
        have hw : |(1077495529/2500000000 : ℝ)|=(1077495529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1846545097/5000000000 : ℝ)|^4211 ≤ (3351969148271/12500000000000 : ℝ)^3187
        have hw : |(1846545097/5000000000 : ℝ)|=(1846545097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5026408159/10000000000 : ℝ)|^4211 ≤ (40296774322091/100000000000000 : ℝ)^3187
        have hw : |(5026408159/10000000000 : ℝ)|=(5026408159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_s1_4 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-257953301/1250000000 : ℝ)*x 0 + (1005732273/2000000000 : ℝ)*x 1 + (5670017511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (257953301/1250000000 : ℝ)^4211 ≤ (621424557611/5000000000000 : ℝ)^3187 := by
    have hnat : (257953301 : ℕ)^4211*5000000000000^3187 ≤ 621424557611^3187*1250000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257953301 1250000000 621424557611 5000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1005732273/2000000000 : ℝ)^4211 ≤ (126002012727/312500000000 : ℝ)^3187 := by
    have hnat : (1005732273 : ℕ)^4211*312500000000^3187 ≤ 126002012727^3187*2000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005732273 2000000000 126002012727 312500000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5670017511/10000000000 : ℝ)^4211 ≤ (1890034590759/4000000000000 : ℝ)^3187 := by
    have hnat : (5670017511 : ℕ)^4211*4000000000000^3187 ≤ 1890034590759^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5670017511 10000000000 1890034590759 4000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-257953301/1250000000 : ℝ), (1005732273/2000000000 : ℝ), (5670017511/10000000000 : ℝ)] ![(621424557611/5000000000000 : ℝ), (126002012727/312500000000 : ℝ), (1890034590759/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-257953301/1250000000 : ℝ)|^4211 ≤ (621424557611/5000000000000 : ℝ)^3187
        have hw : |(-257953301/1250000000 : ℝ)|=(257953301/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1005732273/2000000000 : ℝ)|^4211 ≤ (126002012727/312500000000 : ℝ)^3187
        have hw : |(1005732273/2000000000 : ℝ)|=(1005732273/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5670017511/10000000000 : ℝ)|^4211 ≤ (1890034590759/4000000000000 : ℝ)^3187
        have hw : |(5670017511/10000000000 : ℝ)|=(5670017511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_s1_5 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (104894237/200000000 : ℝ)*x 0 + (-883466693/5000000000 : ℝ)*x 1 + (88594029/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (104894237/200000000 : ℝ)^4211 ≤ (8525045440149/20000000000000 : ℝ)^3187 := by
    have hnat : (104894237 : ℕ)^4211*20000000000000^3187 ≤ 8525045440149^3187*200000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104894237 200000000 8525045440149 20000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (883466693/5000000000 : ℝ)^4211 ≤ (5061952109761/50000000000000 : ℝ)^3187 := by
    have hnat : (883466693 : ℕ)^4211*50000000000000^3187 ≤ 5061952109761^3187*5000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      883466693 5000000000 5061952109761 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (88594029/156250000 : ℝ)^4211 ≤ (23625434283893/50000000000000 : ℝ)^3187 := by
    have hnat : (88594029 : ℕ)^4211*50000000000000^3187 ≤ 23625434283893^3187*156250000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88594029 156250000 23625434283893 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(104894237/200000000 : ℝ), (-883466693/5000000000 : ℝ), (88594029/156250000 : ℝ)] ![(8525045440149/20000000000000 : ℝ), (5061952109761/50000000000000 : ℝ), (23625434283893/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(104894237/200000000 : ℝ)|^4211 ≤ (8525045440149/20000000000000 : ℝ)^3187
        have hw : |(104894237/200000000 : ℝ)|=(104894237/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-883466693/5000000000 : ℝ)|^4211 ≤ (5061952109761/50000000000000 : ℝ)^3187
        have hw : |(-883466693/5000000000 : ℝ)|=(883466693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(88594029/156250000 : ℝ)|^4211 ≤ (23625434283893/50000000000000 : ℝ)^3187
        have hw : |(88594029/156250000 : ℝ)|=(88594029/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_s1_6 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5244712147/10000000000 : ℝ)*x 0 + (2835009301/5000000000 : ℝ)*x 1 + (-1766931879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5244712147/10000000000 : ℝ)^4211 ≤ (21312615195057/50000000000000 : ℝ)^3187 := by
    have hnat : (5244712147 : ℕ)^4211*50000000000000^3187 ≤ 21312615195057^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244712147 10000000000 21312615195057 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2835009301/5000000000 : ℝ)^4211 ≤ (23625438391013/50000000000000 : ℝ)^3187 := by
    have hnat : (2835009301 : ℕ)^4211*50000000000000^3187 ≤ 23625438391013^3187*5000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2835009301 5000000000 23625438391013 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1766931879/10000000000 : ℝ)^4211 ≤ (1012389281061/10000000000000 : ℝ)^3187 := by
    have hnat : (1766931879 : ℕ)^4211*10000000000000^3187 ≤ 1012389281061^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1766931879 10000000000 1012389281061 10000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5244712147/10000000000 : ℝ), (2835009301/5000000000 : ℝ), (-1766931879/10000000000 : ℝ)] ![(21312615195057/50000000000000 : ℝ), (23625438391013/50000000000000 : ℝ), (1012389281061/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5244712147/10000000000 : ℝ)|^4211 ≤ (21312615195057/50000000000000 : ℝ)^3187
        have hw : |(5244712147/10000000000 : ℝ)|=(5244712147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2835009301/5000000000 : ℝ)|^4211 ≤ (23625438391013/50000000000000 : ℝ)^3187
        have hw : |(2835009301/5000000000 : ℝ)|=(2835009301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1766931879/10000000000 : ℝ)|^4211 ≤ (1012389281061/10000000000000 : ℝ)^3187
        have hw : |(-1766931879/10000000000 : ℝ)|=(1766931879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_s1_7 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (107784547/250000000 : ℝ)*x 0 + (1001760923/2000000000 : ℝ)*x 1 + (74220609/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107784547/250000000 : ℝ)^4211 ≤ (8225396502831/25000000000000 : ℝ)^3187 := by
    have hnat : (107784547 : ℕ)^4211*25000000000000^3187 ≤ 8225396502831^3187*250000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107784547 250000000 8225396502831 25000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1001760923/2000000000 : ℝ)^4211 ≤ (40110406381793/100000000000000 : ℝ)^3187 := by
    have hnat : (1001760923 : ℕ)^4211*100000000000000^3187 ≤ 40110406381793^3187*2000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001760923 2000000000 40110406381793 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (74220609/200000000 : ℝ)^4211 ≤ (13494003793529/50000000000000 : ℝ)^3187 := by
    have hnat : (74220609 : ℕ)^4211*50000000000000^3187 ≤ 13494003793529^3187*200000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74220609 200000000 13494003793529 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107784547/250000000 : ℝ), (1001760923/2000000000 : ℝ), (74220609/200000000 : ℝ)] ![(8225396502831/25000000000000 : ℝ), (40110406381793/100000000000000 : ℝ), (13494003793529/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107784547/250000000 : ℝ)|^4211 ≤ (8225396502831/25000000000000 : ℝ)^3187
        have hw : |(107784547/250000000 : ℝ)|=(107784547/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1001760923/2000000000 : ℝ)|^4211 ≤ (40110406381793/100000000000000 : ℝ)^3187
        have hw : |(1001760923/2000000000 : ℝ)|=(1001760923/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(74220609/200000000 : ℝ)|^4211 ≤ (13494003793529/50000000000000 : ℝ)^3187
        have hw : |(74220609/200000000 : ℝ)|=(74220609/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1229_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151173987/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5497/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (383/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (6123/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10027/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5497/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (383/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5497/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (383/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5497/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (383/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5497/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (383/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5497/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (383/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5497/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (383/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (383/50000 : ℝ) ^ (8421/2048 : ℝ) ≤ (39936236797/20000000000000000000 : ℝ) := by
    have hpowers : (383/50000 : ℝ)^8421 ≤ (39936236797/20000000000000000000 : ℝ)^2048 := by
      have hnat : (383 : ℕ)^8421*20000000000000000000^2048 ≤ 39936236797^2048*50000^8421 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        383 50000 39936236797 20000000000000000000 8421 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (383/50000 : ℝ)) (X := (39936236797/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8421 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (5497/20000 : ℝ) ^ (8421/2048 : ℝ) ≤ (49392916053630029/10000000000000000000 : ℝ) := by
    have hpowers : (5497/20000 : ℝ)^8421 ≤ (49392916053630029/10000000000000000000 : ℝ)^2048 := by
      have hnat : (5497 : ℕ)^8421*10000000000000000000^2048 ≤ 49392916053630029^2048*20000^8421 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5497 20000 49392916053630029 10000000000000000000 8421 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5497/20000 : ℝ)) (X := (49392916053630029/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8421 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000000039936236797/10000000000000000000 : ℝ) ≤ (5000000004856277/5000000000000000 : ℝ) ^ (8421/2048 : ℝ) := by
    have hpowers : (10000000039936236797/10000000000000000000 : ℝ)^2048 ≤ (5000000004856277/5000000000000000 : ℝ)^8421 := by
      have hnat : (10000000039936236797 : ℕ)^2048*5000000000000000^8421 ≤ 5000000004856277^8421*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000000039936236797 10000000000000000000 5000000004856277 5000000000000000 2048 8421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000004856277/5000000000000000 : ℝ)) (X := (10000000039936236797/10000000000000000000 : ℝ)) (by norm_num) 8421 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (4019757174408699371/4000000000000000000 : ℝ) ≤ (2502997512573317/2500000000000000 : ℝ) ^ (8421/2048 : ℝ) := by
    have hpowers : (4019757174408699371/4000000000000000000 : ℝ)^2048 ≤ (2502997512573317/2500000000000000 : ℝ)^8421 := by
      have hnat : (4019757174408699371 : ℕ)^2048*2500000000000000^8421 ≤ 2502997512573317^8421*4000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4019757174408699371 4000000000000000000 2502997512573317 2500000000000000 2048 8421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2502997512573317/2500000000000000 : ℝ)) (X := (4019757174408699371/4000000000000000000 : ℝ)) (by norm_num) 8421 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (5049392916053630029/5000000000000000000 : ℝ) ≤ (5011990045436991/5000000000000000 : ℝ) ^ (8421/2048 : ℝ) := by
    have hpowers : (5049392916053630029/5000000000000000000 : ℝ)^2048 ≤ (5011990045436991/5000000000000000 : ℝ)^8421 := by
      have hnat : (5049392916053630029 : ℕ)^2048*5000000000000000^8421 ≤ 5011990045436991^8421*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5049392916053630029 5000000000000000000 5011990045436991 5000000000000000 2048 8421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5011990045436991/5000000000000000 : ℝ)) (X := (5049392916053630029/5000000000000000000 : ℝ)) (by norm_num) 8421 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(39936236797/20000000000000000000 : ℝ) ≤ ((19083687965524291177/19085000000000000000 : ℝ)+2*(856431470051/190850000000000 : ℝ)*(383/50000 : ℝ))^(8421/2048 : ℝ) := by
    rw [show (19083687965524291177/19085000000000000000 : ℝ)+2*(856431470051/190850000000000 : ℝ)*(383/50000 : ℝ)=(5000000004856277/5000000000000000 : ℝ) by norm_num, show 1+2*(39936236797/20000000000000000000 : ℝ)=(10000000039936236797/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(49392916053630029/10000000000000000000 : ℝ)+(39936236797/20000000000000000000 : ℝ) ≤ ((19083687965524291177/19085000000000000000 : ℝ)+(856431470051/190850000000000 : ℝ)*((5497/20000 : ℝ)+(383/50000 : ℝ)))^(8421/2048 : ℝ) := by
    rw [show (19083687965524291177/19085000000000000000 : ℝ)+(856431470051/190850000000000 : ℝ)*((5497/20000 : ℝ)+(383/50000 : ℝ))=(2502997512573317/2500000000000000 : ℝ) by norm_num, show 1+(49392916053630029/10000000000000000000 : ℝ)+(39936236797/20000000000000000000 : ℝ)=(4019757174408699371/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(49392916053630029/10000000000000000000 : ℝ) ≤ ((19083687965524291177/19085000000000000000 : ℝ)+2*(856431470051/190850000000000 : ℝ)*(5497/20000 : ℝ))^(8421/2048 : ℝ) := by
    rw [show (19083687965524291177/19085000000000000000 : ℝ)+2*(856431470051/190850000000000 : ℝ)*(5497/20000 : ℝ)=(5011990045436991/5000000000000000 : ℝ) by norm_num, show 1+2*(49392916053630029/10000000000000000000 : ℝ)=(5049392916053630029/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19083687965524291177/19085000000000000000 : ℝ)*(X 1 0+X 2 0)+(856431470051/190850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8421/2048 : ℝ)) (lo := (383/50000 : ℝ)) (hi := (5497/20000 : ℝ)) (c := (19083687965524291177/19085000000000000000 : ℝ)) (alpha := (856431470051/190850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19083687965524291177/19085000000000000000 : ℝ)*(X 0 1+X 2 1)+(856431470051/190850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8421/2048 : ℝ)) (lo := (383/50000 : ℝ)) (hi := (5497/20000 : ℝ)) (c := (19083687965524291177/19085000000000000000 : ℝ)) (alpha := (856431470051/190850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19083687965524291177/19085000000000000000 : ℝ)*(X 0 2+X 1 2)+(856431470051/190850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8421/2048 : ℝ)) (lo := (383/50000 : ℝ)) (hi := (5497/20000 : ℝ)) (c := (19083687965524291177/19085000000000000000 : ℝ)) (alpha := (856431470051/190850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2062933761/10000000000 : ℝ)*X 0 0+(5678884357/10000000000 : ℝ)*X 0 1+(1254990339/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1353591383/2500000000 : ℝ)*X 1 0+(-604247543/2500000000 : ℝ)*X 1 1+(313747589/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5414365609/10000000000 : ℝ)*X 2 0+(2509980691/5000000000 : ℝ)*X 2 1+(-604247531/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1077495529/2500000000 : ℝ)*X 0 0+(1846545097/5000000000 : ℝ)*X 0 1+(5026408159/10000000000 : ℝ)*X 0 2+(1077495529/2500000000 : ℝ)*X 1 0+(1846545097/5000000000 : ℝ)*X 1 1+(5026408159/10000000000 : ℝ)*X 1 2+(1077495529/2500000000 : ℝ)*X 2 0+(1846545097/5000000000 : ℝ)*X 2 1+(5026408159/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-257953301/1250000000 : ℝ)*X 0 0+(1005732273/2000000000 : ℝ)*X 0 1+(5670017511/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((104894237/200000000 : ℝ)*X 1 0+(-883466693/5000000000 : ℝ)*X 1 1+(88594029/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5244712147/10000000000 : ℝ)*X 2 0+(2835009301/5000000000 : ℝ)*X 2 1+(-1766931879/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((107784547/250000000 : ℝ)*X 0 0+(1001760923/2000000000 : ℝ)*X 0 1+(74220609/200000000 : ℝ)*X 0 2+(107784547/250000000 : ℝ)*X 1 0+(1001760923/2000000000 : ℝ)*X 1 1+(74220609/200000000 : ℝ)*X 1 2+(107784547/250000000 : ℝ)*X 2 0+(1001760923/2000000000 : ℝ)*X 2 1+(74220609/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1966635811887336120119834439/954250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27503923/100000000000000 : ℝ)*(base1) + (123708727/25000000000000 : ℝ)*(base19) + (516417813/100000000000000 : ℝ)*(base23) + (26899301/50000000000000 : ℝ)*(upper3) + (77070361/100000000000000 : ℝ)*(upper5) + (1133822606485623/100000000000000 : ℝ)*(major0) + (1133822606485623/100000000000000 : ℝ)*(major1) + (1133822606485623/100000000000000 : ℝ)*(major2) + (379407637779829/25000000000000 : ℝ)*(sp0) + (758816469219447/50000000000000 : ℝ)*(sp1) + (151763291685599/10000000000000 : ℝ)*(sp2) + (375005092276057/50000000000000 : ℝ)*(sp3) + (2909658409/100000000000000 : ℝ)*(sp4) + (46841999/3125000000000 : ℝ)*(sp7) + (187502927750001/25000000000000 : ℝ)*(f.failure) + (758816716636901/50000000000000 : ℝ)*(f.sum) + (2733431255657/9542500000000000000000000000 : ℝ)*base66 + (4152757824436951729/1908500000000000000000000000000000 : ℝ)*base68 + (9449581409984951729/1908500000000000000000000000000000 : ℝ)*base70 + (5184309973718451729/1908500000000000000000000000000000 : ℝ)*base72 + (2985658157617/9542500000000000000000000000 : ℝ)*base74 + (1314929492653451729/1908500000000000000000000000000000 : ℝ)*base76 + (11100366641085451729/1908500000000000000000000000000000 : ℝ)*base78 + (18460343527842451729/1908500000000000000000000000000000 : ℝ)*base80 + (977493729359/4771250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (15423987/2500000000000000000000 : ℝ)*base89 + (15423987/2500000000000000000000 : ℝ)*base91 + (15423987/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1091598527595578054166968763/477125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (115435169/10000000000000 : ℝ)*(base19) + (1653224399/100000000000000 : ℝ)*(base23) + (118995729/100000000000000 : ℝ)*(upper2) + (224221757/100000000000000 : ℝ)*(upper3) + (64866911/100000000000000 : ℝ)*(upper5) + (582436306696073/50000000000000 : ℝ)*(major0) + (582436306696073/50000000000000 : ℝ)*(major1) + (582436306696073/50000000000000 : ℝ)*(major2) + (2533646673/50000000000000 : ℝ)*(sp1) + (5372985277/50000000000000 : ℝ)*(sp2) + (779597093510273/50000000000000 : ℝ)*(sp4) + (155918796537551/10000000000000 : ℝ)*(sp5) + (194897723478199/12500000000000 : ℝ)*(sp6) + (770550963501509/100000000000000 : ℝ)*(sp7) + (770550963501509/100000000000000 : ℝ)*(f.failure) + (779597093510273/50000000000000 : ℝ)*(f.sum) + (22223202176993/4771250000000000000000000000 : ℝ)*base65 + (5797034360314502079/954250000000000000000000000000000 : ℝ)*base68 + (5486102237871252079/954250000000000000000000000000000 : ℝ)*base70 + (4526289376424252079/954250000000000000000000000000000 : ℝ)*base72 + (77846152850537/19085000000000000000000000000 : ℝ)*base73 + (3310612876567752079/954250000000000000000000000000000 : ℝ)*base76 + (3229854778164247921/954250000000000000000000000000000 : ℝ)*base77 + (1045508092216997921/954250000000000000000000000000000 : ℝ)*base79 + (16808953199459/9542500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (3953617/10000000000000000000000 : ℝ)*base90 + (3953617/10000000000000000000000 : ℝ)*base92 + (3953617/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1229_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151173987/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5497/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (383/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6123/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10027/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1229_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1229_s2_0 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-263953831/1250000000 : ℝ)*x 0 + (5495017979/10000000000 : ℝ)*x 1 + (5172783513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263953831/1250000000 : ℝ)^4211 ≤ (1281191724371/10000000000000 : ℝ)^3187 := by
    have hnat : (263953831 : ℕ)^4211*10000000000000^3187 ≤ 1281191724371^3187*1250000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263953831 1250000000 1281191724371 10000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5495017979/10000000000 : ℝ)^4211 ≤ (45333559084927/100000000000000 : ℝ)^3187 := by
    have hnat : (5495017979 : ℕ)^4211*100000000000000^3187 ≤ 45333559084927^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5495017979 10000000000 45333559084927 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5172783513/10000000000 : ℝ)^4211 ≤ (20927261826163/50000000000000 : ℝ)^3187 := by
    have hnat : (5172783513 : ℕ)^4211*50000000000000^3187 ≤ 20927261826163^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172783513 10000000000 20927261826163 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-263953831/1250000000 : ℝ), (5495017979/10000000000 : ℝ), (5172783513/10000000000 : ℝ)] ![(1281191724371/10000000000000 : ℝ), (45333559084927/100000000000000 : ℝ), (20927261826163/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-263953831/1250000000 : ℝ)|^4211 ≤ (1281191724371/10000000000000 : ℝ)^3187
        have hw : |(-263953831/1250000000 : ℝ)|=(263953831/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5495017979/10000000000 : ℝ)|^4211 ≤ (45333559084927/100000000000000 : ℝ)^3187
        have hw : |(5495017979/10000000000 : ℝ)|=(5495017979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5172783513/10000000000 : ℝ)|^4211 ≤ (20927261826163/50000000000000 : ℝ)^3187
        have hw : |(5172783513/10000000000 : ℝ)|=(5172783513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_s2_1 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2685107801/5000000000 : ℝ)*x 0 + (-227862177/1000000000 : ℝ)*x 1 + (161649483/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685107801/5000000000 : ℝ)^4211 ≤ (21989058506197/50000000000000 : ℝ)^3187 := by
    have hnat : (2685107801 : ℕ)^4211*50000000000000^3187 ≤ 21989058506197^3187*5000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685107801 5000000000 21989058506197 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (227862177/1000000000 : ℝ)^4211 ≤ (7083679966657/50000000000000 : ℝ)^3187 := by
    have hnat : (227862177 : ℕ)^4211*50000000000000^3187 ≤ 7083679966657^3187*1000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227862177 1000000000 7083679966657 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (161649483/312500000 : ℝ)^4211 ≤ (8370904608587/20000000000000 : ℝ)^3187 := by
    have hnat : (161649483 : ℕ)^4211*20000000000000^3187 ≤ 8370904608587^3187*312500000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161649483 312500000 8370904608587 20000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685107801/5000000000 : ℝ), (-227862177/1000000000 : ℝ), (161649483/312500000 : ℝ)] ![(21989058506197/50000000000000 : ℝ), (7083679966657/50000000000000 : ℝ), (8370904608587/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685107801/5000000000 : ℝ)|^4211 ≤ (21989058506197/50000000000000 : ℝ)^3187
        have hw : |(2685107801/5000000000 : ℝ)|=(2685107801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-227862177/1000000000 : ℝ)|^4211 ≤ (7083679966657/50000000000000 : ℝ)^3187
        have hw : |(-227862177/1000000000 : ℝ)|=(227862177/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(161649483/312500000 : ℝ)|^4211 ≤ (8370904608587/20000000000000 : ℝ)^3187
        have hw : |(161649483/312500000 : ℝ)|=(161649483/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_s2_2 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1074043083/2000000000 : ℝ)*x 0 + (258639181/500000000 : ℝ)*x 1 + (-1139310901/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074043083/2000000000 : ℝ)^4211 ≤ (43978114988957/100000000000000 : ℝ)^3187 := by
    have hnat : (1074043083 : ℕ)^4211*100000000000000^3187 ≤ 43978114988957^3187*2000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074043083 2000000000 43978114988957 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (258639181/500000000 : ℝ)^4211 ≤ (41854524796271/100000000000000 : ℝ)^3187 := by
    have hnat : (258639181 : ℕ)^4211*100000000000000^3187 ≤ 41854524796271^3187*500000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258639181 500000000 41854524796271 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1139310901/5000000000 : ℝ)^4211 ≤ (7083680098101/50000000000000 : ℝ)^3187 := by
    have hnat : (1139310901 : ℕ)^4211*50000000000000^3187 ≤ 7083680098101^3187*5000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1139310901 5000000000 7083680098101 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074043083/2000000000 : ℝ), (258639181/500000000 : ℝ), (-1139310901/5000000000 : ℝ)] ![(43978114988957/100000000000000 : ℝ), (41854524796271/100000000000000 : ℝ), (7083680098101/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074043083/2000000000 : ℝ)|^4211 ≤ (43978114988957/100000000000000 : ℝ)^3187
        have hw : |(1074043083/2000000000 : ℝ)|=(1074043083/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(258639181/500000000 : ℝ)|^4211 ≤ (41854524796271/100000000000000 : ℝ)^3187
        have hw : |(258639181/500000000 : ℝ)|=(258639181/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1139310901/5000000000 : ℝ)|^4211 ≤ (7083680098101/50000000000000 : ℝ)^3187
        have hw : |(-1139310901/5000000000 : ℝ)|=(1139310901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_s2_3 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (434359157/1000000000 : ℝ)*x 0 + (4029459479/10000000000 : ℝ)*x 1 + (2340747307/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (434359157/1000000000 : ℝ)^4211 ≤ (2076672234283/6250000000000 : ℝ)^3187 := by
    have hnat : (434359157 : ℕ)^4211*6250000000000^3187 ≤ 2076672234283^3187*1000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434359157 1000000000 2076672234283 6250000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4029459479/10000000000 : ℝ)^4211 ≤ (601783796267/2000000000000 : ℝ)^3187 := by
    have hnat : (4029459479 : ℕ)^4211*2000000000000^3187 ≤ 601783796267^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4029459479 10000000000 601783796267 2000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2340747307/5000000000 : ℝ)^4211 ≤ (18342027210723/50000000000000 : ℝ)^3187 := by
    have hnat : (2340747307 : ℕ)^4211*50000000000000^3187 ≤ 18342027210723^3187*5000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2340747307 5000000000 18342027210723 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(434359157/1000000000 : ℝ), (4029459479/10000000000 : ℝ), (2340747307/5000000000 : ℝ)] ![(2076672234283/6250000000000 : ℝ), (601783796267/2000000000000 : ℝ), (18342027210723/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(434359157/1000000000 : ℝ)|^4211 ≤ (2076672234283/6250000000000 : ℝ)^3187
        have hw : |(434359157/1000000000 : ℝ)|=(434359157/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4029459479/10000000000 : ℝ)|^4211 ≤ (601783796267/2000000000000 : ℝ)^3187
        have hw : |(4029459479/10000000000 : ℝ)|=(4029459479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2340747307/5000000000 : ℝ)|^4211 ≤ (18342027210723/50000000000000 : ℝ)^3187
        have hw : |(2340747307/5000000000 : ℝ)|=(2340747307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_s2_4 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-527927953/2500000000 : ℝ)*x 0 + (206994949/400000000 : ℝ)*x 1 + (2746454003/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527927953/2500000000 : ℝ)^4211 ≤ (3203141980183/25000000000000 : ℝ)^3187 := by
    have hnat : (527927953 : ℕ)^4211*25000000000000^3187 ≤ 3203141980183^3187*2500000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527927953 2500000000 3203141980183 25000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (206994949/400000000 : ℝ)^4211 ≤ (41876871711081/100000000000000 : ℝ)^3187 := by
    have hnat : (206994949 : ℕ)^4211*100000000000000^3187 ≤ 41876871711081^3187*400000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206994949 400000000 41876871711081 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2746454003/5000000000 : ℝ)^4211 ≤ (9062112069649/20000000000000 : ℝ)^3187 := by
    have hnat : (2746454003 : ℕ)^4211*20000000000000^3187 ≤ 9062112069649^3187*5000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2746454003 5000000000 9062112069649 20000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-527927953/2500000000 : ℝ), (206994949/400000000 : ℝ), (2746454003/5000000000 : ℝ)] ![(3203141980183/25000000000000 : ℝ), (41876871711081/100000000000000 : ℝ), (9062112069649/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-527927953/2500000000 : ℝ)|^4211 ≤ (3203141980183/25000000000000 : ℝ)^3187
        have hw : |(-527927953/2500000000 : ℝ)|=(527927953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(206994949/400000000 : ℝ)|^4211 ≤ (41876871711081/100000000000000 : ℝ)^3187
        have hw : |(206994949/400000000 : ℝ)|=(206994949/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2746454003/5000000000 : ℝ)|^4211 ≤ (9062112069649/20000000000000 : ℝ)^3187
        have hw : |(2746454003/5000000000 : ℝ)|=(2746454003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_s2_5 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5287992287/10000000000 : ℝ)*x 0 + (-979248519/5000000000 : ℝ)*x 1 + (2746454023/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287992287/10000000000 : ℝ)^4211 ≤ (43090614148909/100000000000000 : ℝ)^3187 := by
    have hnat : (5287992287 : ℕ)^4211*100000000000000^3187 ≤ 43090614148909^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287992287 10000000000 43090614148909 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (979248519/5000000000 : ℝ)^4211 ≤ (2319765011809/20000000000000 : ℝ)^3187 := by
    have hnat : (979248519 : ℕ)^4211*20000000000000^3187 ≤ 2319765011809^3187*5000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      979248519 5000000000 2319765011809 20000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2746454023/5000000000 : ℝ)^4211 ≤ (45310560784219/100000000000000 : ℝ)^3187 := by
    have hnat : (2746454023 : ℕ)^4211*100000000000000^3187 ≤ 45310560784219^3187*5000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2746454023 5000000000 45310560784219 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287992287/10000000000 : ℝ), (-979248519/5000000000 : ℝ), (2746454023/5000000000 : ℝ)] ![(43090614148909/100000000000000 : ℝ), (2319765011809/20000000000000 : ℝ), (45310560784219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287992287/10000000000 : ℝ)|^4211 ≤ (43090614148909/100000000000000 : ℝ)^3187
        have hw : |(5287992287/10000000000 : ℝ)|=(5287992287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-979248519/5000000000 : ℝ)|^4211 ≤ (2319765011809/20000000000000 : ℝ)^3187
        have hw : |(-979248519/5000000000 : ℝ)|=(979248519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2746454023/5000000000 : ℝ)|^4211 ≤ (45310560784219/100000000000000 : ℝ)^3187
        have hw : |(2746454023/5000000000 : ℝ)|=(2746454023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_s2_6 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057598493/2000000000 : ℝ)*x 0 + (1098581621/2000000000 : ℝ)*x 1 + (-195849671/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057598493/2000000000 : ℝ)^4211 ≤ (10772654016359/25000000000000 : ℝ)^3187 := by
    have hnat : (1057598493 : ℕ)^4211*25000000000000^3187 ≤ 10772654016359^3187*2000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057598493 2000000000 10772654016359 25000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1098581621/2000000000 : ℝ)^4211 ≤ (566382017841/1250000000000 : ℝ)^3187 := by
    have hnat : (1098581621 : ℕ)^4211*1250000000000^3187 ≤ 566382017841^3187*2000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098581621 2000000000 566382017841 1250000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (195849671/1000000000 : ℝ)^4211 ≤ (11598822492387/100000000000000 : ℝ)^3187 := by
    have hnat : (195849671 : ℕ)^4211*100000000000000^3187 ≤ 11598822492387^3187*1000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195849671 1000000000 11598822492387 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057598493/2000000000 : ℝ), (1098581621/2000000000 : ℝ), (-195849671/1000000000 : ℝ)] ![(10772654016359/25000000000000 : ℝ), (566382017841/1250000000000 : ℝ), (11598822492387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057598493/2000000000 : ℝ)|^4211 ≤ (10772654016359/25000000000000 : ℝ)^3187
        have hw : |(1057598493/2000000000 : ℝ)|=(1057598493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1098581621/2000000000 : ℝ)|^4211 ≤ (566382017841/1250000000000 : ℝ)^3187
        have hw : |(1098581621/2000000000 : ℝ)|=(1098581621/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-195849671/1000000000 : ℝ)|^4211 ≤ (11598822492387/100000000000000 : ℝ)^3187
        have hw : |(-195849671/1000000000 : ℝ)|=(195849671/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_s2_7 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4343755261/10000000000 : ℝ)*x 0 + (4677265267/10000000000 : ℝ)*x 1 + (161349143/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4343755261/10000000000 : ℝ)^4211 ≤ (4153551282397/12500000000000 : ℝ)^3187 := by
    have hnat : (4343755261 : ℕ)^4211*12500000000000^3187 ≤ 4153551282397^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4343755261 10000000000 4153551282397 12500000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4677265267/10000000000 : ℝ)^4211 ≤ (36640271347639/100000000000000 : ℝ)^3187 := by
    have hnat : (4677265267 : ℕ)^4211*100000000000000^3187 ≤ 36640271347639^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4677265267 10000000000 36640271347639 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (161349143/400000000 : ℝ)^4211 ≤ (30131318381239/100000000000000 : ℝ)^3187 := by
    have hnat : (161349143 : ℕ)^4211*100000000000000^3187 ≤ 30131318381239^3187*400000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161349143 400000000 30131318381239 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4343755261/10000000000 : ℝ), (4677265267/10000000000 : ℝ), (161349143/400000000 : ℝ)] ![(4153551282397/12500000000000 : ℝ), (36640271347639/100000000000000 : ℝ), (30131318381239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4343755261/10000000000 : ℝ)|^4211 ≤ (4153551282397/12500000000000 : ℝ)^3187
        have hw : |(4343755261/10000000000 : ℝ)|=(4343755261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4677265267/10000000000 : ℝ)|^4211 ≤ (36640271347639/100000000000000 : ℝ)^3187
        have hw : |(4677265267/10000000000 : ℝ)|=(4677265267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(161349143/400000000 : ℝ)|^4211 ≤ (30131318381239/100000000000000 : ℝ)^3187
        have hw : |(161349143/400000000 : ℝ)|=(161349143/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1229_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151173987/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10027/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6123/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4723/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16257/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10027/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6123/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10027/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6123/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10027/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6123/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10027/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6123/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10027/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6123/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10027/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6123/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6123/100000 : ℝ) ^ (8421/2048 : ℝ) ≤ (1028536576567883/100000000000000000000 : ℝ) := by
    have hpowers : (6123/100000 : ℝ)^8421 ≤ (1028536576567883/100000000000000000000 : ℝ)^2048 := by
      have hnat : (6123 : ℕ)^8421*100000000000000000000^2048 ≤ 1028536576567883^2048*100000^8421 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6123 100000 1028536576567883 100000000000000000000 8421 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6123/100000 : ℝ)) (X := (1028536576567883/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8421 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (10027/50000 : ℝ) ^ (8421/2048 : ℝ) ≤ (33784591788720471/25000000000000000000 : ℝ) := by
    have hpowers : (10027/50000 : ℝ)^8421 ≤ (33784591788720471/25000000000000000000 : ℝ)^2048 := by
      have hnat : (10027 : ℕ)^8421*25000000000000000000^2048 ≤ 33784591788720471^2048*50000^8421 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10027 50000 33784591788720471 25000000000000000000 8421 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10027/50000 : ℝ)) (X := (33784591788720471/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8421 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001028536576567883/50000000000000000000 : ℝ) ≤ (10000050027942349/10000000000000000 : ℝ) ^ (8421/2048 : ℝ) := by
    have hpowers : (50001028536576567883/50000000000000000000 : ℝ)^2048 ≤ (10000050027942349/10000000000000000 : ℝ)^8421 := by
      have hnat : (50001028536576567883 : ℕ)^2048*10000000000000000^8421 ≤ 10000050027942349^8421*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001028536576567883 50000000000000000000 10000050027942349 10000000000000000 2048 8421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000050027942349/10000000000000000 : ℝ)) (X := (50001028536576567883/50000000000000000000 : ℝ)) (by norm_num) 8421 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100136166903731449767/100000000000000000000 : ℝ) ≤ (19537714638357/19531250000000 : ℝ) ^ (8421/2048 : ℝ) := by
    have hpowers : (100136166903731449767/100000000000000000000 : ℝ)^2048 ≤ (19537714638357/19531250000000 : ℝ)^8421 := by
      have hnat : (100136166903731449767 : ℕ)^2048*19531250000000^8421 ≤ 19537714638357^8421*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100136166903731449767 100000000000000000000 19537714638357 19531250000000 2048 8421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (19537714638357/19531250000000 : ℝ)) (X := (100136166903731449767/100000000000000000000 : ℝ)) (by norm_num) 8421 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12533784591788720471/12500000000000000000 : ℝ) ≤ (10006569761735219/10000000000000000 : ℝ) ^ (8421/2048 : ℝ) := by
    have hpowers : (12533784591788720471/12500000000000000000 : ℝ)^2048 ≤ (10006569761735219/10000000000000000 : ℝ)^8421 := by
      have hnat : (12533784591788720471 : ℕ)^2048*10000000000000000^8421 ≤ 10006569761735219^8421*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12533784591788720471 12500000000000000000 10006569761735219 10000000000000000 2048 8421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006569761735219/10000000000000000 : ℝ)) (X := (12533784591788720471/12500000000000000000 : ℝ)) (by norm_num) 8421 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1028536576567883/100000000000000000000 : ℝ) ≤ ((139270776609251120909/139310000000000000000 : ℝ)+2*(651973379287/278620000000000 : ℝ)*(6123/100000 : ℝ))^(8421/2048 : ℝ) := by
    rw [show (139270776609251120909/139310000000000000000 : ℝ)+2*(651973379287/278620000000000 : ℝ)*(6123/100000 : ℝ)=(10000050027942349/10000000000000000 : ℝ) by norm_num, show 1+2*(1028536576567883/100000000000000000000 : ℝ)=(50001028536576567883/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33784591788720471/25000000000000000000 : ℝ)+(1028536576567883/100000000000000000000 : ℝ) ≤ ((139270776609251120909/139310000000000000000 : ℝ)+(651973379287/278620000000000 : ℝ)*((10027/50000 : ℝ)+(6123/100000 : ℝ)))^(8421/2048 : ℝ) := by
    rw [show (139270776609251120909/139310000000000000000 : ℝ)+(651973379287/278620000000000 : ℝ)*((10027/50000 : ℝ)+(6123/100000 : ℝ))=(19537714638357/19531250000000 : ℝ) by norm_num, show 1+(33784591788720471/25000000000000000000 : ℝ)+(1028536576567883/100000000000000000000 : ℝ)=(100136166903731449767/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33784591788720471/25000000000000000000 : ℝ) ≤ ((139270776609251120909/139310000000000000000 : ℝ)+2*(651973379287/278620000000000 : ℝ)*(10027/50000 : ℝ))^(8421/2048 : ℝ) := by
    rw [show (139270776609251120909/139310000000000000000 : ℝ)+2*(651973379287/278620000000000 : ℝ)*(10027/50000 : ℝ)=(10006569761735219/10000000000000000 : ℝ) by norm_num, show 1+2*(33784591788720471/25000000000000000000 : ℝ)=(12533784591788720471/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (139270776609251120909/139310000000000000000 : ℝ)*(X 1 0+X 2 0)+(651973379287/278620000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8421/2048 : ℝ)) (lo := (6123/100000 : ℝ)) (hi := (10027/50000 : ℝ)) (c := (139270776609251120909/139310000000000000000 : ℝ)) (alpha := (651973379287/278620000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (139270776609251120909/139310000000000000000 : ℝ)*(X 0 1+X 2 1)+(651973379287/278620000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8421/2048 : ℝ)) (lo := (6123/100000 : ℝ)) (hi := (10027/50000 : ℝ)) (c := (139270776609251120909/139310000000000000000 : ℝ)) (alpha := (651973379287/278620000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (139270776609251120909/139310000000000000000 : ℝ)*(X 0 2+X 1 2)+(651973379287/278620000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8421/2048 : ℝ)) (lo := (6123/100000 : ℝ)) (hi := (10027/50000 : ℝ)) (c := (139270776609251120909/139310000000000000000 : ℝ)) (alpha := (651973379287/278620000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-263953831/1250000000 : ℝ)*X 0 0+(5495017979/10000000000 : ℝ)*X 0 1+(5172783513/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2685107801/5000000000 : ℝ)*X 1 0+(-227862177/1000000000 : ℝ)*X 1 1+(161649483/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1074043083/2000000000 : ℝ)*X 2 0+(258639181/500000000 : ℝ)*X 2 1+(-1139310901/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((434359157/1000000000 : ℝ)*X 0 0+(4029459479/10000000000 : ℝ)*X 0 1+(2340747307/5000000000 : ℝ)*X 0 2+(434359157/1000000000 : ℝ)*X 1 0+(4029459479/10000000000 : ℝ)*X 1 1+(2340747307/5000000000 : ℝ)*X 1 2+(434359157/1000000000 : ℝ)*X 2 0+(4029459479/10000000000 : ℝ)*X 2 1+(2340747307/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-527927953/2500000000 : ℝ)*X 0 0+(206994949/400000000 : ℝ)*X 0 1+(2746454003/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5287992287/10000000000 : ℝ)*X 1 0+(-979248519/5000000000 : ℝ)*X 1 1+(2746454023/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1057598493/2000000000 : ℝ)*X 2 0+(1098581621/2000000000 : ℝ)*X 2 1+(-195849671/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4343755261/10000000000 : ℝ)*X 0 0+(4677265267/10000000000 : ℝ)*X 0 1+(161349143/400000000 : ℝ)*X 0 2+(4343755261/10000000000 : ℝ)*X 1 0+(4677265267/10000000000 : ℝ)*X 1 1+(161349143/400000000 : ℝ)*X 1 2+(4343755261/10000000000 : ℝ)*X 2 0+(4677265267/10000000000 : ℝ)*X 2 1+(161349143/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26843474083304205187591136889/3482750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (308152101/20000000000000 : ℝ)*(base19) + (1323172733/100000000000000 : ℝ)*(base23) + (29408233/50000000000000 : ℝ)*(lower2) + (30622051/12500000000000 : ℝ)*(upper3) + (107322681/100000000000000 : ℝ)*(upper5) + (1159259859108593/50000000000000 : ℝ)*(major0) + (1159259859108593/50000000000000 : ℝ)*(major1) + (1159259859108593/50000000000000 : ℝ)*(major2) + (124133911195181/4000000000000 : ℝ)*(sp0) + (12122504950879/390625000000 : ℝ)*(sp1) + (775840371253199/25000000000000 : ℝ)*(sp2) + (1533667370473857/100000000000000 : ℝ)*(sp3) + (3757076501/25000000000000 : ℝ)*(sp4) + (4500428303/50000000000000 : ℝ)*(sp7) + (1533676371330463/100000000000000 : ℝ)*(f.failure) + (387920351023191/12500000000000 : ℝ)*(f.sum) + (12770679200367/6965500000000000000000000000 : ℝ)*base65 + (39050850967890628963/6965500000000000000000000000000000 : ℝ)*base68 + (7528890665295871037/6965500000000000000000000000000000 : ℝ)*base69 + (58004985936012628963/6965500000000000000000000000000000 : ℝ)*base72 + (18328114832307/13931000000000000000000000000 : ℝ)*base73 + (8700044794323371037/6965500000000000000000000000000000 : ℝ)*base75 + (9550432013261371037/6965500000000000000000000000000000 : ℝ)*base77 + (23980817761361871037/6965500000000000000000000000000000 : ℝ)*base79 + (14137616448023/6965500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (13734019/10000000000000000000000 : ℝ)*base90 + (13734019/10000000000000000000000 : ℝ)*base92 + (13734019/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19783851387004700740490696253/6965500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (468556581/50000000000000 : ℝ)*(base19) + (624729529/50000000000000 : ℝ)*(base23) + (59740347/100000000000000 : ℝ)*(upper2) + (146727867/100000000000000 : ℝ)*(upper3) + (2741141/5000000000000 : ℝ)*(upper5) + (2349113657327913/100000000000000 : ℝ)*(major0) + (2349113657327913/100000000000000 : ℝ)*(major1) + (2349113657327913/100000000000000 : ℝ)*(major2) + (9003210437/100000000000000 : ℝ)*(sp1) + (15018501331/100000000000000 : ℝ)*(sp2) + (1572156640095661/50000000000000 : ℝ)*(sp4) + (3144303339867723/100000000000000 : ℝ)*(sp5) + (786074253057733/25000000000000 : ℝ)*(sp6) + (388478484947267/25000000000000 : ℝ)*(sp7) + (388478484947267/25000000000000 : ℝ)*(f.failure) + (1572156640095661/50000000000000 : ℝ)*(f.sum) + (2601094560627/13931000000000000000000000000 : ℝ)*base65 + (91049062221146867083/13931000000000000000000000000000000 : ℝ)*base68 + (59896928161752867083/13931000000000000000000000000000000 : ℝ)*base70 + (107045496200673867083/13931000000000000000000000000000000 : ℝ)*base72 + (18963980709721/13931000000000000000000000000 : ℝ)*base74 + (113071633147490867083/13931000000000000000000000000000000 : ℝ)*base76 + (16483606042943867083/13931000000000000000000000000000000 : ℝ)*base78 + (52999149594676867083/13931000000000000000000000000000000 : ℝ)*base80 + (62067314534373/13931000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (12143529/2500000000000000000000 : ℝ)*base89 + (12143529/2500000000000000000000 : ℝ)*base91 + (12143529/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1229_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151173987/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10027/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6123/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4723/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16257/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1229_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1229_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151173987/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4723/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16257/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1229_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1229_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1229_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151173987/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4723/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16257/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1229_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

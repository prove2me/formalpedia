-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1314_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:41:04.867575+00:00
-- url     : https://prove2.me/submissions/6112cca3-2592-41ce-aecb-1edf3be2fb6d

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
theorem support_rectangle_w1314_s0_0 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1825815277/10000000000 : ℝ)*x 0 + (6009098113/10000000000 : ℝ)*x 1 + (600523081/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1825815277/10000000000 : ℝ)^2137 ≤ (10684616262399/100000000000000 : ℝ)^1625 := by
    have hnat : (1825815277 : ℕ)^2137*100000000000000^1625 ≤ 10684616262399^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1825815277 10000000000 10684616262399 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6009098113/10000000000 : ℝ)^2137 ≤ (25590997392241/50000000000000 : ℝ)^1625 := by
    have hnat : (6009098113 : ℕ)^2137*50000000000000^1625 ≤ 25590997392241^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6009098113 10000000000 25590997392241 50000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (600523081/1250000000 : ℝ)^2137 ≤ (7626677787133/20000000000000 : ℝ)^1625 := by
    have hnat : (600523081 : ℕ)^2137*20000000000000^1625 ≤ 7626677787133^1625*1250000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      600523081 1250000000 7626677787133 20000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1825815277/10000000000 : ℝ), (6009098113/10000000000 : ℝ), (600523081/1250000000 : ℝ)] ![(10684616262399/100000000000000 : ℝ), (25590997392241/50000000000000 : ℝ), (7626677787133/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1825815277/10000000000 : ℝ)|^2137 ≤ (10684616262399/100000000000000 : ℝ)^1625
        have hw : |(-1825815277/10000000000 : ℝ)|=(1825815277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6009098113/10000000000 : ℝ)|^2137 ≤ (25590997392241/50000000000000 : ℝ)^1625
        have hw : |(6009098113/10000000000 : ℝ)|=(6009098113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(600523081/1250000000 : ℝ)|^2137 ≤ (7626677787133/20000000000000 : ℝ)^1625
        have hw : |(600523081/1250000000 : ℝ)|=(600523081/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s0_1 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5504950861/10000000000 : ℝ)*x 0 + (-2512088579/10000000000 : ℝ)*x 1 + (600523079/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5504950861/10000000000 : ℝ)^2137 ≤ (4561113088831/10000000000000 : ℝ)^1625 := by
    have hnat : (5504950861 : ℕ)^2137*10000000000000^1625 ≤ 4561113088831^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5504950861 10000000000 4561113088831 10000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2512088579/10000000000 : ℝ)^2137 ≤ (16255480326979/100000000000000 : ℝ)^1625 := by
    have hnat : (2512088579 : ℕ)^2137*100000000000000^1625 ≤ 16255480326979^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2512088579 10000000000 16255480326979 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (600523079/1250000000 : ℝ)^2137 ≤ (38133388768649/100000000000000 : ℝ)^1625 := by
    have hnat : (600523079 : ℕ)^2137*100000000000000^1625 ≤ 38133388768649^1625*1250000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      600523079 1250000000 38133388768649 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5504950861/10000000000 : ℝ), (-2512088579/10000000000 : ℝ), (600523079/1250000000 : ℝ)] ![(4561113088831/10000000000000 : ℝ), (16255480326979/100000000000000 : ℝ), (38133388768649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5504950861/10000000000 : ℝ)|^2137 ≤ (4561113088831/10000000000000 : ℝ)^1625
        have hw : |(5504950861/10000000000 : ℝ)|=(5504950861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2512088579/10000000000 : ℝ)|^2137 ≤ (16255480326979/100000000000000 : ℝ)^1625
        have hw : |(-2512088579/10000000000 : ℝ)|=(2512088579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(600523079/1250000000 : ℝ)|^2137 ≤ (38133388768649/100000000000000 : ℝ)^1625
        have hw : |(600523079/1250000000 : ℝ)|=(600523079/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s0_2 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5504950121/10000000000 : ℝ)*x 0 + (240209259/500000000 : ℝ)*x 1 + (-502417771/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5504950121/10000000000 : ℝ)^2137 ≤ (45611122825243/100000000000000 : ℝ)^1625 := by
    have hnat : (5504950121 : ℕ)^2137*100000000000000^1625 ≤ 45611122825243^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5504950121 10000000000 45611122825243 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (240209259/500000000 : ℝ)^2137 ≤ (38133394488931/100000000000000 : ℝ)^1625 := by
    have hnat : (240209259 : ℕ)^2137*100000000000000^1625 ≤ 38133394488931^1625*500000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240209259 500000000 38133394488931 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (502417771/2000000000 : ℝ)^2137 ≤ (8127741337833/50000000000000 : ℝ)^1625 := by
    have hnat : (502417771 : ℕ)^2137*50000000000000^1625 ≤ 8127741337833^1625*2000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502417771 2000000000 8127741337833 50000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5504950121/10000000000 : ℝ), (240209259/500000000 : ℝ), (-502417771/2000000000 : ℝ)] ![(45611122825243/100000000000000 : ℝ), (38133394488931/100000000000000 : ℝ), (8127741337833/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5504950121/10000000000 : ℝ)|^2137 ≤ (45611122825243/100000000000000 : ℝ)^1625
        have hw : |(5504950121/10000000000 : ℝ)|=(5504950121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(240209259/500000000 : ℝ)|^2137 ≤ (38133394488931/100000000000000 : ℝ)^1625
        have hw : |(240209259/500000000 : ℝ)|=(240209259/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-502417771/2000000000 : ℝ)|^2137 ≤ (8127741337833/50000000000000 : ℝ)^1625
        have hw : |(-502417771/2000000000 : ℝ)|=(502417771/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s0_3 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (261435577/625000000 : ℝ)*x 0 + (621614969/2000000000 : ℝ)*x 1 + (2802645143/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (261435577/625000000 : ℝ)^2137 ≤ (15892536918819/50000000000000 : ℝ)^1625 := by
    have hnat : (261435577 : ℕ)^2137*50000000000000^1625 ≤ 15892536918819^1625*625000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261435577 625000000 15892536918819 50000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (621614969/2000000000 : ℝ)^2137 ≤ (10753683399059/50000000000000 : ℝ)^1625 := by
    have hnat : (621614969 : ℕ)^2137*50000000000000^1625 ≤ 10753683399059^1625*2000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      621614969 2000000000 10753683399059 50000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2802645143/5000000000 : ℝ)^2137 ≤ (5838444918861/12500000000000 : ℝ)^1625 := by
    have hnat : (2802645143 : ℕ)^2137*12500000000000^1625 ≤ 5838444918861^1625*5000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2802645143 5000000000 5838444918861 12500000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(261435577/625000000 : ℝ), (621614969/2000000000 : ℝ), (2802645143/5000000000 : ℝ)] ![(15892536918819/50000000000000 : ℝ), (10753683399059/50000000000000 : ℝ), (5838444918861/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(261435577/625000000 : ℝ)|^2137 ≤ (15892536918819/50000000000000 : ℝ)^1625
        have hw : |(261435577/625000000 : ℝ)|=(261435577/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(621614969/2000000000 : ℝ)|^2137 ≤ (10753683399059/50000000000000 : ℝ)^1625
        have hw : |(621614969/2000000000 : ℝ)|=(621614969/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2802645143/5000000000 : ℝ)|^2137 ≤ (5838444918861/12500000000000 : ℝ)^1625
        have hw : |(2802645143/5000000000 : ℝ)|=(2802645143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s0_4 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-457605159/2500000000 : ℝ)*x 0 + (193409813/400000000 : ℝ)*x 1 + (5976930091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (457605159/2500000000 : ℝ)^2137 ≤ (5360036108433/50000000000000 : ℝ)^1625 := by
    have hnat : (457605159 : ℕ)^2137*50000000000000^1625 ≤ 5360036108433^1625*2500000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      457605159 2500000000 5360036108433 50000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (193409813/400000000 : ℝ)^2137 ≤ (38457944647423/100000000000000 : ℝ)^1625 := by
    have hnat : (193409813 : ℕ)^2137*100000000000000^1625 ≤ 38457944647423^1625*400000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      193409813 400000000 38457944647423 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5976930091/10000000000 : ℝ)^2137 ≤ (794093486323/1562500000000 : ℝ)^1625 := by
    have hnat : (5976930091 : ℕ)^2137*1562500000000^1625 ≤ 794093486323^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5976930091 10000000000 794093486323 1562500000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-457605159/2500000000 : ℝ), (193409813/400000000 : ℝ), (5976930091/10000000000 : ℝ)] ![(5360036108433/50000000000000 : ℝ), (38457944647423/100000000000000 : ℝ), (794093486323/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-457605159/2500000000 : ℝ)|^2137 ≤ (5360036108433/50000000000000 : ℝ)^1625
        have hw : |(-457605159/2500000000 : ℝ)|=(457605159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(193409813/400000000 : ℝ)|^2137 ≤ (38457944647423/100000000000000 : ℝ)^1625
        have hw : |(193409813/400000000 : ℝ)|=(193409813/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5976930091/10000000000 : ℝ)|^2137 ≤ (794093486323/1562500000000 : ℝ)^1625
        have hw : |(5976930091/10000000000 : ℝ)|=(5976930091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s0_5 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1294190393/2500000000 : ℝ)*x 0 + (-669671917/5000000000 : ℝ)*x 1 + (59769301/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1294190393/2500000000 : ℝ)^2137 ≤ (42069222799769/100000000000000 : ℝ)^1625 := by
    have hnat : (1294190393 : ℕ)^2137*100000000000000^1625 ≤ 42069222799769^1625*2500000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294190393 2500000000 42069222799769 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (669671917/5000000000 : ℝ)^2137 ≤ (7108793953949/100000000000000 : ℝ)^1625 := by
    have hnat : (669671917 : ℕ)^2137*100000000000000^1625 ≤ 7108793953949^1625*5000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669671917 5000000000 7108793953949 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (59769301/100000000 : ℝ)^2137 ≤ (50821983225311/100000000000000 : ℝ)^1625 := by
    have hnat : (59769301 : ℕ)^2137*100000000000000^1625 ≤ 50821983225311^1625*100000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59769301 100000000 50821983225311 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1294190393/2500000000 : ℝ), (-669671917/5000000000 : ℝ), (59769301/100000000 : ℝ)] ![(42069222799769/100000000000000 : ℝ), (7108793953949/100000000000000 : ℝ), (50821983225311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1294190393/2500000000 : ℝ)|^2137 ≤ (42069222799769/100000000000000 : ℝ)^1625
        have hw : |(1294190393/2500000000 : ℝ)|=(1294190393/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-669671917/5000000000 : ℝ)|^2137 ≤ (7108793953949/100000000000000 : ℝ)^1625
        have hw : |(-669671917/5000000000 : ℝ)|=(669671917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(59769301/100000000 : ℝ)|^2137 ≤ (50821983225311/100000000000000 : ℝ)^1625
        have hw : |(59769301/100000000 : ℝ)|=(59769301/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s0_6 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5176761561/10000000000 : ℝ)*x 0 + (2988465049/5000000000 : ℝ)*x 1 + (-267868771/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5176761561/10000000000 : ℝ)^2137 ≤ (10517305670553/25000000000000 : ℝ)^1625 := by
    have hnat : (5176761561 : ℕ)^2137*25000000000000^1625 ≤ 10517305670553^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176761561 10000000000 10517305670553 25000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2988465049/5000000000 : ℝ)^2137 ≤ (25410991601473/50000000000000 : ℝ)^1625 := by
    have hnat : (2988465049 : ℕ)^2137*50000000000000^1625 ≤ 25410991601473^1625*5000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2988465049 5000000000 25410991601473 50000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (267868771/2000000000 : ℝ)^2137 ≤ (7108794100529/100000000000000 : ℝ)^1625 := by
    have hnat : (267868771 : ℕ)^2137*100000000000000^1625 ≤ 7108794100529^1625*2000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267868771 2000000000 7108794100529 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5176761561/10000000000 : ℝ), (2988465049/5000000000 : ℝ), (-267868771/2000000000 : ℝ)] ![(10517305670553/25000000000000 : ℝ), (25410991601473/50000000000000 : ℝ), (7108794100529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5176761561/10000000000 : ℝ)|^2137 ≤ (10517305670553/25000000000000 : ℝ)^1625
        have hw : |(5176761561/10000000000 : ℝ)|=(5176761561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2988465049/5000000000 : ℝ)|^2137 ≤ (25410991601473/50000000000000 : ℝ)^1625
        have hw : |(2988465049/5000000000 : ℝ)|=(2988465049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-267868771/2000000000 : ℝ)|^2137 ≤ (7108794100529/100000000000000 : ℝ)^1625
        have hw : |(-267868771/2000000000 : ℝ)|=(267868771/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s0_7 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2096256819/5000000000 : ℝ)*x 0 + (5540916629/10000000000 : ℝ)*x 1 + (3174743341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2096256819/5000000000 : ℝ)^2137 ≤ (31880483996457/100000000000000 : ℝ)^1625 := by
    have hnat : (2096256819 : ℕ)^2137*100000000000000^1625 ≤ 31880483996457^1625*5000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096256819 5000000000 31880483996457 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5540916629/10000000000 : ℝ)^2137 ≤ (46003417958647/100000000000000 : ℝ)^1625 := by
    have hnat : (5540916629 : ℕ)^2137*100000000000000^1625 ≤ 46003417958647^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5540916629 10000000000 46003417958647 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3174743341/10000000000 : ℝ)^2137 ≤ (22116098036999/100000000000000 : ℝ)^1625 := by
    have hnat : (3174743341 : ℕ)^2137*100000000000000^1625 ≤ 22116098036999^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3174743341 10000000000 22116098036999 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2096256819/5000000000 : ℝ), (5540916629/10000000000 : ℝ), (3174743341/10000000000 : ℝ)] ![(31880483996457/100000000000000 : ℝ), (46003417958647/100000000000000 : ℝ), (22116098036999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2096256819/5000000000 : ℝ)|^2137 ≤ (31880483996457/100000000000000 : ℝ)^1625
        have hw : |(2096256819/5000000000 : ℝ)|=(2096256819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5540916629/10000000000 : ℝ)|^2137 ≤ (46003417958647/100000000000000 : ℝ)^1625
        have hw : |(5540916629/10000000000 : ℝ)|=(5540916629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3174743341/10000000000 : ℝ)|^2137 ≤ (22116098036999/100000000000000 : ℝ)^1625
        have hw : |(3174743341/10000000000 : ℝ)|=(3174743341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1314_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76813193/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (601/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13537/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4273/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4273 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4273*1^1024 ≤ 0^1024*1^4273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4273 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4273/1024 : ℝ) ≤ (546254995607571721/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4273 ≤ (546254995607571721/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4273*25000000000000000000^1024 ≤ 546254995607571721^1024*5^4273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 546254995607571721 25000000000000000000 4273 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (546254995607571721/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4273/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4273 := by
      have hnat : (1 : ℕ)^1024*1^4273 ≤ 1^4273*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25546254995607571721/25000000000000000000 : ℝ) ≤ (1256491659055939/1250000000000000 : ℝ) ^ (4273/1024 : ℝ) := by
    have hpowers : (25546254995607571721/25000000000000000000 : ℝ)^1024 ≤ (1256491659055939/1250000000000000 : ℝ)^4273 := by
      have hnat : (25546254995607571721 : ℕ)^1024*1250000000000000^4273 ≤ 1256491659055939^4273*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25546254995607571721 25000000000000000000 1256491659055939 1250000000000000 1024 4273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1256491659055939/1250000000000000 : ℝ)) (X := (25546254995607571721/25000000000000000000 : ℝ)) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (13046254995607571721/12500000000000000000 : ℝ) ≤ (631491659055939/625000000000000 : ℝ) ^ (4273/1024 : ℝ) := by
    have hpowers : (13046254995607571721/12500000000000000000 : ℝ)^1024 ≤ (631491659055939/625000000000000 : ℝ)^4273 := by
      have hnat : (13046254995607571721 : ℕ)^1024*625000000000000^4273 ≤ 631491659055939^4273*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13046254995607571721 12500000000000000000 631491659055939 625000000000000 1024 4273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (631491659055939/625000000000000 : ℝ)) (X := (13046254995607571721/12500000000000000000 : ℝ)) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(6491659055939/500000000000000 : ℝ)*(0 : ℝ))^(4273/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(6491659055939/500000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(546254995607571721/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(6491659055939/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4273/1024 : ℝ) := by
    rw [show (1 : ℝ)+(6491659055939/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1256491659055939/1250000000000000 : ℝ) by norm_num, show 1+(546254995607571721/25000000000000000000 : ℝ)+(0 : ℝ)=(25546254995607571721/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(546254995607571721/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(6491659055939/500000000000000 : ℝ)*(2/5 : ℝ))^(4273/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(6491659055939/500000000000000 : ℝ)*(2/5 : ℝ)=(631491659055939/625000000000000 : ℝ) by norm_num, show 1+2*(546254995607571721/25000000000000000000 : ℝ)=(13046254995607571721/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(6491659055939/500000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4273/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6491659055939/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(6491659055939/500000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4273/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6491659055939/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(6491659055939/500000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4273/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6491659055939/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1825815277/10000000000 : ℝ)*X 0 0+(6009098113/10000000000 : ℝ)*X 0 1+(600523081/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5504950861/10000000000 : ℝ)*X 1 0+(-2512088579/10000000000 : ℝ)*X 1 1+(600523079/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5504950121/10000000000 : ℝ)*X 2 0+(240209259/500000000 : ℝ)*X 2 1+(-502417771/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((261435577/625000000 : ℝ)*X 0 0+(621614969/2000000000 : ℝ)*X 0 1+(2802645143/5000000000 : ℝ)*X 0 2+(261435577/625000000 : ℝ)*X 1 0+(621614969/2000000000 : ℝ)*X 1 1+(2802645143/5000000000 : ℝ)*X 1 2+(261435577/625000000 : ℝ)*X 2 0+(621614969/2000000000 : ℝ)*X 2 1+(2802645143/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-457605159/2500000000 : ℝ)*X 0 0+(193409813/400000000 : ℝ)*X 0 1+(5976930091/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1294190393/2500000000 : ℝ)*X 1 0+(-669671917/5000000000 : ℝ)*X 1 1+(59769301/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5176761561/10000000000 : ℝ)*X 2 0+(2988465049/5000000000 : ℝ)*X 2 1+(-267868771/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2096256819/5000000000 : ℝ)*X 0 0+(5540916629/10000000000 : ℝ)*X 0 1+(3174743341/10000000000 : ℝ)*X 0 2+(2096256819/5000000000 : ℝ)*X 1 0+(5540916629/10000000000 : ℝ)*X 1 1+(3174743341/10000000000 : ℝ)*X 1 2+(2096256819/5000000000 : ℝ)*X 2 0+(5540916629/10000000000 : ℝ)*X 2 1+(3174743341/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4660466918532035067/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (599143/800000000000 : ℝ)*(base1) + (1217221101/100000000000000 : ℝ)*(base19) + (276414161/25000000000000 : ℝ)*(base23) + (17470599/10000000000000 : ℝ)*(upper3) + (69008661/100000000000000 : ℝ)*(upper5) + (307598145811033/50000000000000 : ℝ)*(major0) + (307598145811033/50000000000000 : ℝ)*(major1) + (307598145811033/50000000000000 : ℝ)*(major2) + (20748482238053/2500000000000 : ℝ)*(sp0) + (414970791214943/50000000000000 : ℝ)*(sp1) + (414970846997171/50000000000000 : ℝ)*(sp2) + (80089525933593/20000000000000 : ℝ)*(sp3) + (1792510871/50000000000000 : ℝ)*(sp4) + (1923683403/100000000000000 : ℝ)*(sp7) + (400449628244243/100000000000000 : ℝ)*(f.failure) + (829942799650987/100000000000000 : ℝ)*(f.sum) + (18296577650013/12500000000000000000000000000 : ℝ)*base66 + (120784345175013/25000000000000000000000000000 : ℝ)*base68 + (179957027999987/25000000000000000000000000000 : ℝ)*base69 + (103913600625013/25000000000000000000000000000 : ℝ)*base72 + (20697441100013/12500000000000000000000000000 : ℝ)*base74 + (11725536249987/25000000000000000000000000000 : ℝ)*base75 + (32126810974987/25000000000000000000000000000 : ℝ)*base77 + (58024758574987/25000000000000000000000000000 : ℝ)*base79 + (30913532837487/12500000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (11302101/5000000000000000000000 : ℝ)*base90 + (11302101/5000000000000000000000 : ℝ)*base92 + (11302101/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4257135744819912309891/781250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1301593207/100000000000000 : ℝ)*(base19) + (655219869/50000000000000 : ℝ)*(base23) + (43817443/50000000000000 : ℝ)*(base32) + (185539799/100000000000000 : ℝ)*(upper3) + (124060509/100000000000000 : ℝ)*(upper5) + (162315189483771/25000000000000 : ℝ)*(major0) + (162315189483771/25000000000000 : ℝ)*(major1) + (162315189483771/25000000000000 : ℝ)*(major2) + (1444851263/50000000000000 : ℝ)*(sp1) + (191163097/6250000000000 : ℝ)*(sp2) + (3421477063001/390625000000 : ℝ)*(sp4) + (875893936832523/100000000000000 : ℝ)*(sp5) + (437946879539483/50000000000000 : ℝ)*(sp6) + (42262311846923/10000000000000 : ℝ)*(sp7) + (105655801526029/25000000000000 : ℝ)*(f.failure) + (3421477063001/390625000000 : ℝ)*(f.sum) + (2132302859031/6250000000000000000000000000 : ℝ)*base66 + (77702239209031/12500000000000000000000000000 : ℝ)*base68 + (8869987409031/12500000000000000000000000000 : ℝ)*base70 + (41526125609031/12500000000000000000000000000 : ℝ)*base72 + (11306015421531/6250000000000000000000000000 : ℝ)*base74 + (71928380359031/12500000000000000000000000000 : ℝ)*base76 + (45561134059031/12500000000000000000000000000 : ℝ)*base78 + (114509174559031/12500000000000000000000000000 : ℝ)*base80 + (19823743290969/6250000000000000000000000000 : ℝ)*base81 + (10100597/1250000000000000000000 : ℝ)*base89 + (10100597/1250000000000000000000 : ℝ)*base91 + (10100597/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1314_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76813193/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (601/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13537/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1314_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1314_s1_0 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-503669019/2500000000 : ℝ)*x 0 + (1130985827/2000000000 : ℝ)*x 1 + (2518714917/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (503669019/2500000000 : ℝ)^2137 ≤ (12161197843743/100000000000000 : ℝ)^1625 := by
    have hnat : (503669019 : ℕ)^2137*100000000000000^1625 ≤ 12161197843743^1625*2500000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503669019 2500000000 12161197843743 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1130985827/2000000000 : ℝ)^2137 ≤ (5906533798507/12500000000000 : ℝ)^1625 := by
    have hnat : (1130985827 : ℕ)^2137*12500000000000^1625 ≤ 5906533798507^1625*2000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130985827 2000000000 5906533798507 12500000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2518714917/5000000000 : ℝ)^2137 ≤ (10146632938097/25000000000000 : ℝ)^1625 := by
    have hnat : (2518714917 : ℕ)^2137*25000000000000^1625 ≤ 10146632938097^1625*5000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2518714917 5000000000 10146632938097 25000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-503669019/2500000000 : ℝ), (1130985827/2000000000 : ℝ), (2518714917/5000000000 : ℝ)] ![(12161197843743/100000000000000 : ℝ), (5906533798507/12500000000000 : ℝ), (10146632938097/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-503669019/2500000000 : ℝ)|^2137 ≤ (12161197843743/100000000000000 : ℝ)^1625
        have hw : |(-503669019/2500000000 : ℝ)|=(503669019/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1130985827/2000000000 : ℝ)|^2137 ≤ (5906533798507/12500000000000 : ℝ)^1625
        have hw : |(1130985827/2000000000 : ℝ)|=(1130985827/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2518714917/5000000000 : ℝ)|^2137 ≤ (10146632938097/25000000000000 : ℝ)^1625
        have hw : |(2518714917/5000000000 : ℝ)|=(2518714917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s1_1 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2704327883/5000000000 : ℝ)*x 0 + (-2344992411/10000000000 : ℝ)*x 1 + (5037429789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2704327883/5000000000 : ℝ)^2137 ≤ (44564799061309/100000000000000 : ℝ)^1625 := by
    have hnat : (2704327883 : ℕ)^2137*100000000000000^1625 ≤ 44564799061309^1625*5000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704327883 5000000000 44564799061309 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2344992411/10000000000 : ℝ)^2137 ≤ (7424334820429/50000000000000 : ℝ)^1625 := by
    have hnat : (2344992411 : ℕ)^2137*50000000000000^1625 ≤ 7424334820429^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2344992411 10000000000 7424334820429 50000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5037429789/10000000000 : ℝ)^2137 ≤ (40586531275587/100000000000000 : ℝ)^1625 := by
    have hnat : (5037429789 : ℕ)^2137*100000000000000^1625 ≤ 40586531275587^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5037429789 10000000000 40586531275587 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2704327883/5000000000 : ℝ), (-2344992411/10000000000 : ℝ), (5037429789/10000000000 : ℝ)] ![(44564799061309/100000000000000 : ℝ), (7424334820429/50000000000000 : ℝ), (40586531275587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2704327883/5000000000 : ℝ)|^2137 ≤ (44564799061309/100000000000000 : ℝ)^1625
        have hw : |(2704327883/5000000000 : ℝ)|=(2704327883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2344992411/10000000000 : ℝ)|^2137 ≤ (7424334820429/50000000000000 : ℝ)^1625
        have hw : |(-2344992411/10000000000 : ℝ)|=(2344992411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5037429789/10000000000 : ℝ)|^2137 ≤ (40586531275587/100000000000000 : ℝ)^1625
        have hw : |(5037429789/10000000000 : ℝ)|=(5037429789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s1_2 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5408655729/10000000000 : ℝ)*x 0 + (5037429607/10000000000 : ℝ)*x 1 + (-586248173/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5408655729/10000000000 : ℝ)^2137 ≤ (44564798660391/100000000000000 : ℝ)^1625 := by
    have hnat : (5408655729 : ℕ)^2137*100000000000000^1625 ≤ 44564798660391^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408655729 10000000000 44564798660391 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5037429607/10000000000 : ℝ)^2137 ≤ (8117305869439/20000000000000 : ℝ)^1625 := by
    have hnat : (5037429607 : ℕ)^2137*20000000000000^1625 ≤ 8117305869439^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5037429607 10000000000 8117305869439 20000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (586248173/2500000000 : ℝ)^2137 ≤ (1856083997599/12500000000000 : ℝ)^1625 := by
    have hnat : (586248173 : ℕ)^2137*12500000000000^1625 ≤ 1856083997599^1625*2500000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      586248173 2500000000 1856083997599 12500000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5408655729/10000000000 : ℝ), (5037429607/10000000000 : ℝ), (-586248173/2500000000 : ℝ)] ![(44564798660391/100000000000000 : ℝ), (8117305869439/20000000000000 : ℝ), (1856083997599/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5408655729/10000000000 : ℝ)|^2137 ≤ (44564798660391/100000000000000 : ℝ)^1625
        have hw : |(5408655729/10000000000 : ℝ)|=(5408655729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5037429607/10000000000 : ℝ)|^2137 ≤ (8117305869439/20000000000000 : ℝ)^1625
        have hw : |(5037429607/10000000000 : ℝ)|=(5037429607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-586248173/2500000000 : ℝ)|^2137 ≤ (1856083997599/12500000000000 : ℝ)^1625
        have hw : |(-586248173/2500000000 : ℝ)|=(586248173/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s1_3 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2148636531/5000000000 : ℝ)*x 0 + (3702077747/10000000000 : ℝ)*x 1 + (2490931149/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2148636531/5000000000 : ℝ)^2137 ≤ (6586436517147/20000000000000 : ℝ)^1625 := by
    have hnat : (2148636531 : ℕ)^2137*20000000000000^1625 ≤ 6586436517147^1625*5000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148636531 5000000000 6586436517147 20000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3702077747/10000000000 : ℝ)^2137 ≤ (13534514649151/50000000000000 : ℝ)^1625 := by
    have hnat : (3702077747 : ℕ)^2137*50000000000000^1625 ≤ 13534514649151^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3702077747 10000000000 13534514649151 50000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2490931149/5000000000 : ℝ)^2137 ≤ (7999757621217/20000000000000 : ℝ)^1625 := by
    have hnat : (2490931149 : ℕ)^2137*20000000000000^1625 ≤ 7999757621217^1625*5000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2490931149 5000000000 7999757621217 20000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2148636531/5000000000 : ℝ), (3702077747/10000000000 : ℝ), (2490931149/5000000000 : ℝ)] ![(6586436517147/20000000000000 : ℝ), (13534514649151/50000000000000 : ℝ), (7999757621217/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2148636531/5000000000 : ℝ)|^2137 ≤ (6586436517147/20000000000000 : ℝ)^1625
        have hw : |(2148636531/5000000000 : ℝ)|=(2148636531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3702077747/10000000000 : ℝ)|^2137 ≤ (13534514649151/50000000000000 : ℝ)^1625
        have hw : |(3702077747/10000000000 : ℝ)|=(3702077747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2490931149/5000000000 : ℝ)|^2137 ≤ (7999757621217/20000000000000 : ℝ)^1625
        have hw : |(2490931149/5000000000 : ℝ)|=(2490931149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s1_4 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2015266791/10000000000 : ℝ)*x 0 + (630668249/1250000000 : ℝ)*x 1 + (5646865743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2015266791/10000000000 : ℝ)^2137 ≤ (2433177455357/20000000000000 : ℝ)^1625 := by
    have hnat : (2015266791 : ℕ)^2137*20000000000000^1625 ≤ 2433177455357^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015266791 10000000000 2433177455357 20000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (630668249/1250000000 : ℝ)^2137 ≤ (508380358379/1250000000000 : ℝ)^1625 := by
    have hnat : (630668249 : ℕ)^2137*1250000000000^1625 ≤ 508380358379^1625*1250000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      630668249 1250000000 508380358379 1250000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5646865743/10000000000 : ℝ)^2137 ≤ (11790921007707/25000000000000 : ℝ)^1625 := by
    have hnat : (5646865743 : ℕ)^2137*25000000000000^1625 ≤ 11790921007707^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5646865743 10000000000 11790921007707 25000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2015266791/10000000000 : ℝ), (630668249/1250000000 : ℝ), (5646865743/10000000000 : ℝ)] ![(2433177455357/20000000000000 : ℝ), (508380358379/1250000000000 : ℝ), (11790921007707/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2015266791/10000000000 : ℝ)|^2137 ≤ (2433177455357/20000000000000 : ℝ)^1625
        have hw : |(-2015266791/10000000000 : ℝ)|=(2015266791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(630668249/1250000000 : ℝ)|^2137 ≤ (508380358379/1250000000000 : ℝ)^1625
        have hw : |(630668249/1250000000 : ℝ)|=(630668249/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5646865743/10000000000 : ℝ)|^2137 ≤ (11790921007707/25000000000000 : ℝ)^1625
        have hw : |(5646865743/10000000000 : ℝ)|=(5646865743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s1_5 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5248805547/10000000000 : ℝ)*x 0 + (-43388917/250000000 : ℝ)*x 1 + (5646865437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5248805547/10000000000 : ℝ)^2137 ≤ (42840842429083/100000000000000 : ℝ)^1625 := by
    have hnat : (5248805547 : ℕ)^2137*100000000000000^1625 ≤ 42840842429083^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5248805547 10000000000 42840842429083 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43388917/250000000 : ℝ)^2137 ≤ (4997738443193/50000000000000 : ℝ)^1625 := by
    have hnat : (43388917 : ℕ)^2137*50000000000000^1625 ≤ 4997738443193^1625*250000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43388917 250000000 4997738443193 50000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5646865437/10000000000 : ℝ)^2137 ≤ (23581840334897/50000000000000 : ℝ)^1625 := by
    have hnat : (5646865437 : ℕ)^2137*50000000000000^1625 ≤ 23581840334897^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5646865437 10000000000 23581840334897 50000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5248805547/10000000000 : ℝ), (-43388917/250000000 : ℝ), (5646865437/10000000000 : ℝ)] ![(42840842429083/100000000000000 : ℝ), (4997738443193/50000000000000 : ℝ), (23581840334897/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5248805547/10000000000 : ℝ)|^2137 ≤ (42840842429083/100000000000000 : ℝ)^1625
        have hw : |(5248805547/10000000000 : ℝ)|=(5248805547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-43388917/250000000 : ℝ)|^2137 ≤ (4997738443193/50000000000000 : ℝ)^1625
        have hw : |(-43388917/250000000 : ℝ)|=(43388917/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5646865437/10000000000 : ℝ)|^2137 ≤ (23581840334897/50000000000000 : ℝ)^1625
        have hw : |(5646865437/10000000000 : ℝ)|=(5646865437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s1_6 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2624402727/5000000000 : ℝ)*x 0 + (1129373057/2000000000 : ℝ)*x 1 + (-216944629/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2624402727/5000000000 : ℝ)^2137 ≤ (42840841430851/100000000000000 : ℝ)^1625 := by
    have hnat : (2624402727 : ℕ)^2137*100000000000000^1625 ≤ 42840841430851^1625*5000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2624402727 5000000000 42840841430851 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1129373057/2000000000 : ℝ)^2137 ≤ (47163679000261/100000000000000 : ℝ)^1625 := by
    have hnat : (1129373057 : ℕ)^2137*100000000000000^1625 ≤ 47163679000261^1625*2000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129373057 2000000000 47163679000261 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216944629/1250000000 : ℝ)^2137 ≤ (1249434944047/12500000000000 : ℝ)^1625 := by
    have hnat : (216944629 : ℕ)^2137*12500000000000^1625 ≤ 1249434944047^1625*1250000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216944629 1250000000 1249434944047 12500000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2624402727/5000000000 : ℝ), (1129373057/2000000000 : ℝ), (-216944629/1250000000 : ℝ)] ![(42840841430851/100000000000000 : ℝ), (47163679000261/100000000000000 : ℝ), (1249434944047/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2624402727/5000000000 : ℝ)|^2137 ≤ (42840841430851/100000000000000 : ℝ)^1625
        have hw : |(2624402727/5000000000 : ℝ)|=(2624402727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1129373057/2000000000 : ℝ)|^2137 ≤ (47163679000261/100000000000000 : ℝ)^1625
        have hw : |(1129373057/2000000000 : ℝ)|=(1129373057/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-216944629/1250000000 : ℝ)|^2137 ≤ (1249434944047/12500000000000 : ℝ)^1625
        have hw : |(-216944629/1250000000 : ℝ)|=(216944629/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s1_7 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4298496719/10000000000 : ℝ)*x 0 + (620681897/1250000000 : ℝ)*x 1 + (743758007/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4298496719/10000000000 : ℝ)^2137 ≤ (6588903055629/20000000000000 : ℝ)^1625 := by
    have hnat : (4298496719 : ℕ)^2137*20000000000000^1625 ≤ 6588903055629^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4298496719 10000000000 6588903055629 20000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (620681897/1250000000 : ℝ)^2137 ≤ (39825641842591/100000000000000 : ℝ)^1625 := by
    have hnat : (620681897 : ℕ)^2137*100000000000000^1625 ≤ 39825641842591^1625*1250000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      620681897 1250000000 39825641842591 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (743758007/2000000000 : ℝ)^2137 ≤ (27229842851383/100000000000000 : ℝ)^1625 := by
    have hnat : (743758007 : ℕ)^2137*100000000000000^1625 ≤ 27229842851383^1625*2000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      743758007 2000000000 27229842851383 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4298496719/10000000000 : ℝ), (620681897/1250000000 : ℝ), (743758007/2000000000 : ℝ)] ![(6588903055629/20000000000000 : ℝ), (39825641842591/100000000000000 : ℝ), (27229842851383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4298496719/10000000000 : ℝ)|^2137 ≤ (6588903055629/20000000000000 : ℝ)^1625
        have hw : |(4298496719/10000000000 : ℝ)|=(4298496719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(620681897/1250000000 : ℝ)|^2137 ≤ (39825641842591/100000000000000 : ℝ)^1625
        have hw : |(620681897/1250000000 : ℝ)|=(620681897/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(743758007/2000000000 : ℝ)|^2137 ≤ (27229842851383/100000000000000 : ℝ)^1625
        have hw : |(743758007/2000000000 : ℝ)|=(743758007/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1314_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76813193/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13537/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (601/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (207/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4919/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13537/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (601/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13537/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (601/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13537/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (601/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13537/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (601/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13537/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (601/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13537/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (601/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (601/50000 : ℝ) ^ (4273/1024 : ℝ) ≤ (972134503827/100000000000000000000 : ℝ) := by
    have hpowers : (601/50000 : ℝ)^4273 ≤ (972134503827/100000000000000000000 : ℝ)^1024 := by
      have hnat : (601 : ℕ)^4273*100000000000000000000^1024 ≤ 972134503827^1024*50000^4273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        601 50000 972134503827 100000000000000000000 4273 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (601/50000 : ℝ)) (X := (972134503827/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (13537/50000 : ℝ) ^ (4273/1024 : ℝ) ≤ (428672376138492417/100000000000000000000 : ℝ) := by
    have hpowers : (13537/50000 : ℝ)^4273 ≤ (428672376138492417/100000000000000000000 : ℝ)^1024 := by
      have hnat : (13537 : ℕ)^4273*100000000000000000000^1024 ≤ 428672376138492417^1024*50000^4273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13537 50000 428672376138492417 100000000000000000000 4273 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13537/50000 : ℝ)) (X := (428672376138492417/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000972134503827/50000000000000000000 : ℝ) ≤ (5000000023296647/5000000000000000 : ℝ) ^ (4273/1024 : ℝ) := by
    have hpowers : (50000000972134503827/50000000000000000000 : ℝ)^1024 ≤ (5000000023296647/5000000000000000 : ℝ)^4273 := by
      have hnat : (50000000972134503827 : ℕ)^1024*5000000000000000^4273 ≤ 5000000023296647^4273*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000972134503827 50000000000000000000 5000000023296647 5000000000000000 1024 4273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000023296647/5000000000000000 : ℝ)) (X := (50000000972134503827/50000000000000000000 : ℝ)) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25107168337068249061/25000000000000000000 : ℝ) ≤ (2002051242302537/2000000000000000 : ℝ) ^ (4273/1024 : ℝ) := by
    have hpowers : (25107168337068249061/25000000000000000000 : ℝ)^1024 ≤ (2002051242302537/2000000000000000 : ℝ)^4273 := by
      have hnat : (25107168337068249061 : ℕ)^1024*2000000000000000^4273 ≤ 2002051242302537^4273*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25107168337068249061 25000000000000000000 2002051242302537 2000000000000000 1024 4273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2002051242302537/2000000000000000 : ℝ)) (X := (25107168337068249061/25000000000000000000 : ℝ)) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50428672376138492417/50000000000000000000 : ℝ) ≤ (2505128094108019/2500000000000000 : ℝ) ^ (4273/1024 : ℝ) := by
    have hpowers : (50428672376138492417/50000000000000000000 : ℝ)^1024 ≤ (2505128094108019/2500000000000000 : ℝ)^4273 := by
      have hnat : (50428672376138492417 : ℕ)^1024*2500000000000000^4273 ≤ 2505128094108019^4273*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50428672376138492417 50000000000000000000 2505128094108019 2500000000000000 1024 4273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2505128094108019/2500000000000000 : ℝ)) (X := (50428672376138492417/50000000000000000000 : ℝ)) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(972134503827/100000000000000000000 : ℝ) ≤ ((21557945448749623867/21560000000000000000 : ℝ)+2*(3418721639797/862400000000000 : ℝ)*(601/50000 : ℝ))^(4273/1024 : ℝ) := by
    rw [show (21557945448749623867/21560000000000000000 : ℝ)+2*(3418721639797/862400000000000 : ℝ)*(601/50000 : ℝ)=(5000000023296647/5000000000000000 : ℝ) by norm_num, show 1+2*(972134503827/100000000000000000000 : ℝ)=(50000000972134503827/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(428672376138492417/100000000000000000000 : ℝ)+(972134503827/100000000000000000000 : ℝ) ≤ ((21557945448749623867/21560000000000000000 : ℝ)+(3418721639797/862400000000000 : ℝ)*((13537/50000 : ℝ)+(601/50000 : ℝ)))^(4273/1024 : ℝ) := by
    rw [show (21557945448749623867/21560000000000000000 : ℝ)+(3418721639797/862400000000000 : ℝ)*((13537/50000 : ℝ)+(601/50000 : ℝ))=(2002051242302537/2000000000000000 : ℝ) by norm_num, show 1+(428672376138492417/100000000000000000000 : ℝ)+(972134503827/100000000000000000000 : ℝ)=(25107168337068249061/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(428672376138492417/100000000000000000000 : ℝ) ≤ ((21557945448749623867/21560000000000000000 : ℝ)+2*(3418721639797/862400000000000 : ℝ)*(13537/50000 : ℝ))^(4273/1024 : ℝ) := by
    rw [show (21557945448749623867/21560000000000000000 : ℝ)+2*(3418721639797/862400000000000 : ℝ)*(13537/50000 : ℝ)=(2505128094108019/2500000000000000 : ℝ) by norm_num, show 1+2*(428672376138492417/100000000000000000000 : ℝ)=(50428672376138492417/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (21557945448749623867/21560000000000000000 : ℝ)*(X 1 0+X 2 0)+(3418721639797/862400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4273/1024 : ℝ)) (lo := (601/50000 : ℝ)) (hi := (13537/50000 : ℝ)) (c := (21557945448749623867/21560000000000000000 : ℝ)) (alpha := (3418721639797/862400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (21557945448749623867/21560000000000000000 : ℝ)*(X 0 1+X 2 1)+(3418721639797/862400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4273/1024 : ℝ)) (lo := (601/50000 : ℝ)) (hi := (13537/50000 : ℝ)) (c := (21557945448749623867/21560000000000000000 : ℝ)) (alpha := (3418721639797/862400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (21557945448749623867/21560000000000000000 : ℝ)*(X 0 2+X 1 2)+(3418721639797/862400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4273/1024 : ℝ)) (lo := (601/50000 : ℝ)) (hi := (13537/50000 : ℝ)) (c := (21557945448749623867/21560000000000000000 : ℝ)) (alpha := (3418721639797/862400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-503669019/2500000000 : ℝ)*X 0 0+(1130985827/2000000000 : ℝ)*X 0 1+(2518714917/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2704327883/5000000000 : ℝ)*X 1 0+(-2344992411/10000000000 : ℝ)*X 1 1+(5037429789/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5408655729/10000000000 : ℝ)*X 2 0+(5037429607/10000000000 : ℝ)*X 2 1+(-586248173/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2148636531/5000000000 : ℝ)*X 0 0+(3702077747/10000000000 : ℝ)*X 0 1+(2490931149/5000000000 : ℝ)*X 0 2+(2148636531/5000000000 : ℝ)*X 1 0+(3702077747/10000000000 : ℝ)*X 1 1+(2490931149/5000000000 : ℝ)*X 1 2+(2148636531/5000000000 : ℝ)*X 2 0+(3702077747/10000000000 : ℝ)*X 2 1+(2490931149/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2015266791/10000000000 : ℝ)*X 0 0+(630668249/1250000000 : ℝ)*X 0 1+(5646865743/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5248805547/10000000000 : ℝ)*X 1 0+(-43388917/250000000 : ℝ)*X 1 1+(5646865437/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2624402727/5000000000 : ℝ)*X 2 0+(1129373057/2000000000 : ℝ)*X 2 1+(-216944629/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4298496719/10000000000 : ℝ)*X 0 0+(620681897/1250000000 : ℝ)*X 0 1+(743758007/2000000000 : ℝ)*X 0 2+(4298496719/10000000000 : ℝ)*X 1 0+(620681897/1250000000 : ℝ)*X 1 1+(743758007/2000000000 : ℝ)*X 1 2+(4298496719/10000000000 : ℝ)*X 2 0+(620681897/1250000000 : ℝ)*X 2 1+(743758007/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (474405053131477145759714259/49000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (55400063/50000000000000 : ℝ)*(base1) + (880487649/50000000000000 : ℝ)*(base19) + (437474203/25000000000000 : ℝ)*(base23) + (134657243/50000000000000 : ℝ)*(upper3) + (9712241/6250000000000 : ℝ)*(upper5) + (600211211708449/50000000000000 : ℝ)*(major0) + (600211211708449/50000000000000 : ℝ)*(major1) + (600211211708449/50000000000000 : ℝ)*(major2) + (809722482527303/50000000000000 : ℝ)*(sp0) + (404862994552309/25000000000000 : ℝ)*(sp1) + (809725994643861/50000000000000 : ℝ)*(sp2) + (156277155491629/20000000000000 : ℝ)*(sp3) + (4442465027/50000000000000 : ℝ)*(sp4) + (2448333231/50000000000000 : ℝ)*(sp7) + (195347696231183/25000000000000 : ℝ)*(f.failure) + (809726869592267/50000000000000 : ℝ)*(f.sum) + (430968578543/1960000000000000000000000000 : ℝ)*base65 + (869908791777520247/98000000000000000000000000000000 : ℝ)*base68 + (547055916075520247/98000000000000000000000000000000 : ℝ)*base70 + (588755311799520247/98000000000000000000000000000000 : ℝ)*base72 + (671165358137/1960000000000000000000000000 : ℝ)*base74 + (68964667480479753/98000000000000000000000000000000 : ℝ)*base75 + (40521841124479753/98000000000000000000000000000000 : ℝ)*base77 + (101568787625520247/98000000000000000000000000000000 : ℝ)*base80 + (2943668276863/1960000000000000000000000000 : ℝ)*base81 + (7397319/1250000000000000000000 : ℝ)*base89 + (7397319/1250000000000000000000 : ℝ)*base91 + (7397319/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (632966360829099760408300527/77000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17048481/100000000000000 : ℝ)*(base1) + (194201593/12500000000000 : ℝ)*(base19) + (369981097/25000000000000 : ℝ)*(base23) + (19386071/12500000000000 : ℝ)*(upper3) + (110711949/50000000000000 : ℝ)*(upper5) + (616149071388711/50000000000000 : ℝ)*(major0) + (616149071388711/50000000000000 : ℝ)*(major1) + (616149071388711/50000000000000 : ℝ)*(major2) + (1889952423/25000000000000 : ℝ)*(sp1) + (6107400749/100000000000000 : ℝ)*(sp2) + (103903524157947/6250000000000 : ℝ)*(sp4) + (831223628028117/50000000000000 : ℝ)*(sp5) + (831224391076767/50000000000000 : ℝ)*(sp6) + (200534906254069/25000000000000 : ℝ)*(sp7) + (802139642064757/100000000000000 : ℝ)*(f.failure) + (1662456369478671/100000000000000 : ℝ)*(f.sum) + (5851269325579/3080000000000000000000000000 : ℝ)*base66 + (389696367973091491/154000000000000000000000000000000 : ℝ)*base67 + (861406955629091491/154000000000000000000000000000000 : ℝ)*base69 + (900731022257091491/154000000000000000000000000000000 : ℝ)*base71 + (4519677008139/3080000000000000000000000000 : ℝ)*base74 + (1325478977889091491/154000000000000000000000000000000 : ℝ)*base75 + (121936991340908509/154000000000000000000000000000000 : ℝ)*base78 + (283109311572908509/154000000000000000000000000000000 : ℝ)*base80 + (9912962074261/3080000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (2060899/5000000000000000000000 : ℝ)*base90 + (2060899/5000000000000000000000 : ℝ)*base92 + (2060899/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1314_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76813193/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13537/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (601/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (207/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4919/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1314_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1314_s2_0 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-411465417/2000000000 : ℝ)*x 0 + (5487669691/10000000000 : ℝ)*x 1 + (5177412377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (411465417/2000000000 : ℝ)^2137 ≤ (6250447021167/50000000000000 : ℝ)^1625 := by
    have hnat : (411465417 : ℕ)^2137*50000000000000^1625 ≤ 6250447021167^1625*2000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411465417 2000000000 6250447021167 50000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5487669691/10000000000 : ℝ)^2137 ≤ (45422927816647/100000000000000 : ℝ)^1625 := by
    have hnat : (5487669691 : ℕ)^2137*100000000000000^1625 ≤ 45422927816647^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5487669691 10000000000 45422927816647 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5177412377/10000000000 : ℝ)^2137 ≤ (21038089058673/50000000000000 : ℝ)^1625 := by
    have hnat : (5177412377 : ℕ)^2137*50000000000000^1625 ≤ 21038089058673^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177412377 10000000000 21038089058673 50000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-411465417/2000000000 : ℝ), (5487669691/10000000000 : ℝ), (5177412377/10000000000 : ℝ)] ![(6250447021167/50000000000000 : ℝ), (45422927816647/100000000000000 : ℝ), (21038089058673/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-411465417/2000000000 : ℝ)|^2137 ≤ (6250447021167/50000000000000 : ℝ)^1625
        have hw : |(-411465417/2000000000 : ℝ)|=(411465417/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5487669691/10000000000 : ℝ)|^2137 ≤ (45422927816647/100000000000000 : ℝ)^1625
        have hw : |(5487669691/10000000000 : ℝ)|=(5487669691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5177412377/10000000000 : ℝ)|^2137 ≤ (21038089058673/50000000000000 : ℝ)^1625
        have hw : |(5177412377/10000000000 : ℝ)|=(5177412377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s2_1 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2683980129/5000000000 : ℝ)*x 0 + (-2217895627/10000000000 : ℝ)*x 1 + (2588705981/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2683980129/5000000000 : ℝ)^2137 ≤ (22062180794811/50000000000000 : ℝ)^1625 := by
    have hnat : (2683980129 : ℕ)^2137*50000000000000^1625 ≤ 22062180794811^1625*5000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2683980129 5000000000 22062180794811 50000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2217895627/10000000000 : ℝ)^2137 ≤ (13799464716013/100000000000000 : ℝ)^1625 := by
    have hnat : (2217895627 : ℕ)^2137*100000000000000^1625 ≤ 13799464716013^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2217895627 10000000000 13799464716013 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2588705981/5000000000 : ℝ)^2137 ≤ (328720106891/781250000000 : ℝ)^1625 := by
    have hnat : (2588705981 : ℕ)^2137*781250000000^1625 ≤ 328720106891^1625*5000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588705981 5000000000 328720106891 781250000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2683980129/5000000000 : ℝ), (-2217895627/10000000000 : ℝ), (2588705981/5000000000 : ℝ)] ![(22062180794811/50000000000000 : ℝ), (13799464716013/100000000000000 : ℝ), (328720106891/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2683980129/5000000000 : ℝ)|^2137 ≤ (22062180794811/50000000000000 : ℝ)^1625
        have hw : |(2683980129/5000000000 : ℝ)|=(2683980129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2217895627/10000000000 : ℝ)|^2137 ≤ (13799464716013/100000000000000 : ℝ)^1625
        have hw : |(-2217895627/10000000000 : ℝ)|=(2217895627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2588705981/5000000000 : ℝ)|^2137 ≤ (328720106891/781250000000 : ℝ)^1625
        have hw : |(2588705981/5000000000 : ℝ)|=(2588705981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s2_2 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2683979829/5000000000 : ℝ)*x 0 + (5177412537/10000000000 : ℝ)*x 1 + (-554473917/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2683979829/5000000000 : ℝ)^2137 ≤ (44124355103703/100000000000000 : ℝ)^1625 := by
    have hnat : (2683979829 : ℕ)^2137*100000000000000^1625 ≤ 44124355103703^1625*5000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2683979829 5000000000 44124355103703 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5177412537/10000000000 : ℝ)^2137 ≤ (2103808991367/5000000000000 : ℝ)^1625 := by
    have hnat : (5177412537 : ℕ)^2137*5000000000000^1625 ≤ 2103808991367^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177412537 10000000000 2103808991367 5000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (554473917/2500000000 : ℝ)^2137 ≤ (2759893010297/20000000000000 : ℝ)^1625 := by
    have hnat : (554473917 : ℕ)^2137*20000000000000^1625 ≤ 2759893010297^1625*2500000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554473917 2500000000 2759893010297 20000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2683979829/5000000000 : ℝ), (5177412537/10000000000 : ℝ), (-554473917/2500000000 : ℝ)] ![(44124355103703/100000000000000 : ℝ), (2103808991367/5000000000000 : ℝ), (2759893010297/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2683979829/5000000000 : ℝ)|^2137 ≤ (44124355103703/100000000000000 : ℝ)^1625
        have hw : |(2683979829/5000000000 : ℝ)|=(2683979829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5177412537/10000000000 : ℝ)|^2137 ≤ (2103808991367/5000000000000 : ℝ)^1625
        have hw : |(5177412537/10000000000 : ℝ)|=(5177412537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-554473917/2500000000 : ℝ)|^2137 ≤ (2759893010297/20000000000000 : ℝ)^1625
        have hw : |(-554473917/2500000000 : ℝ)|=(554473917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s2_3 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4327001003/10000000000 : ℝ)*x 0 + (4016758217/10000000000 : ℝ)*x 1 + (2329891629/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4327001003/10000000000 : ℝ)^2137 ≤ (33232109787319/100000000000000 : ℝ)^1625 := by
    have hnat : (4327001003 : ℕ)^2137*100000000000000^1625 ≤ 33232109787319^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4327001003 10000000000 33232109787319 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4016758217/10000000000 : ℝ)^2137 ≤ (30134643795189/100000000000000 : ℝ)^1625 := by
    have hnat : (4016758217 : ℕ)^2137*100000000000000^1625 ≤ 30134643795189^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4016758217 10000000000 30134643795189 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2329891629/5000000000 : ℝ)^2137 ≤ (36633246401061/100000000000000 : ℝ)^1625 := by
    have hnat : (2329891629 : ℕ)^2137*100000000000000^1625 ≤ 36633246401061^1625*5000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2329891629 5000000000 36633246401061 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4327001003/10000000000 : ℝ), (4016758217/10000000000 : ℝ), (2329891629/5000000000 : ℝ)] ![(33232109787319/100000000000000 : ℝ), (30134643795189/100000000000000 : ℝ), (36633246401061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4327001003/10000000000 : ℝ)|^2137 ≤ (33232109787319/100000000000000 : ℝ)^1625
        have hw : |(4327001003/10000000000 : ℝ)|=(4327001003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4016758217/10000000000 : ℝ)|^2137 ≤ (30134643795189/100000000000000 : ℝ)^1625
        have hw : |(4016758217/10000000000 : ℝ)|=(4016758217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2329891629/5000000000 : ℝ)|^2137 ≤ (36633246401061/100000000000000 : ℝ)^1625
        have hw : |(2329891629/5000000000 : ℝ)|=(2329891629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s2_4 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-514350393/2500000000 : ℝ)*x 0 + (5179420083/10000000000 : ℝ)*x 1 + (5485643547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (514350393/2500000000 : ℝ)^2137 ≤ (6250744627283/50000000000000 : ℝ)^1625 := by
    have hnat : (514350393 : ℕ)^2137*50000000000000^1625 ≤ 6250744627283^1625*2500000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514350393 2500000000 6250744627283 50000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5179420083/10000000000 : ℝ)^2137 ≤ (42097636714619/100000000000000 : ℝ)^1625 := by
    have hnat : (5179420083 : ℕ)^2137*100000000000000^1625 ≤ 42097636714619^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179420083 10000000000 42097636714619 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5485643547/10000000000 : ℝ)^2137 ≤ (11350218505049/25000000000000 : ℝ)^1625 := by
    have hnat : (5485643547 : ℕ)^2137*25000000000000^1625 ≤ 11350218505049^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5485643547 10000000000 11350218505049 25000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-514350393/2500000000 : ℝ), (5179420083/10000000000 : ℝ), (5485643547/10000000000 : ℝ)] ![(6250744627283/50000000000000 : ℝ), (42097636714619/100000000000000 : ℝ), (11350218505049/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-514350393/2500000000 : ℝ)|^2137 ≤ (6250744627283/50000000000000 : ℝ)^1625
        have hw : |(-514350393/2500000000 : ℝ)|=(514350393/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5179420083/10000000000 : ℝ)|^2137 ≤ (42097636714619/100000000000000 : ℝ)^1625
        have hw : |(5179420083/10000000000 : ℝ)|=(5179420083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5485643547/10000000000 : ℝ)|^2137 ≤ (11350218505049/25000000000000 : ℝ)^1625
        have hw : |(5485643547/10000000000 : ℝ)|=(5485643547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s2_5 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1322059769/2500000000 : ℝ)*x 0 + (-1909663573/10000000000 : ℝ)*x 1 + (5485643629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322059769/2500000000 : ℝ)^2137 ≤ (43264609448523/100000000000000 : ℝ)^1625 := by
    have hnat : (1322059769 : ℕ)^2137*100000000000000^1625 ≤ 43264609448523^1625*2500000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322059769 2500000000 43264609448523 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1909663573/10000000000 : ℝ)^2137 ≤ (11334515614953/100000000000000 : ℝ)^1625 := by
    have hnat : (1909663573 : ℕ)^2137*100000000000000^1625 ≤ 11334515614953^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1909663573 10000000000 11334515614953 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5485643629/10000000000 : ℝ)^2137 ≤ (22700437456341/50000000000000 : ℝ)^1625 := by
    have hnat : (5485643629 : ℕ)^2137*50000000000000^1625 ≤ 22700437456341^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5485643629 10000000000 22700437456341 50000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322059769/2500000000 : ℝ), (-1909663573/10000000000 : ℝ), (5485643629/10000000000 : ℝ)] ![(43264609448523/100000000000000 : ℝ), (11334515614953/100000000000000 : ℝ), (22700437456341/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322059769/2500000000 : ℝ)|^2137 ≤ (43264609448523/100000000000000 : ℝ)^1625
        have hw : |(1322059769/2500000000 : ℝ)|=(1322059769/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1909663573/10000000000 : ℝ)|^2137 ≤ (11334515614953/100000000000000 : ℝ)^1625
        have hw : |(-1909663573/10000000000 : ℝ)|=(1909663573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5485643629/10000000000 : ℝ)|^2137 ≤ (22700437456341/50000000000000 : ℝ)^1625
        have hw : |(5485643629/10000000000 : ℝ)|=(5485643629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s2_6 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1057647837/2000000000 : ℝ)*x 0 + (2742821777/5000000000 : ℝ)*x 1 + (-238707941/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057647837/2000000000 : ℝ)^2137 ≤ (5408076327657/12500000000000 : ℝ)^1625 := by
    have hnat : (1057647837 : ℕ)^2137*12500000000000^1625 ≤ 5408076327657^1625*2000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057647837 2000000000 5408076327657 12500000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2742821777/5000000000 : ℝ)^2137 ≤ (177347164439/390625000000 : ℝ)^1625 := by
    have hnat : (2742821777 : ℕ)^2137*390625000000^1625 ≤ 177347164439^1625*5000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2742821777 5000000000 177347164439 390625000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (238707941/1250000000 : ℝ)^2137 ≤ (11334515263709/100000000000000 : ℝ)^1625 := by
    have hnat : (238707941 : ℕ)^2137*100000000000000^1625 ≤ 11334515263709^1625*1250000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238707941 1250000000 11334515263709 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057647837/2000000000 : ℝ), (2742821777/5000000000 : ℝ), (-238707941/1250000000 : ℝ)] ![(5408076327657/12500000000000 : ℝ), (177347164439/390625000000 : ℝ), (11334515263709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057647837/2000000000 : ℝ)|^2137 ≤ (5408076327657/12500000000000 : ℝ)^1625
        have hw : |(1057647837/2000000000 : ℝ)|=(1057647837/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2742821777/5000000000 : ℝ)|^2137 ≤ (177347164439/390625000000 : ℝ)^1625
        have hw : |(2742821777/5000000000 : ℝ)|=(2742821777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-238707941/1250000000 : ℝ)|^2137 ≤ (11334515263709/100000000000000 : ℝ)^1625
        have hw : |(-238707941/1250000000 : ℝ)|=(238707941/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s2_7 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (86543081/200000000 : ℝ)*x 0 + (1163905039/2500000000 : ℝ)*x 1 + (4020962741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86543081/200000000 : ℝ)^2137 ≤ (4154206946641/12500000000000 : ℝ)^1625 := by
    have hnat : (86543081 : ℕ)^2137*12500000000000^1625 ≤ 4154206946641^1625*200000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86543081 200000000 4154206946641 12500000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1163905039/2500000000 : ℝ)^2137 ≤ (18295105950767/50000000000000 : ℝ)^1625 := by
    have hnat : (1163905039 : ℕ)^2137*50000000000000^1625 ≤ 18295105950767^1625*2500000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1163905039 2500000000 18295105950767 50000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4020962741/10000000000 : ℝ)^2137 ≤ (30176132507663/100000000000000 : ℝ)^1625 := by
    have hnat : (4020962741 : ℕ)^2137*100000000000000^1625 ≤ 30176132507663^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4020962741 10000000000 30176132507663 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(86543081/200000000 : ℝ), (1163905039/2500000000 : ℝ), (4020962741/10000000000 : ℝ)] ![(4154206946641/12500000000000 : ℝ), (18295105950767/50000000000000 : ℝ), (30176132507663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(86543081/200000000 : ℝ)|^2137 ≤ (4154206946641/12500000000000 : ℝ)^1625
        have hw : |(86543081/200000000 : ℝ)|=(86543081/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1163905039/2500000000 : ℝ)|^2137 ≤ (18295105950767/50000000000000 : ℝ)^1625
        have hw : |(1163905039/2500000000 : ℝ)|=(1163905039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4020962741/10000000000 : ℝ)|^2137 ≤ (30176132507663/100000000000000 : ℝ)^1625
        have hw : |(4020962741/10000000000 : ℝ)|=(4020962741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1314_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76813193/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4919/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (207/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (4831/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (811/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4919/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (207/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4919/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (207/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4919/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (207/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4919/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (207/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4919/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (207/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4919/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (207/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (207/3125 : ℝ) ^ (4273/1024 : ℝ) ≤ (1204231826867423/100000000000000000000 : ℝ) := by
    have hpowers : (207/3125 : ℝ)^4273 ≤ (1204231826867423/100000000000000000000 : ℝ)^1024 := by
      have hnat : (207 : ℕ)^4273*100000000000000000000^1024 ≤ 1204231826867423^1024*3125^4273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        207 3125 1204231826867423 100000000000000000000 4273 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (207/3125 : ℝ)) (X := (1204231826867423/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4919/25000 : ℝ) ^ (4273/1024 : ℝ) ≤ (113162655617409853/100000000000000000000 : ℝ) := by
    have hpowers : (4919/25000 : ℝ)^4273 ≤ (113162655617409853/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4919 : ℕ)^4273*100000000000000000000^1024 ≤ 113162655617409853^1024*25000^4273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4919 25000 113162655617409853 100000000000000000000 4273 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4919/25000 : ℝ)) (X := (113162655617409853/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001204231826867423/50000000000000000000 : ℝ) ≤ (5000028858462433/5000000000000000 : ℝ) ^ (4273/1024 : ℝ) := by
    have hpowers : (50001204231826867423/50000000000000000000 : ℝ)^1024 ≤ (5000028858462433/5000000000000000 : ℝ)^4273 := by
      have hnat : (50001204231826867423 : ℕ)^1024*5000000000000000^4273 ≤ 5000028858462433^4273*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001204231826867423 50000000000000000000 5000028858462433 5000000000000000 1024 4273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000028858462433/5000000000000000 : ℝ)) (X := (50001204231826867423/50000000000000000000 : ℝ)) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25028591721861069319/25000000000000000000 : ℝ) ≤ (2000547909230079/2000000000000000 : ℝ) ^ (4273/1024 : ℝ) := by
    have hpowers : (25028591721861069319/25000000000000000000 : ℝ)^1024 ≤ (2000547909230079/2000000000000000 : ℝ)^4273 := by
      have hnat : (25028591721861069319 : ℕ)^1024*2000000000000000^4273 ≤ 2000547909230079^4273*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25028591721861069319 25000000000000000000 2000547909230079 2000000000000000 1024 4273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000547909230079/2000000000000000 : ℝ)) (X := (25028591721861069319/25000000000000000000 : ℝ)) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50113162655617409853/50000000000000000000 : ℝ) ≤ (2501355343843981/2500000000000000 : ℝ) ^ (4273/1024 : ℝ) := by
    have hpowers : (50113162655617409853/50000000000000000000 : ℝ)^1024 ≤ (2501355343843981/2500000000000000 : ℝ)^4273 := by
      have hnat : (50113162655617409853 : ℕ)^1024*2500000000000000^4273 ≤ 2501355343843981^4273*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50113162655617409853 50000000000000000000 2501355343843981 2500000000000000 1024 4273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501355343843981/2500000000000000 : ℝ)) (X := (50113162655617409853/50000000000000000000 : ℝ)) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1204231826867423/100000000000000000000 : ℝ) ≤ ((3262130611193088571/3263000000000000000 : ℝ)+2*(2681829225529/1305200000000000 : ℝ)*(207/3125 : ℝ))^(4273/1024 : ℝ) := by
    rw [show (3262130611193088571/3263000000000000000 : ℝ)+2*(2681829225529/1305200000000000 : ℝ)*(207/3125 : ℝ)=(5000028858462433/5000000000000000 : ℝ) by norm_num, show 1+2*(1204231826867423/100000000000000000000 : ℝ)=(50001204231826867423/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(113162655617409853/100000000000000000000 : ℝ)+(1204231826867423/100000000000000000000 : ℝ) ≤ ((3262130611193088571/3263000000000000000 : ℝ)+(2681829225529/1305200000000000 : ℝ)*((4919/25000 : ℝ)+(207/3125 : ℝ)))^(4273/1024 : ℝ) := by
    rw [show (3262130611193088571/3263000000000000000 : ℝ)+(2681829225529/1305200000000000 : ℝ)*((4919/25000 : ℝ)+(207/3125 : ℝ))=(2000547909230079/2000000000000000 : ℝ) by norm_num, show 1+(113162655617409853/100000000000000000000 : ℝ)+(1204231826867423/100000000000000000000 : ℝ)=(25028591721861069319/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(113162655617409853/100000000000000000000 : ℝ) ≤ ((3262130611193088571/3263000000000000000 : ℝ)+2*(2681829225529/1305200000000000 : ℝ)*(4919/25000 : ℝ))^(4273/1024 : ℝ) := by
    rw [show (3262130611193088571/3263000000000000000 : ℝ)+2*(2681829225529/1305200000000000 : ℝ)*(4919/25000 : ℝ)=(2501355343843981/2500000000000000 : ℝ) by norm_num, show 1+2*(113162655617409853/100000000000000000000 : ℝ)=(50113162655617409853/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3262130611193088571/3263000000000000000 : ℝ)*(X 1 0+X 2 0)+(2681829225529/1305200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4273/1024 : ℝ)) (lo := (207/3125 : ℝ)) (hi := (4919/25000 : ℝ)) (c := (3262130611193088571/3263000000000000000 : ℝ)) (alpha := (2681829225529/1305200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3262130611193088571/3263000000000000000 : ℝ)*(X 0 1+X 2 1)+(2681829225529/1305200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4273/1024 : ℝ)) (lo := (207/3125 : ℝ)) (hi := (4919/25000 : ℝ)) (c := (3262130611193088571/3263000000000000000 : ℝ)) (alpha := (2681829225529/1305200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3262130611193088571/3263000000000000000 : ℝ)*(X 0 2+X 1 2)+(2681829225529/1305200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4273/1024 : ℝ)) (lo := (207/3125 : ℝ)) (hi := (4919/25000 : ℝ)) (c := (3262130611193088571/3263000000000000000 : ℝ)) (alpha := (2681829225529/1305200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-411465417/2000000000 : ℝ)*X 0 0+(5487669691/10000000000 : ℝ)*X 0 1+(5177412377/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2683980129/5000000000 : ℝ)*X 1 0+(-2217895627/10000000000 : ℝ)*X 1 1+(2588705981/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2683979829/5000000000 : ℝ)*X 2 0+(5177412537/10000000000 : ℝ)*X 2 1+(-554473917/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4327001003/10000000000 : ℝ)*X 0 0+(4016758217/10000000000 : ℝ)*X 0 1+(2329891629/5000000000 : ℝ)*X 0 2+(4327001003/10000000000 : ℝ)*X 1 0+(4016758217/10000000000 : ℝ)*X 1 1+(2329891629/5000000000 : ℝ)*X 1 2+(4327001003/10000000000 : ℝ)*X 2 0+(4016758217/10000000000 : ℝ)*X 2 1+(2329891629/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-514350393/2500000000 : ℝ)*X 0 0+(5179420083/10000000000 : ℝ)*X 0 1+(5485643547/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1322059769/2500000000 : ℝ)*X 1 0+(-1909663573/10000000000 : ℝ)*X 1 1+(5485643629/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1057647837/2000000000 : ℝ)*X 2 0+(2742821777/5000000000 : ℝ)*X 2 1+(-238707941/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((86543081/200000000 : ℝ)*X 0 0+(1163905039/2500000000 : ℝ)*X 0 1+(4020962741/10000000000 : ℝ)*X 0 2+(86543081/200000000 : ℝ)*X 1 0+(1163905039/2500000000 : ℝ)*X 1 1+(4020962741/10000000000 : ℝ)*X 1 2+(86543081/200000000 : ℝ)*X 2 0+(1163905039/2500000000 : ℝ)*X 2 1+(4020962741/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18515492989871625919282671/3137500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1087745119/50000000000000 : ℝ)*(base19) + (1292004251/100000000000000 : ℝ)*(base23) + (280862543/100000000000000 : ℝ)*(lower2) + (4328833/625000000000 : ℝ)*(upper3) + (38916939/25000000000000 : ℝ)*(upper5) + (597291995169743/25000000000000 : ℝ)*(major0) + (597291995169743/25000000000000 : ℝ)*(major1) + (597291995169743/25000000000000 : ℝ)*(major2) + (1611573893983979/50000000000000 : ℝ)*(sp0) + (1611576420005547/50000000000000 : ℝ)*(sp1) + (1611576861748541/50000000000000 : ℝ)*(sp2) + (777581200615551/50000000000000 : ℝ)*(sp3) + (57820267/800000000000 : ℝ)*(sp4) + (4586978439/25000000000000 : ℝ)*(sp7) + (777590374572429/50000000000000 : ℝ)*(f.failure) + (3223155015501333/100000000000000 : ℝ)*(f.sum) + (38391401087393/16315000000000000000000000000 : ℝ)*base66 + (491627095738449753/81575000000000000000000000000000 : ℝ)*base67 + (211964287596199753/81575000000000000000000000000000 : ℝ)*base69 + (675207784122074753/81575000000000000000000000000000 : ℝ)*base71 + (22924513640467/16315000000000000000000000000 : ℝ)*base73 + (736996557245424753/81575000000000000000000000000000 : ℝ)*base75 + (23781183068274753/81575000000000000000000000000000 : ℝ)*base77 + (230082478417124753/81575000000000000000000000000000 : ℝ)*base79 + (9484712551207/16315000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (18744203/2500000000000000000000 : ℝ)*base90 + (18744203/2500000000000000000000 : ℝ)*base92 + (18744203/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (108464384512315339997961/13052000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1624259411/100000000000000 : ℝ)*(base19) + (385658467/20000000000000 : ℝ)*(base23) + (11406961/5000000000000 : ℝ)*(upper3) + (90855337/100000000000000 : ℝ)*(lower4) + (473053/390625000000 : ℝ)*(upper5) + (484124047583699/20000000000000 : ℝ)*(major0) + (484124047583699/20000000000000 : ℝ)*(major1) + (484124047583699/20000000000000 : ℝ)*(major2) + (4314021131/25000000000000 : ℝ)*(sp1) + (21562493427/100000000000000 : ℝ)*(sp2) + (816396559170033/25000000000000 : ℝ)*(sp4) + (3265567356336197/100000000000000 : ℝ)*(sp5) + (326556274589437/10000000000000 : ℝ)*(sp6) + (1575653962151069/100000000000000 : ℝ)*(sp7) + (1575653962151069/100000000000000 : ℝ)*(f.failure) + (816396559170033/25000000000000 : ℝ)*(f.sum) + (73810235267421/13052000000000000000000000000 : ℝ)*base66 + (261831654534968371/65260000000000000000000000000000 : ℝ)*base68 + (528206518060651629/65260000000000000000000000000000 : ℝ)*base69 + (654398152597408371/65260000000000000000000000000000 : ℝ)*base72 + (68353277456649/13052000000000000000000000000 : ℝ)*base74 + (992406980488431629/65260000000000000000000000000000 : ℝ)*base75 + (43667353542928371/65260000000000000000000000000000 : ℝ)*base78 + (276080791946051629/65260000000000000000000000000000 : ℝ)*base79 + (5563058335811/2610400000000000000000000000 : ℝ)*base81 + (8253317/5000000000000000000000 : ℝ)*base89 + (8253317/5000000000000000000000 : ℝ)*base91 + (8253317/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1314_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76813193/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4919/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (207/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4831/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (811/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1314_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1314_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76813193/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4831/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (811/5000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1314_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1314_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1314_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76813193/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4831/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (811/5000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1314_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

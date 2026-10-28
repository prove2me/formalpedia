-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1048_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:53:06.501651+00:00
-- url     : https://prove2.me/submissions/0314045e-592d-4e52-b1fb-593bb448c167

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
theorem support_rectangle_w1048_s0_0 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-384384347/2000000000 : ℝ)*x 0 + (3038155981/5000000000 : ℝ)*x 1 + (2384235067/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (384384347/2000000000 : ℝ)^8241 ≤ (2784902565877/25000000000000 : ℝ)^6193 := by
    have hnat : (384384347 : ℕ)^8241*25000000000000^6193 ≤ 2784902565877^6193*2000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      384384347 2000000000 2784902565877 25000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3038155981/5000000000 : ℝ)^8241 ≤ (25766813420983/50000000000000 : ℝ)^6193 := by
    have hnat : (3038155981 : ℕ)^8241*50000000000000^6193 ≤ 25766813420983^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3038155981 5000000000 25766813420983 50000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2384235067/5000000000 : ℝ)^8241 ≤ (72903833743/195312500000 : ℝ)^6193 := by
    have hnat : (2384235067 : ℕ)^8241*195312500000^6193 ≤ 72903833743^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2384235067 5000000000 72903833743 195312500000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-384384347/2000000000 : ℝ), (3038155981/5000000000 : ℝ), (2384235067/5000000000 : ℝ)] ![(2784902565877/25000000000000 : ℝ), (25766813420983/50000000000000 : ℝ), (72903833743/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-384384347/2000000000 : ℝ)|^8241 ≤ (2784902565877/25000000000000 : ℝ)^6193
        have hw : |(-384384347/2000000000 : ℝ)|=(384384347/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3038155981/5000000000 : ℝ)|^8241 ≤ (25766813420983/50000000000000 : ℝ)^6193
        have hw : |(3038155981/5000000000 : ℝ)|=(3038155981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2384235067/5000000000 : ℝ)|^8241 ≤ (72903833743/195312500000 : ℝ)^6193
        have hw : |(2384235067/5000000000 : ℝ)|=(2384235067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s0_1 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2761042861/5000000000 : ℝ)*x 0 + (-2675263657/10000000000 : ℝ)*x 1 + (1192117553/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2761042861/5000000000 : ℝ)^8241 ≤ (45375110861607/100000000000000 : ℝ)^6193 := by
    have hnat : (2761042861 : ℕ)^8241*100000000000000^6193 ≤ 45375110861607^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2761042861 5000000000 45375110861607 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2675263657/10000000000 : ℝ)^8241 ≤ (1729812542953/10000000000000 : ℝ)^6193 := by
    have hnat : (2675263657 : ℕ)^8241*10000000000000^6193 ≤ 1729812542953^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675263657 10000000000 1729812542953 10000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1192117553/2500000000 : ℝ)^8241 ≤ (373267636889/1000000000000 : ℝ)^6193 := by
    have hnat : (1192117553 : ℕ)^8241*1000000000000^6193 ≤ 373267636889^6193*2500000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1192117553 2500000000 373267636889 1000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2761042861/5000000000 : ℝ), (-2675263657/10000000000 : ℝ), (1192117553/2500000000 : ℝ)] ![(45375110861607/100000000000000 : ℝ), (1729812542953/10000000000000 : ℝ), (373267636889/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2761042861/5000000000 : ℝ)|^8241 ≤ (45375110861607/100000000000000 : ℝ)^6193
        have hw : |(2761042861/5000000000 : ℝ)|=(2761042861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2675263657/10000000000 : ℝ)|^8241 ≤ (1729812542953/10000000000000 : ℝ)^6193
        have hw : |(-2675263657/10000000000 : ℝ)|=(2675263657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1192117553/2500000000 : ℝ)|^8241 ≤ (373267636889/1000000000000 : ℝ)^6193
        have hw : |(1192117553/2500000000 : ℝ)|=(1192117553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s0_2 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5522085739/10000000000 : ℝ)*x 0 + (4768470199/10000000000 : ℝ)*x 1 + (-668815913/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5522085739/10000000000 : ℝ)^8241 ≤ (45375111047491/100000000000000 : ℝ)^6193 := by
    have hnat : (5522085739 : ℕ)^8241*100000000000000^6193 ≤ 45375111047491^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5522085739 10000000000 45375111047491 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4768470199/10000000000 : ℝ)^8241 ≤ (18663381776743/50000000000000 : ℝ)^6193 := by
    have hnat : (4768470199 : ℕ)^8241*50000000000000^6193 ≤ 18663381776743^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4768470199 10000000000 18663381776743 50000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (668815913/2500000000 : ℝ)^8241 ≤ (17298125386509/100000000000000 : ℝ)^6193 := by
    have hnat : (668815913 : ℕ)^8241*100000000000000^6193 ≤ 17298125386509^6193*2500000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668815913 2500000000 17298125386509 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5522085739/10000000000 : ℝ), (4768470199/10000000000 : ℝ), (-668815913/2500000000 : ℝ)] ![(45375111047491/100000000000000 : ℝ), (18663381776743/50000000000000 : ℝ), (17298125386509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5522085739/10000000000 : ℝ)|^8241 ≤ (45375111047491/100000000000000 : ℝ)^6193
        have hw : |(5522085739/10000000000 : ℝ)|=(5522085739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4768470199/10000000000 : ℝ)|^8241 ≤ (18663381776743/50000000000000 : ℝ)^6193
        have hw : |(4768470199/10000000000 : ℝ)|=(4768470199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-668815913/2500000000 : ℝ)|^8241 ≤ (17298125386509/100000000000000 : ℝ)^6193
        have hw : |(-668815913/2500000000 : ℝ)|=(668815913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s0_3 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (841740817/2000000000 : ℝ)*x 0 + (97682607/312500000 : ℝ)*x 1 + (1135975081/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (841740817/2000000000 : ℝ)^8241 ≤ (31612277661667/100000000000000 : ℝ)^6193 := by
    have hnat : (841740817 : ℕ)^8241*100000000000000^6193 ≤ 31612277661667^6193*2000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      841740817 2000000000 31612277661667 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (97682607/312500000 : ℝ)^8241 ≤ (2659897734923/12500000000000 : ℝ)^6193 := by
    have hnat : (97682607 : ℕ)^8241*12500000000000^6193 ≤ 2659897734923^6193*312500000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97682607 312500000 2659897734923 12500000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1135975081/2000000000 : ℝ)^8241 ≤ (2355427022559/5000000000000 : ℝ)^6193 := by
    have hnat : (1135975081 : ℕ)^8241*5000000000000^6193 ≤ 2355427022559^6193*2000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135975081 2000000000 2355427022559 5000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(841740817/2000000000 : ℝ), (97682607/312500000 : ℝ), (1135975081/2000000000 : ℝ)] ![(31612277661667/100000000000000 : ℝ), (2659897734923/12500000000000 : ℝ), (2355427022559/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(841740817/2000000000 : ℝ)|^8241 ≤ (31612277661667/100000000000000 : ℝ)^6193
        have hw : |(841740817/2000000000 : ℝ)|=(841740817/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(97682607/312500000 : ℝ)|^8241 ≤ (2659897734923/12500000000000 : ℝ)^6193
        have hw : |(97682607/312500000 : ℝ)|=(97682607/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1135975081/2000000000 : ℝ)|^8241 ≤ (2355427022559/5000000000000 : ℝ)^6193
        have hw : |(1135975081/2000000000 : ℝ)|=(1135975081/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s0_4 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-385469929/2000000000 : ℝ)*x 0 + (4802247203/10000000000 : ℝ)*x 1 + (3020677767/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (385469929/2000000000 : ℝ)^8241 ≤ (5590747143829/50000000000000 : ℝ)^6193 := by
    have hnat : (385469929 : ℕ)^8241*50000000000000^6193 ≤ 5590747143829^6193*2000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385469929 2000000000 5590747143829 50000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4802247203/10000000000 : ℝ)^8241 ≤ (18839505876279/50000000000000 : ℝ)^6193 := by
    have hnat : (4802247203 : ℕ)^8241*50000000000000^6193 ≤ 18839505876279^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4802247203 10000000000 18839505876279 50000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3020677767/5000000000 : ℝ)^8241 ≤ (25569746972707/50000000000000 : ℝ)^6193 := by
    have hnat : (3020677767 : ℕ)^8241*50000000000000^6193 ≤ 25569746972707^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3020677767 5000000000 25569746972707 50000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-385469929/2000000000 : ℝ), (4802247203/10000000000 : ℝ), (3020677767/5000000000 : ℝ)] ![(5590747143829/50000000000000 : ℝ), (18839505876279/50000000000000 : ℝ), (25569746972707/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-385469929/2000000000 : ℝ)|^8241 ≤ (5590747143829/50000000000000 : ℝ)^6193
        have hw : |(-385469929/2000000000 : ℝ)|=(385469929/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4802247203/10000000000 : ℝ)|^8241 ≤ (18839505876279/50000000000000 : ℝ)^6193
        have hw : |(4802247203/10000000000 : ℝ)|=(4802247203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3020677767/5000000000 : ℝ)|^8241 ≤ (25569746972707/50000000000000 : ℝ)^6193
        have hw : |(3020677767/5000000000 : ℝ)|=(3020677767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s0_5 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5167218267/10000000000 : ℝ)*x 0 + (-701188781/5000000000 : ℝ)*x 1 + (3020677881/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5167218267/10000000000 : ℝ)^8241 ≤ (10384175124407/25000000000000 : ℝ)^6193 := by
    have hnat : (5167218267 : ℕ)^8241*25000000000000^6193 ≤ 10384175124407^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5167218267 10000000000 10384175124407 25000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (701188781/5000000000 : ℝ)^8241 ≤ (3661901489251/50000000000000 : ℝ)^6193 := by
    have hnat : (701188781 : ℕ)^8241*50000000000000^6193 ≤ 3661901489251^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      701188781 5000000000 3661901489251 50000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3020677881/5000000000 : ℝ)^8241 ≤ (25569748256827/50000000000000 : ℝ)^6193 := by
    have hnat : (3020677881 : ℕ)^8241*50000000000000^6193 ≤ 25569748256827^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3020677881 5000000000 25569748256827 50000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5167218267/10000000000 : ℝ), (-701188781/5000000000 : ℝ), (3020677881/5000000000 : ℝ)] ![(10384175124407/25000000000000 : ℝ), (3661901489251/50000000000000 : ℝ), (25569748256827/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5167218267/10000000000 : ℝ)|^8241 ≤ (10384175124407/25000000000000 : ℝ)^6193
        have hw : |(5167218267/10000000000 : ℝ)|=(5167218267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-701188781/5000000000 : ℝ)|^8241 ≤ (3661901489251/50000000000000 : ℝ)^6193
        have hw : |(-701188781/5000000000 : ℝ)|=(701188781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3020677881/5000000000 : ℝ)|^8241 ≤ (25569748256827/50000000000000 : ℝ)^6193
        have hw : |(3020677881/5000000000 : ℝ)|=(3020677881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s0_6 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5167217533/10000000000 : ℝ)*x 0 + (1510339099/2500000000 : ℝ)*x 1 + (-21912151/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5167217533/10000000000 : ℝ)^8241 ≤ (20768346323087/50000000000000 : ℝ)^6193 := by
    have hnat : (5167217533 : ℕ)^8241*50000000000000^6193 ≤ 20768346323087^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5167217533 10000000000 20768346323087 50000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1510339099/2500000000 : ℝ)^8241 ≤ (25569751827583/50000000000000 : ℝ)^6193 := by
    have hnat : (1510339099 : ℕ)^8241*50000000000000^6193 ≤ 25569751827583^6193*2500000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1510339099 2500000000 25569751827583 50000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21912151/156250000 : ℝ)^8241 ≤ (3661901843673/50000000000000 : ℝ)^6193 := by
    have hnat : (21912151 : ℕ)^8241*50000000000000^6193 ≤ 3661901843673^6193*156250000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21912151 156250000 3661901843673 50000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5167217533/10000000000 : ℝ), (1510339099/2500000000 : ℝ), (-21912151/156250000 : ℝ)] ![(20768346323087/50000000000000 : ℝ), (25569751827583/50000000000000 : ℝ), (3661901843673/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5167217533/10000000000 : ℝ)|^8241 ≤ (20768346323087/50000000000000 : ℝ)^6193
        have hw : |(5167217533/10000000000 : ℝ)|=(5167217533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1510339099/2500000000 : ℝ)|^8241 ≤ (25569751827583/50000000000000 : ℝ)^6193
        have hw : |(1510339099/2500000000 : ℝ)|=(1510339099/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-21912151/156250000 : ℝ)|^8241 ≤ (3661901843673/50000000000000 : ℝ)^6193
        have hw : |(-21912151/156250000 : ℝ)|=(21912151/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s0_7 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4219302949/10000000000 : ℝ)*x 0 + (1403478591/2500000000 : ℝ)*x 1 + (3194107929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4219302949/10000000000 : ℝ)^8241 ≤ (31718258231617/100000000000000 : ℝ)^6193 := by
    have hnat : (4219302949 : ℕ)^8241*100000000000000^6193 ≤ 31718258231617^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4219302949 10000000000 31718258231617 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1403478591/2500000000 : ℝ)^8241 ≤ (1855277961353/4000000000000 : ℝ)^6193 := by
    have hnat : (1403478591 : ℕ)^8241*4000000000000^6193 ≤ 1855277961353^6193*2500000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1403478591 2500000000 1855277961353 4000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3194107929/10000000000 : ℝ)^8241 ≤ (4379958542111/20000000000000 : ℝ)^6193 := by
    have hnat : (3194107929 : ℕ)^8241*20000000000000^6193 ≤ 4379958542111^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3194107929 10000000000 4379958542111 20000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4219302949/10000000000 : ℝ), (1403478591/2500000000 : ℝ), (3194107929/10000000000 : ℝ)] ![(31718258231617/100000000000000 : ℝ), (1855277961353/4000000000000 : ℝ), (4379958542111/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4219302949/10000000000 : ℝ)|^8241 ≤ (31718258231617/100000000000000 : ℝ)^6193
        have hw : |(4219302949/10000000000 : ℝ)|=(4219302949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1403478591/2500000000 : ℝ)|^8241 ≤ (1855277961353/4000000000000 : ℝ)^6193
        have hw : |(1403478591/2500000000 : ℝ)|=(1403478591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3194107929/10000000000 : ℝ)|^8241 ≤ (4379958542111/20000000000000 : ℝ)^6193
        have hw : |(3194107929/10000000000 : ℝ)|=(3194107929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1048_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147643001/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1409/5000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (515/128 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^515 ≤ (0 : ℝ)^128 := by
      have hnat : (0 : ℕ)^515*1^128 ≤ 0^128*1^515 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 515 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (515/128 : ℝ) ≤ (2505608688555957049/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^515 ≤ (2505608688555957049/100000000000000000000 : ℝ)^128 := by
      have hnat : (2 : ℕ)^515*100000000000000000000^128 ≤ 2505608688555957049^128*5^515 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2505608688555957049 100000000000000000000 515 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2505608688555957049/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (515/128 : ℝ) := by
    have hpowers : (1 : ℝ)^128 ≤ (1 : ℝ)^515 := by
      have hnat : (1 : ℕ)^128*1^515 ≤ 1^515*1^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 128 515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (102505608688555957049/100000000000000000000 : ℝ) ≤ (5030848738343651/5000000000000000 : ℝ) ^ (515/128 : ℝ) := by
    have hpowers : (102505608688555957049/100000000000000000000 : ℝ)^128 ≤ (5030848738343651/5000000000000000 : ℝ)^515 := by
      have hnat : (102505608688555957049 : ℕ)^128*5000000000000000^515 ≤ 5030848738343651^515*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102505608688555957049 100000000000000000000 5030848738343651 5000000000000000 128 515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5030848738343651/5000000000000000 : ℝ)) (X := (102505608688555957049/100000000000000000000 : ℝ)) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (52505608688555957049/50000000000000000000 : ℝ) ≤ (2530848738343651/2500000000000000 : ℝ) ^ (515/128 : ℝ) := by
    have hpowers : (52505608688555957049/50000000000000000000 : ℝ)^128 ≤ (2530848738343651/2500000000000000 : ℝ)^515 := by
      have hnat : (52505608688555957049 : ℕ)^128*2500000000000000^515 ≤ 2530848738343651^515*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52505608688555957049 50000000000000000000 2530848738343651 2500000000000000 128 515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2530848738343651/2500000000000000 : ℝ)) (X := (52505608688555957049/50000000000000000000 : ℝ)) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(30848738343651/2000000000000000 : ℝ)*(0 : ℝ))^(515/128 : ℝ) := by
    rw [show (1 : ℝ)+2*(30848738343651/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2505608688555957049/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(30848738343651/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(515/128 : ℝ) := by
    rw [show (1 : ℝ)+(30848738343651/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5030848738343651/5000000000000000 : ℝ) by norm_num, show 1+(2505608688555957049/100000000000000000000 : ℝ)+(0 : ℝ)=(102505608688555957049/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2505608688555957049/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(30848738343651/2000000000000000 : ℝ)*(2/5 : ℝ))^(515/128 : ℝ) := by
    rw [show (1 : ℝ)+2*(30848738343651/2000000000000000 : ℝ)*(2/5 : ℝ)=(2530848738343651/2500000000000000 : ℝ) by norm_num, show 1+2*(2505608688555957049/100000000000000000000 : ℝ)=(52505608688555957049/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(30848738343651/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (515/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30848738343651/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(30848738343651/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (515/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30848738343651/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(30848738343651/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (515/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30848738343651/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-384384347/2000000000 : ℝ)*X 0 0+(3038155981/5000000000 : ℝ)*X 0 1+(2384235067/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2761042861/5000000000 : ℝ)*X 1 0+(-2675263657/10000000000 : ℝ)*X 1 1+(1192117553/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5522085739/10000000000 : ℝ)*X 2 0+(4768470199/10000000000 : ℝ)*X 2 1+(-668815913/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((841740817/2000000000 : ℝ)*X 0 0+(97682607/312500000 : ℝ)*X 0 1+(1135975081/2000000000 : ℝ)*X 0 2+(841740817/2000000000 : ℝ)*X 1 0+(97682607/312500000 : ℝ)*X 1 1+(1135975081/2000000000 : ℝ)*X 1 2+(841740817/2000000000 : ℝ)*X 2 0+(97682607/312500000 : ℝ)*X 2 1+(1135975081/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-385469929/2000000000 : ℝ)*X 0 0+(4802247203/10000000000 : ℝ)*X 0 1+(3020677767/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5167218267/10000000000 : ℝ)*X 1 0+(-701188781/5000000000 : ℝ)*X 1 1+(3020677881/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5167217533/10000000000 : ℝ)*X 2 0+(1510339099/2500000000 : ℝ)*X 2 1+(-21912151/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4219302949/10000000000 : ℝ)*X 0 0+(1403478591/2500000000 : ℝ)*X 0 1+(3194107929/10000000000 : ℝ)*X 0 2+(4219302949/10000000000 : ℝ)*X 1 0+(1403478591/2500000000 : ℝ)*X 1 1+(3194107929/10000000000 : ℝ)*X 1 2+(4219302949/10000000000 : ℝ)*X 2 0+(1403478591/2500000000 : ℝ)*X 2 1+(3194107929/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (289910894413892135087877/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11630071/20000000000000 : ℝ)*(base1) + (1440802009/100000000000000 : ℝ)*(base19) + (671680473/50000000000000 : ℝ)*(base23) + (24948749/25000000000000 : ℝ)*(base24) + (82641869/25000000000000 : ℝ)*(upper3) + (578084193962703/100000000000000 : ℝ)*(major0) + (578084193962703/100000000000000 : ℝ)*(major1) + (578084193962703/100000000000000 : ℝ)*(major2) + (764623210883939/100000000000000 : ℝ)*(sp0) + (191156216403533/25000000000000 : ℝ)*(sp1) + (382312431630099/50000000000000 : ℝ)*(sp2) + (97884820499061/25000000000000 : ℝ)*(sp3) + (3153682557/100000000000000 : ℝ)*(sp4) + (2548088729/100000000000000 : ℝ)*(sp7) + (391541888235327/100000000000000 : ℝ)*(f.failure) + (38231315320807/5000000000000 : ℝ)*(f.sum) + (187807922251347/100000000000000000000000000000 : ℝ)*base66 + (1986485549351347/200000000000000000000000000000 : ℝ)*base68 + (935123574151347/200000000000000000000000000000 : ℝ)*base70 + (1129930082151347/200000000000000000000000000000 : ℝ)*base72 + (287491917951347/100000000000000000000000000000 : ℝ)*base74 + (2226171118151347/200000000000000000000000000000 : ℝ)*base76 + (598628685751347/200000000000000000000000000000 : ℝ)*base78 + (1687150151951347/200000000000000000000000000000 : ℝ)*base80 + (258510505651347/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (27503673/10000000000000000000000 : ℝ)*base90 + (27503673/10000000000000000000000 : ℝ)*base92 + (27503673/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (435470224542925559300073/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (432981/3125000000000 : ℝ)*(base1) + (45777821/2000000000000 : ℝ)*(base19) + (1089966807/50000000000000 : ℝ)*(base23) + (636717563/100000000000000 : ℝ)*(base45) + (3492533/1250000000000 : ℝ)*(upper3) + (109257089/50000000000000 : ℝ)*(upper5) + (610140147522959/100000000000000 : ℝ)*(major0) + (610140147522959/100000000000000 : ℝ)*(major1) + (610140147522959/100000000000000 : ℝ)*(major2) + (41351779/50000000000000 : ℝ)*(sp2) + (807026330034743/100000000000000 : ℝ)*(sp4) + (807024027288301/100000000000000 : ℝ)*(sp5) + (403512026771089/50000000000000 : ℝ)*(sp6) + (413253674697687/100000000000000 : ℝ)*(sp7) + (413253688553079/100000000000000 : ℝ)*(f.failure) + (16140526323587/2000000000000 : ℝ)*(f.sum) + (114625881583309/100000000000000000000000000000 : ℝ)*base65 + (808722174983309/200000000000000000000000000000 : ℝ)*base67 + (1968983442616691/200000000000000000000000000000 : ℝ)*base70 + (186022511616691/200000000000000000000000000000 : ℝ)*base72 + (445074763783309/100000000000000000000000000000 : ℝ)*base73 + (541772037383309/200000000000000000000000000000 : ℝ)*base75 + (671903114583309/200000000000000000000000000000 : ℝ)*base77 + (1663569234783309/200000000000000000000000000000 : ℝ)*base79 + (177695267116691/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (31350079/10000000000000000000000 : ℝ)*base89 + (31350079/10000000000000000000000 : ℝ)*base91 + (31350079/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1048_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147643001/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1409/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1048_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1048_s1_0 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2133334921/10000000000 : ℝ)*x 0 + (2863704741/5000000000 : ℝ)*x 1 + (4981967503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2133334921/10000000000 : ℝ)^8241 ≤ (12799163506539/100000000000000 : ℝ)^6193 := by
    have hnat : (2133334921 : ℕ)^8241*100000000000000^6193 ≤ 12799163506539^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133334921 10000000000 12799163506539 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2863704741/5000000000 : ℝ)^8241 ≤ (47633884930333/100000000000000 : ℝ)^6193 := by
    have hnat : (2863704741 : ℕ)^8241*100000000000000^6193 ≤ 47633884930333^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2863704741 5000000000 47633884930333 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4981967503/10000000000 : ℝ)^8241 ≤ (39566951551563/100000000000000 : ℝ)^6193 := by
    have hnat : (4981967503 : ℕ)^8241*100000000000000^6193 ≤ 39566951551563^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4981967503 10000000000 39566951551563 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2133334921/10000000000 : ℝ), (2863704741/5000000000 : ℝ), (4981967503/10000000000 : ℝ)] ![(12799163506539/100000000000000 : ℝ), (47633884930333/100000000000000 : ℝ), (39566951551563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2133334921/10000000000 : ℝ)|^8241 ≤ (12799163506539/100000000000000 : ℝ)^6193
        have hw : |(-2133334921/10000000000 : ℝ)|=(2133334921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2863704741/5000000000 : ℝ)|^8241 ≤ (47633884930333/100000000000000 : ℝ)^6193
        have hw : |(2863704741/5000000000 : ℝ)|=(2863704741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4981967503/10000000000 : ℝ)|^8241 ≤ (39566951551563/100000000000000 : ℝ)^6193
        have hw : |(4981967503/10000000000 : ℝ)|=(4981967503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s1_1 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1356077661/2500000000 : ℝ)*x 0 + (-2537607753/10000000000 : ℝ)*x 1 + (4981967827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1356077661/2500000000 : ℝ)^8241 ≤ (22154572686697/50000000000000 : ℝ)^6193 := by
    have hnat : (1356077661 : ℕ)^8241*50000000000000^6193 ≤ 22154572686697^6193*2500000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356077661 2500000000 22154572686697 50000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2537607753/10000000000 : ℝ)^8241 ≤ (3224779925943/20000000000000 : ℝ)^6193 := by
    have hnat : (2537607753 : ℕ)^8241*20000000000000^6193 ≤ 3224779925943^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2537607753 10000000000 3224779925943 20000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4981967827/10000000000 : ℝ)^8241 ≤ (7913390995147/20000000000000 : ℝ)^6193 := by
    have hnat : (4981967827 : ℕ)^8241*20000000000000^6193 ≤ 7913390995147^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4981967827 10000000000 7913390995147 20000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1356077661/2500000000 : ℝ), (-2537607753/10000000000 : ℝ), (4981967827/10000000000 : ℝ)] ![(22154572686697/50000000000000 : ℝ), (3224779925943/20000000000000 : ℝ), (7913390995147/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1356077661/2500000000 : ℝ)|^8241 ≤ (22154572686697/50000000000000 : ℝ)^6193
        have hw : |(1356077661/2500000000 : ℝ)|=(1356077661/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2537607753/10000000000 : ℝ)|^8241 ≤ (3224779925943/20000000000000 : ℝ)^6193
        have hw : |(-2537607753/10000000000 : ℝ)|=(2537607753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4981967827/10000000000 : ℝ)|^8241 ≤ (7913390995147/20000000000000 : ℝ)^6193
        have hw : |(4981967827/10000000000 : ℝ)|=(4981967827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s1_2 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5424311069/10000000000 : ℝ)*x 0 + (4981967309/10000000000 : ℝ)*x 1 + (-507521571/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5424311069/10000000000 : ℝ)^8241 ≤ (11077287498281/25000000000000 : ℝ)^6193 := by
    have hnat : (5424311069 : ℕ)^8241*25000000000000^6193 ≤ 11077287498281^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424311069 10000000000 11077287498281 25000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4981967309/10000000000 : ℝ)^8241 ≤ (39566949501287/100000000000000 : ℝ)^6193 := by
    have hnat : (4981967309 : ℕ)^8241*100000000000000^6193 ≤ 39566949501287^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4981967309 10000000000 39566949501287 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (507521571/2000000000 : ℝ)^8241 ≤ (16123900492147/100000000000000 : ℝ)^6193 := by
    have hnat : (507521571 : ℕ)^8241*100000000000000^6193 ≤ 16123900492147^6193*2000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507521571 2000000000 16123900492147 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5424311069/10000000000 : ℝ), (4981967309/10000000000 : ℝ), (-507521571/2000000000 : ℝ)] ![(11077287498281/25000000000000 : ℝ), (39566949501287/100000000000000 : ℝ), (16123900492147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5424311069/10000000000 : ℝ)|^8241 ≤ (11077287498281/25000000000000 : ℝ)^6193
        have hw : |(5424311069/10000000000 : ℝ)|=(5424311069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4981967309/10000000000 : ℝ)|^8241 ≤ (39566949501287/100000000000000 : ℝ)^6193
        have hw : |(4981967309/10000000000 : ℝ)|=(4981967309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-507521571/2000000000 : ℝ)|^8241 ≤ (16123900492147/100000000000000 : ℝ)^6193
        have hw : |(-507521571/2000000000 : ℝ)|=(507521571/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s1_3 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4325284791/10000000000 : ℝ)*x 0 + (914757457/2500000000 : ℝ)*x 1 + (5114772341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4325284791/10000000000 : ℝ)^8241 ≤ (32782815333103/100000000000000 : ℝ)^6193 := by
    have hnat : (4325284791 : ℕ)^8241*100000000000000^6193 ≤ 32782815333103^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4325284791 10000000000 32782815333103 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (914757457/2500000000 : ℝ)^8241 ≤ (1312027214537/5000000000000 : ℝ)^6193 := by
    have hnat : (914757457 : ℕ)^8241*5000000000000^6193 ≤ 1312027214537^6193*2500000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      914757457 2500000000 1312027214537 5000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5114772341/10000000000 : ℝ)^8241 ≤ (40976640366603/100000000000000 : ℝ)^6193 := by
    have hnat : (5114772341 : ℕ)^8241*100000000000000^6193 ≤ 40976640366603^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5114772341 10000000000 40976640366603 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4325284791/10000000000 : ℝ), (914757457/2500000000 : ℝ), (5114772341/10000000000 : ℝ)] ![(32782815333103/100000000000000 : ℝ), (1312027214537/5000000000000 : ℝ), (40976640366603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4325284791/10000000000 : ℝ)|^8241 ≤ (32782815333103/100000000000000 : ℝ)^6193
        have hw : |(4325284791/10000000000 : ℝ)|=(4325284791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(914757457/2500000000 : ℝ)|^8241 ≤ (1312027214537/5000000000000 : ℝ)^6193
        have hw : |(914757457/2500000000 : ℝ)|=(914757457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5114772341/10000000000 : ℝ)|^8241 ≤ (40976640366603/100000000000000 : ℝ)^6193
        have hw : |(5114772341/10000000000 : ℝ)|=(5114772341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s1_4 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2134285707/10000000000 : ℝ)*x 0 + (156016089/312500000 : ℝ)*x 1 + (114332893/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2134285707/10000000000 : ℝ)^8241 ≤ (6403377403289/50000000000000 : ℝ)^6193 := by
    have hnat : (2134285707 : ℕ)^8241*50000000000000^6193 ≤ 6403377403289^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134285707 10000000000 6403377403289 50000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (156016089/312500000 : ℝ)^8241 ≤ (9919614861623/25000000000000 : ℝ)^6193 := by
    have hnat : (156016089 : ℕ)^8241*25000000000000^6193 ≤ 9919614861623^6193*312500000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156016089 312500000 9919614861623 25000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (114332893/200000000 : ℝ)^8241 ≤ (2969674108673/6250000000000 : ℝ)^6193 := by
    have hnat : (114332893 : ℕ)^8241*6250000000000^6193 ≤ 2969674108673^6193*200000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114332893 200000000 2969674108673 6250000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2134285707/10000000000 : ℝ), (156016089/312500000 : ℝ), (114332893/200000000 : ℝ)] ![(6403377403289/50000000000000 : ℝ), (9919614861623/25000000000000 : ℝ), (2969674108673/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2134285707/10000000000 : ℝ)|^8241 ≤ (6403377403289/50000000000000 : ℝ)^6193
        have hw : |(-2134285707/10000000000 : ℝ)|=(2134285707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(156016089/312500000 : ℝ)|^8241 ≤ (9919614861623/25000000000000 : ℝ)^6193
        have hw : |(156016089/312500000 : ℝ)|=(156016089/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(114332893/200000000 : ℝ)|^8241 ≤ (2969674108673/6250000000000 : ℝ)^6193
        have hw : |(114332893/200000000 : ℝ)|=(114332893/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s1_5 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1308529209/2500000000 : ℝ)*x 0 + (-1802929223/10000000000 : ℝ)*x 1 + (5716645931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1308529209/2500000000 : ℝ)^8241 ≤ (42253828848529/100000000000000 : ℝ)^6193 := by
    have hnat : (1308529209 : ℕ)^8241*100000000000000^6193 ≤ 42253828848529^6193*2500000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308529209 2500000000 42253828848529 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1802929223/10000000000 : ℝ)^8241 ≤ (5115685612207/50000000000000 : ℝ)^6193 := by
    have hnat : (1802929223 : ℕ)^8241*50000000000000^6193 ≤ 5115685612207^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1802929223 10000000000 5115685612207 50000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5716645931/10000000000 : ℝ)^8241 ≤ (11878699976749/25000000000000 : ℝ)^6193 := by
    have hnat : (5716645931 : ℕ)^8241*25000000000000^6193 ≤ 11878699976749^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5716645931 10000000000 11878699976749 25000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1308529209/2500000000 : ℝ), (-1802929223/10000000000 : ℝ), (5716645931/10000000000 : ℝ)] ![(42253828848529/100000000000000 : ℝ), (5115685612207/50000000000000 : ℝ), (11878699976749/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1308529209/2500000000 : ℝ)|^8241 ≤ (42253828848529/100000000000000 : ℝ)^6193
        have hw : |(1308529209/2500000000 : ℝ)|=(1308529209/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1802929223/10000000000 : ℝ)|^8241 ≤ (5115685612207/50000000000000 : ℝ)^6193
        have hw : |(-1802929223/10000000000 : ℝ)|=(1802929223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5716645931/10000000000 : ℝ)|^8241 ≤ (11878699976749/25000000000000 : ℝ)^6193
        have hw : |(5716645931/10000000000 : ℝ)|=(5716645931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s1_6 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1046822983/2000000000 : ℝ)*x 0 + (5716648041/10000000000 : ℝ)*x 1 + (-901464433/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1046822983/2000000000 : ℝ)^8241 ≤ (10563452053093/25000000000000 : ℝ)^6193 := by
    have hnat : (1046822983 : ℕ)^8241*25000000000000^6193 ≤ 10563452053093^6193*2000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046822983 2000000000 10563452053093 25000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5716648041/10000000000 : ℝ)^8241 ≤ (23757411622103/50000000000000 : ℝ)^6193 := by
    have hnat : (5716648041 : ℕ)^8241*50000000000000^6193 ≤ 23757411622103^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5716648041 10000000000 23757411622103 50000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (901464433/5000000000 : ℝ)^8241 ≤ (2557842132131/25000000000000 : ℝ)^6193 := by
    have hnat : (901464433 : ℕ)^8241*25000000000000^6193 ≤ 2557842132131^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901464433 5000000000 2557842132131 25000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1046822983/2000000000 : ℝ), (5716648041/10000000000 : ℝ), (-901464433/5000000000 : ℝ)] ![(10563452053093/25000000000000 : ℝ), (23757411622103/50000000000000 : ℝ), (2557842132131/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1046822983/2000000000 : ℝ)|^8241 ≤ (10563452053093/25000000000000 : ℝ)^6193
        have hw : |(1046822983/2000000000 : ℝ)|=(1046822983/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5716648041/10000000000 : ℝ)|^8241 ≤ (23757411622103/50000000000000 : ℝ)^6193
        have hw : |(5716648041/10000000000 : ℝ)|=(5716648041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-901464433/5000000000 : ℝ)|^8241 ≤ (2557842132131/25000000000000 : ℝ)^6193
        have hw : |(-901464433/5000000000 : ℝ)|=(901464433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s1_7 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4327138287/10000000000 : ℝ)*x 0 + (5094171479/10000000000 : ℝ)*x 1 + (1840024651/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4327138287/10000000000 : ℝ)^8241 ≤ (16400755324217/50000000000000 : ℝ)^6193 := by
    have hnat : (4327138287 : ℕ)^8241*50000000000000^6193 ≤ 16400755324217^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4327138287 10000000000 16400755324217 50000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5094171479/10000000000 : ℝ)^8241 ≤ (815143311139/2000000000000 : ℝ)^6193 := by
    have hnat : (5094171479 : ℕ)^8241*2000000000000^6193 ≤ 815143311139^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5094171479 10000000000 815143311139 2000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1840024651/5000000000 : ℝ)^8241 ≤ (26441323786369/100000000000000 : ℝ)^6193 := by
    have hnat : (1840024651 : ℕ)^8241*100000000000000^6193 ≤ 26441323786369^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1840024651 5000000000 26441323786369 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4327138287/10000000000 : ℝ), (5094171479/10000000000 : ℝ), (1840024651/5000000000 : ℝ)] ![(16400755324217/50000000000000 : ℝ), (815143311139/2000000000000 : ℝ), (26441323786369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4327138287/10000000000 : ℝ)|^8241 ≤ (16400755324217/50000000000000 : ℝ)^6193
        have hw : |(4327138287/10000000000 : ℝ)|=(4327138287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5094171479/10000000000 : ℝ)|^8241 ≤ (815143311139/2000000000000 : ℝ)^6193
        have hw : |(5094171479/10000000000 : ℝ)|=(5094171479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1840024651/5000000000 : ℝ)|^8241 ≤ (26441323786369/100000000000000 : ℝ)^6193
        have hw : |(1840024651/5000000000 : ℝ)|=(1840024651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1048_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147643001/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1409/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (2553/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10439/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1409/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1409/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1409/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1409/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1409/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1409/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1/5000 : ℝ) ^ (515/128 : ℝ) ≤ (131047/100000000000000000000 : ℝ) := by
    have hpowers : (1/5000 : ℝ)^515 ≤ (131047/100000000000000000000 : ℝ)^128 := by
      have hnat : (1 : ℕ)^515*100000000000000000000^128 ≤ 131047^128*5000^515 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 5000 131047 100000000000000000000 515 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1/5000 : ℝ)) (X := (131047/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have hpowhi : (1409/5000 : ℝ) ^ (515/128 : ℝ) ≤ (61216986505895747/10000000000000000000 : ℝ) := by
    have hpowers : (1409/5000 : ℝ)^515 ≤ (61216986505895747/10000000000000000000 : ℝ)^128 := by
      have hnat : (1409 : ℕ)^515*10000000000000000000^128 ≤ 61216986505895747^128*5000^515 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1409 5000 61216986505895747 10000000000000000000 515 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1409/5000 : ℝ)) (X := (61216986505895747/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000000000131047/50000000000000000000 : ℝ) ≤ (10000000000000007/10000000000000000 : ℝ) ^ (515/128 : ℝ) := by
    have hpowers : (50000000000000131047/50000000000000000000 : ℝ)^128 ≤ (10000000000000007/10000000000000000 : ℝ)^515 := by
      have hnat : (50000000000000131047 : ℕ)^128*10000000000000000^515 ≤ 10000000000000007^515*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000000000131047 50000000000000000000 10000000000000007 10000000000000000 128 515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000000000007/10000000000000000 : ℝ)) (X := (50000000000000131047/50000000000000000000 : ℝ)) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100612169865059088517/100000000000000000000 : ℝ) ≤ (2003036044813487/2000000000000000 : ℝ) ^ (515/128 : ℝ) := by
    have hpowers : (100612169865059088517/100000000000000000000 : ℝ)^128 ≤ (2003036044813487/2000000000000000 : ℝ)^515 := by
      have hnat : (100612169865059088517 : ℕ)^128*2000000000000000^515 ≤ 2003036044813487^515*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100612169865059088517 100000000000000000000 2003036044813487 2000000000000000 128 515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2003036044813487/2000000000000000 : ℝ)) (X := (100612169865059088517/100000000000000000000 : ℝ)) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (5061216986505895747/5000000000000000000 : ℝ) ≤ (10030360448134863/10000000000000000 : ℝ) ^ (515/128 : ℝ) := by
    have hpowers : (5061216986505895747/5000000000000000000 : ℝ)^128 ≤ (10030360448134863/10000000000000000 : ℝ)^515 := by
      have hnat : (5061216986505895747 : ℕ)^128*10000000000000000^515 ≤ 10030360448134863^515*5000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5061216986505895747 5000000000000000000 10030360448134863 10000000000000000 128 515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10030360448134863/10000000000000000 : ℝ)) (X := (5061216986505895747/5000000000000000000 : ℝ)) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(131047/100000000000000000000 : ℝ) ≤ ((22527951423283/22528000000000 : ℝ)+2*(3795056016857/704000000000000 : ℝ)*(1/5000 : ℝ))^(515/128 : ℝ) := by
    rw [show (22527951423283/22528000000000 : ℝ)+2*(3795056016857/704000000000000 : ℝ)*(1/5000 : ℝ)=(10000000000000007/10000000000000000 : ℝ) by norm_num, show 1+2*(131047/100000000000000000000 : ℝ)=(50000000000000131047/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(61216986505895747/10000000000000000000 : ℝ)+(131047/100000000000000000000 : ℝ) ≤ ((22527951423283/22528000000000 : ℝ)+(3795056016857/704000000000000 : ℝ)*((1409/5000 : ℝ)+(1/5000 : ℝ)))^(515/128 : ℝ) := by
    rw [show (22527951423283/22528000000000 : ℝ)+(3795056016857/704000000000000 : ℝ)*((1409/5000 : ℝ)+(1/5000 : ℝ))=(2003036044813487/2000000000000000 : ℝ) by norm_num, show 1+(61216986505895747/10000000000000000000 : ℝ)+(131047/100000000000000000000 : ℝ)=(100612169865059088517/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(61216986505895747/10000000000000000000 : ℝ) ≤ ((22527951423283/22528000000000 : ℝ)+2*(3795056016857/704000000000000 : ℝ)*(1409/5000 : ℝ))^(515/128 : ℝ) := by
    rw [show (22527951423283/22528000000000 : ℝ)+2*(3795056016857/704000000000000 : ℝ)*(1409/5000 : ℝ)=(10030360448134863/10000000000000000 : ℝ) by norm_num, show 1+2*(61216986505895747/10000000000000000000 : ℝ)=(5061216986505895747/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22527951423283/22528000000000 : ℝ)*(X 1 0+X 2 0)+(3795056016857/704000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (515/128 : ℝ)) (lo := (1/5000 : ℝ)) (hi := (1409/5000 : ℝ)) (c := (22527951423283/22528000000000 : ℝ)) (alpha := (3795056016857/704000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22527951423283/22528000000000 : ℝ)*(X 0 1+X 2 1)+(3795056016857/704000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (515/128 : ℝ)) (lo := (1/5000 : ℝ)) (hi := (1409/5000 : ℝ)) (c := (22527951423283/22528000000000 : ℝ)) (alpha := (3795056016857/704000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22527951423283/22528000000000 : ℝ)*(X 0 2+X 1 2)+(3795056016857/704000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (515/128 : ℝ)) (lo := (1/5000 : ℝ)) (hi := (1409/5000 : ℝ)) (c := (22527951423283/22528000000000 : ℝ)) (alpha := (3795056016857/704000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2133334921/10000000000 : ℝ)*X 0 0+(2863704741/5000000000 : ℝ)*X 0 1+(4981967503/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1356077661/2500000000 : ℝ)*X 1 0+(-2537607753/10000000000 : ℝ)*X 1 1+(4981967827/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5424311069/10000000000 : ℝ)*X 2 0+(4981967309/10000000000 : ℝ)*X 2 1+(-507521571/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4325284791/10000000000 : ℝ)*X 0 0+(914757457/2500000000 : ℝ)*X 0 1+(5114772341/10000000000 : ℝ)*X 0 2+(4325284791/10000000000 : ℝ)*X 1 0+(914757457/2500000000 : ℝ)*X 1 1+(5114772341/10000000000 : ℝ)*X 1 2+(4325284791/10000000000 : ℝ)*X 2 0+(914757457/2500000000 : ℝ)*X 2 1+(5114772341/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2134285707/10000000000 : ℝ)*X 0 0+(156016089/312500000 : ℝ)*X 0 1+(114332893/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1308529209/2500000000 : ℝ)*X 1 0+(-1802929223/10000000000 : ℝ)*X 1 1+(5716645931/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1046822983/2000000000 : ℝ)*X 2 0+(5716648041/10000000000 : ℝ)*X 2 1+(-901464433/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4327138287/10000000000 : ℝ)*X 0 0+(5094171479/10000000000 : ℝ)*X 0 1+(1840024651/5000000000 : ℝ)*X 0 2+(4327138287/10000000000 : ℝ)*X 1 0+(5094171479/10000000000 : ℝ)*X 1 1+(1840024651/5000000000 : ℝ)*X 1 2+(4327138287/10000000000 : ℝ)*X 2 0+(5094171479/10000000000 : ℝ)*X 2 1+(1840024651/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1104711848973486159947943/140800000000000000000000000000 : ℝ) := by norm_num
    linear_combination (61997409/50000000000000 : ℝ)*(base1) + (1750478273/100000000000000 : ℝ)*(base19) + (1855586249/100000000000000 : ℝ)*(base23) + (1510757/800000000000 : ℝ)*(upper3) + (3672261/2000000000000 : ℝ)*(upper5) + (1014223640570799/100000000000000 : ℝ)*(major0) + (1014223640570799/100000000000000 : ℝ)*(major1) + (1014223640570799/100000000000000 : ℝ)*(major2) + (670747374763597/50000000000000 : ℝ)*(sp0) + (335375502902601/25000000000000 : ℝ)*(sp1) + (335375476625607/25000000000000 : ℝ)*(sp2) + (85867346992043/12500000000000 : ℝ)*(sp3) + (91365563/1000000000000 : ℝ)*(sp4) + (544698699/12500000000000 : ℝ)*(sp7) + (343471628760377/50000000000000 : ℝ)*(f.failure) + (1341503762088677/100000000000000 : ℝ)*(f.sum) + (58894528678057/35200000000000000000000000000 : ℝ)*base66 + (3091871633641797/281600000000000000000000000000 : ℝ)*base67 + (542775954102597/281600000000000000000000000000 : ℝ)*base69 + (1412893057360197/281600000000000000000000000000 : ℝ)*base71 + (71347373741143/35200000000000000000000000000 : ℝ)*base73 + (1600211965980997/281600000000000000000000000000 : ℝ)*base75 + (2179567261110597/281600000000000000000000000000 : ℝ)*base77 + (964459568771397/281600000000000000000000000000 : ℝ)*base79 + (187988660050857/35200000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (20171377/5000000000000000000000 : ℝ)*base89 + (20171377/5000000000000000000000 : ℝ)*base91 + (20171377/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14485108731875051486661/2816000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2806494057/100000000000000 : ℝ)*(base19) + (529200963/20000000000000 : ℝ)*(base23) + (84291961/50000000000000 : ℝ)*(upper2) + (402035111/100000000000000 : ℝ)*(upper3) + (67210773/12500000000000 : ℝ)*(upper5) + (522029711408489/50000000000000 : ℝ)*(major0) + (522029711408489/50000000000000 : ℝ)*(major1) + (522029711408489/50000000000000 : ℝ)*(major2) + (2659634407/20000000000000 : ℝ)*(sp1) + (3491401469/25000000000000 : ℝ)*(sp2) + (345241839837013/25000000000000 : ℝ)*(sp4) + (1380951254681961/100000000000000 : ℝ)*(sp5) + (690475373868681/50000000000000 : ℝ)*(sp6) + (70715131482391/10000000000000 : ℝ)*(sp7) + (70715131482391/10000000000000 : ℝ)*(f.failure) + (345241839837013/25000000000000 : ℝ)*(f.sum) + (52797767353473/17600000000000000000000000000 : ℝ)*base65 + (119596624540867/140800000000000000000000000000 : ℝ)*base67 + (759698479126333/140800000000000000000000000000 : ℝ)*base70 + (481357363555133/140800000000000000000000000000 : ℝ)*base72 + (34749322415873/17600000000000000000000000000 : ℝ)*base73 + (1376000753635133/140800000000000000000000000000 : ℝ)*base76 + (34539505334467/140800000000000000000000000000 : ℝ)*base77 + (1156085087203133/140800000000000000000000000000 : ℝ)*base80 + (51711278025727/17600000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (5895391/1000000000000000000000 : ℝ)*base89 + (5895391/1000000000000000000000 : ℝ)*base91 + (5895391/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1048_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147643001/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1409/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2553/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10439/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1048_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1048_s2_0 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-273972463/1250000000 : ℝ)*x 0 + (1382421183/2500000000 : ℝ)*x 1 + (5142631981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (273972463/1250000000 : ℝ)^8241 ≤ (6633933477261/50000000000000 : ℝ)^6193 := by
    have hnat : (273972463 : ℕ)^8241*50000000000000^6193 ≤ 6633933477261^6193*1250000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273972463 1250000000 6633933477261 50000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1382421183/2500000000 : ℝ)^8241 ≤ (2841138754807/6250000000000 : ℝ)^6193 := by
    have hnat : (1382421183 : ℕ)^8241*6250000000000^6193 ≤ 2841138754807^6193*2500000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1382421183 2500000000 2841138754807 6250000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5142631981/10000000000 : ℝ)^8241 ≤ (41273912955123/100000000000000 : ℝ)^6193 := by
    have hnat : (5142631981 : ℕ)^8241*100000000000000^6193 ≤ 41273912955123^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5142631981 10000000000 41273912955123 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-273972463/1250000000 : ℝ), (1382421183/2500000000 : ℝ), (5142631981/10000000000 : ℝ)] ![(6633933477261/50000000000000 : ℝ), (2841138754807/6250000000000 : ℝ), (41273912955123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-273972463/1250000000 : ℝ)|^8241 ≤ (6633933477261/50000000000000 : ℝ)^6193
        have hw : |(-273972463/1250000000 : ℝ)|=(273972463/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1382421183/2500000000 : ℝ)|^8241 ≤ (2841138754807/6250000000000 : ℝ)^6193
        have hw : |(1382421183/2500000000 : ℝ)|=(1382421183/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5142631981/10000000000 : ℝ)|^8241 ≤ (41273912955123/100000000000000 : ℝ)^6193
        have hw : |(5142631981/10000000000 : ℝ)|=(5142631981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s2_1 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (537801613/1000000000 : ℝ)*x 0 + (-1196894299/5000000000 : ℝ)*x 1 + (5142634591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537801613/1000000000 : ℝ)^8241 ≤ (43806637687841/100000000000000 : ℝ)^6193 := by
    have hnat : (537801613 : ℕ)^8241*100000000000000^6193 ≤ 43806637687841^6193*1000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537801613 1000000000 43806637687841 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1196894299/5000000000 : ℝ)^8241 ≤ (1491942146399/10000000000000 : ℝ)^6193 := by
    have hnat : (1196894299 : ℕ)^8241*10000000000000^6193 ≤ 1491942146399^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1196894299 5000000000 1491942146399 10000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5142634591/10000000000 : ℝ)^8241 ≤ (41273940829783/100000000000000 : ℝ)^6193 := by
    have hnat : (5142634591 : ℕ)^8241*100000000000000^6193 ≤ 41273940829783^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5142634591 10000000000 41273940829783 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537801613/1000000000 : ℝ), (-1196894299/5000000000 : ℝ), (5142634591/10000000000 : ℝ)] ![(43806637687841/100000000000000 : ℝ), (1491942146399/10000000000000 : ℝ), (41273940829783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537801613/1000000000 : ℝ)|^8241 ≤ (43806637687841/100000000000000 : ℝ)^6193
        have hw : |(537801613/1000000000 : ℝ)|=(537801613/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1196894299/5000000000 : ℝ)|^8241 ≤ (1491942146399/10000000000000 : ℝ)^6193
        have hw : |(-1196894299/5000000000 : ℝ)|=(1196894299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5142634591/10000000000 : ℝ)|^8241 ≤ (41273940829783/100000000000000 : ℝ)^6193
        have hw : |(5142634591/10000000000 : ℝ)|=(5142634591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s2_2 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (215120713/400000000 : ℝ)*x 0 + (321414487/625000000 : ℝ)*x 1 + (-2393789987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215120713/400000000 : ℝ)^8241 ≤ (21903328030131/50000000000000 : ℝ)^6193 := by
    have hnat : (215120713 : ℕ)^8241*50000000000000^6193 ≤ 21903328030131^6193*400000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215120713 400000000 21903328030131 50000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (321414487/625000000 : ℝ)^8241 ≤ (20636955468307/50000000000000 : ℝ)^6193 := by
    have hnat : (321414487 : ℕ)^8241*50000000000000^6193 ≤ 20636955468307^6193*625000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321414487 625000000 20636955468307 50000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2393789987/10000000000 : ℝ)^8241 ≤ (14919432983853/100000000000000 : ℝ)^6193 := by
    have hnat : (2393789987 : ℕ)^8241*100000000000000^6193 ≤ 14919432983853^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2393789987 10000000000 14919432983853 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215120713/400000000 : ℝ), (321414487/625000000 : ℝ), (-2393789987/10000000000 : ℝ)] ![(21903328030131/50000000000000 : ℝ), (20636955468307/50000000000000 : ℝ), (14919432983853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215120713/400000000 : ℝ)|^8241 ≤ (21903328030131/50000000000000 : ℝ)^6193
        have hw : |(215120713/400000000 : ℝ)|=(215120713/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(321414487/625000000 : ℝ)|^8241 ≤ (20636955468307/50000000000000 : ℝ)^6193
        have hw : |(321414487/625000000 : ℝ)|=(321414487/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2393789987/10000000000 : ℝ)|^8241 ≤ (14919432983853/100000000000000 : ℝ)^6193
        have hw : |(-2393789987/10000000000 : ℝ)|=(2393789987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s2_3 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4365108227/10000000000 : ℝ)*x 0 + (4003747651/10000000000 : ℝ)*x 1 + (4759612213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4365108227/10000000000 : ℝ)^8241 ≤ (33185076778053/100000000000000 : ℝ)^6193 := by
    have hnat : (4365108227 : ℕ)^8241*100000000000000^6193 ≤ 33185076778053^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4365108227 10000000000 33185076778053 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4003747651/10000000000 : ℝ)^8241 ≤ (29580400155343/100000000000000 : ℝ)^6193 := by
    have hnat : (4003747651 : ℕ)^8241*100000000000000^6193 ≤ 29580400155343^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4003747651 10000000000 29580400155343 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4759612213/10000000000 : ℝ)^8241 ≤ (93086307651/250000000000 : ℝ)^6193 := by
    have hnat : (4759612213 : ℕ)^8241*250000000000^6193 ≤ 93086307651^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4759612213 10000000000 93086307651 250000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4365108227/10000000000 : ℝ), (4003747651/10000000000 : ℝ), (4759612213/10000000000 : ℝ)] ![(33185076778053/100000000000000 : ℝ), (29580400155343/100000000000000 : ℝ), (93086307651/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4365108227/10000000000 : ℝ)|^8241 ≤ (33185076778053/100000000000000 : ℝ)^6193
        have hw : |(4365108227/10000000000 : ℝ)|=(4365108227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4003747651/10000000000 : ℝ)|^8241 ≤ (29580400155343/100000000000000 : ℝ)^6193
        have hw : |(4003747651/10000000000 : ℝ)|=(4003747651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4759612213/10000000000 : ℝ)|^8241 ≤ (93086307651/250000000000 : ℝ)^6193
        have hw : |(4759612213/10000000000 : ℝ)|=(4759612213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s2_4 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-273989043/1250000000 : ℝ)*x 0 + (5145483337/10000000000 : ℝ)*x 1 + (5526802811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (273989043/1250000000 : ℝ)^8241 ≤ (13268935423457/100000000000000 : ℝ)^6193 := by
    have hnat : (273989043 : ℕ)^8241*100000000000000^6193 ≤ 13268935423457^6193*1250000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273989043 1250000000 13268935423457 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5145483337/10000000000 : ℝ)^8241 ≤ (5163046009117/12500000000000 : ℝ)^6193 := by
    have hnat : (5145483337 : ℕ)^8241*12500000000000^6193 ≤ 5163046009117^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5145483337 10000000000 5163046009117 12500000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5526802811/10000000000 : ℝ)^8241 ≤ (45426696497091/100000000000000 : ℝ)^6193 := by
    have hnat : (5526802811 : ℕ)^8241*100000000000000^6193 ≤ 45426696497091^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5526802811 10000000000 45426696497091 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-273989043/1250000000 : ℝ), (5145483337/10000000000 : ℝ), (5526802811/10000000000 : ℝ)] ![(13268935423457/100000000000000 : ℝ), (5163046009117/12500000000000 : ℝ), (45426696497091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-273989043/1250000000 : ℝ)|^8241 ≤ (13268935423457/100000000000000 : ℝ)^6193
        have hw : |(-273989043/1250000000 : ℝ)|=(273989043/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5145483337/10000000000 : ℝ)|^8241 ≤ (5163046009117/12500000000000 : ℝ)^6193
        have hw : |(5145483337/10000000000 : ℝ)|=(5145483337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5526802811/10000000000 : ℝ)|^8241 ≤ (45426696497091/100000000000000 : ℝ)^6193
        have hw : |(5526802811/10000000000 : ℝ)|=(5526802811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s2_5 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5280446157/10000000000 : ℝ)*x 0 + (-2009619383/10000000000 : ℝ)*x 1 + (1381700719/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5280446157/10000000000 : ℝ)^8241 ≤ (21376122053517/50000000000000 : ℝ)^6193 := by
    have hnat : (5280446157 : ℕ)^8241*50000000000000^6193 ≤ 21376122053517^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280446157 10000000000 21376122053517 50000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2009619383/10000000000 : ℝ)^8241 ≤ (1182105866439/10000000000000 : ℝ)^6193 := by
    have hnat : (2009619383 : ℕ)^8241*10000000000000^6193 ≤ 1182105866439^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2009619383 10000000000 1182105866439 10000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1381700719/2500000000 : ℝ)^8241 ≤ (1817067888321/4000000000000 : ℝ)^6193 := by
    have hnat : (1381700719 : ℕ)^8241*4000000000000^6193 ≤ 1817067888321^6193*2500000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1381700719 2500000000 1817067888321 4000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5280446157/10000000000 : ℝ), (-2009619383/10000000000 : ℝ), (1381700719/2500000000 : ℝ)] ![(21376122053517/50000000000000 : ℝ), (1182105866439/10000000000000 : ℝ), (1817067888321/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5280446157/10000000000 : ℝ)|^8241 ≤ (21376122053517/50000000000000 : ℝ)^6193
        have hw : |(5280446157/10000000000 : ℝ)|=(5280446157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2009619383/10000000000 : ℝ)|^8241 ≤ (1182105866439/10000000000000 : ℝ)^6193
        have hw : |(-2009619383/10000000000 : ℝ)|=(2009619383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1381700719/2500000000 : ℝ)|^8241 ≤ (1817067888321/4000000000000 : ℝ)^6193
        have hw : |(1381700719/2500000000 : ℝ)|=(1381700719/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s2_6 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1056089277/2000000000 : ℝ)*x 0 + (1381700679/2500000000 : ℝ)*x 1 + (-1004809647/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056089277/2000000000 : ℝ)^8241 ≤ (42752246563451/100000000000000 : ℝ)^6193 := by
    have hnat : (1056089277 : ℕ)^8241*100000000000000^6193 ≤ 42752246563451^6193*2000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056089277 2000000000 42752246563451 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1381700679/2500000000 : ℝ)^8241 ≤ (45426695458033/100000000000000 : ℝ)^6193 := by
    have hnat : (1381700679 : ℕ)^8241*100000000000000^6193 ≤ 45426695458033^6193*2500000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1381700679 2500000000 45426695458033 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1004809647/5000000000 : ℝ)^8241 ≤ (2364211593549/20000000000000 : ℝ)^6193 := by
    have hnat : (1004809647 : ℕ)^8241*20000000000000^6193 ≤ 2364211593549^6193*5000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004809647 5000000000 2364211593549 20000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1056089277/2000000000 : ℝ), (1381700679/2500000000 : ℝ), (-1004809647/5000000000 : ℝ)] ![(42752246563451/100000000000000 : ℝ), (45426695458033/100000000000000 : ℝ), (2364211593549/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1056089277/2000000000 : ℝ)|^8241 ≤ (42752246563451/100000000000000 : ℝ)^6193
        have hw : |(1056089277/2000000000 : ℝ)|=(1056089277/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1381700679/2500000000 : ℝ)|^8241 ≤ (45426695458033/100000000000000 : ℝ)^6193
        have hw : |(1381700679/2500000000 : ℝ)|=(1381700679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1004809647/5000000000 : ℝ)|^8241 ≤ (2364211593549/20000000000000 : ℝ)^6193
        have hw : |(-1004809647/5000000000 : ℝ)|=(1004809647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1048_s2_7 (p : ℝ) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (873073877/2000000000 : ℝ)*x 0 + (475404017/1000000000 : ℝ)*x 1 + (4009376459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873073877/2000000000 : ℝ)^8241 ≤ (33187718786947/100000000000000 : ℝ)^6193 := by
    have hnat : (873073877 : ℕ)^8241*100000000000000^6193 ≤ 33187718786947^6193*2000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873073877 2000000000 33187718786947 100000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (475404017/1000000000 : ℝ)^8241 ≤ (1487061160509/4000000000000 : ℝ)^6193 := by
    have hnat : (475404017 : ℕ)^8241*4000000000000^6193 ≤ 1487061160509^6193*1000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      475404017 1000000000 1487061160509 4000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4009376459/10000000000 : ℝ)^8241 ≤ (2963575218239/10000000000000 : ℝ)^6193 := by
    have hnat : (4009376459 : ℕ)^8241*10000000000000^6193 ≤ 2963575218239^6193*10000000000^8241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4009376459 10000000000 2963575218239 10000000000000 8241 6193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8241/2048 : ℝ)) 8241 6193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873073877/2000000000 : ℝ), (475404017/1000000000 : ℝ), (4009376459/10000000000 : ℝ)] ![(33187718786947/100000000000000 : ℝ), (1487061160509/4000000000000 : ℝ), (2963575218239/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873073877/2000000000 : ℝ)|^8241 ≤ (33187718786947/100000000000000 : ℝ)^6193
        have hw : |(873073877/2000000000 : ℝ)|=(873073877/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(475404017/1000000000 : ℝ)|^8241 ≤ (1487061160509/4000000000000 : ℝ)^6193
        have hw : |(475404017/1000000000 : ℝ)|=(475404017/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4009376459/10000000000 : ℝ)|^8241 ≤ (2963575218239/10000000000000 : ℝ)^6193
        have hw : |(4009376459/10000000000 : ℝ)|=(4009376459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1048_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147643001/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10439/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2553/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (4311/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16801/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10439/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2553/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10439/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2553/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10439/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2553/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10439/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2553/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10439/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2553/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10439/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2553/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2553/50000 : ℝ) ^ (515/128 : ℝ) ≤ (79241720953421/12500000000000000000 : ℝ) := by
    have hpowers : (2553/50000 : ℝ)^515 ≤ (79241720953421/12500000000000000000 : ℝ)^128 := by
      have hnat : (2553 : ℕ)^515*12500000000000000000^128 ≤ 79241720953421^128*50000^515 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2553 50000 79241720953421 12500000000000000000 515 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2553/50000 : ℝ)) (X := (79241720953421/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have hpowhi : (10439/50000 : ℝ) ^ (515/128 : ℝ) ≤ (91575813589818127/50000000000000000000 : ℝ) := by
    have hpowers : (10439/50000 : ℝ)^515 ≤ (91575813589818127/50000000000000000000 : ℝ)^128 := by
      have hnat : (10439 : ℕ)^515*50000000000000000000^128 ≤ 91575813589818127^128*50000^515 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10439 50000 91575813589818127 50000000000000000000 515 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10439/50000 : ℝ)) (X := (91575813589818127/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250079241720953421/6250000000000000000 : ℝ) ≤ (2000006302379473/2000000000000000 : ℝ) ^ (515/128 : ℝ) := by
    have hpowers : (6250079241720953421/6250000000000000000 : ℝ)^128 ≤ (2000006302379473/2000000000000000 : ℝ)^515 := by
      have hnat : (6250079241720953421 : ℕ)^128*2000000000000000^515 ≤ 2000006302379473^515*6250000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250079241720953421 6250000000000000000 2000006302379473 2000000000000000 128 515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000006302379473/2000000000000000 : ℝ)) (X := (6250079241720953421/6250000000000000000 : ℝ)) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (50091892780473631811/50000000000000000000 : ℝ) ≤ (10004564723243501/10000000000000000 : ℝ) ^ (515/128 : ℝ) := by
    have hpowers : (50091892780473631811/50000000000000000000 : ℝ)^128 ≤ (10004564723243501/10000000000000000 : ℝ)^515 := by
      have hnat : (50091892780473631811 : ℕ)^128*10000000000000000^515 ≤ 10004564723243501^515*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50091892780473631811 50000000000000000000 10004564723243501 10000000000000000 128 515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004564723243501/10000000000000000 : ℝ)) (X := (50091892780473631811/50000000000000000000 : ℝ)) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (25091575813589818127/25000000000000000000 : ℝ) ≤ (10009097934589637/10000000000000000 : ℝ) ^ (515/128 : ℝ) := by
    have hpowers : (25091575813589818127/25000000000000000000 : ℝ)^128 ≤ (10009097934589637/10000000000000000 : ℝ)^515 := by
      have hnat : (25091575813589818127 : ℕ)^128*10000000000000000^515 ≤ 10009097934589637^515*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25091575813589818127 25000000000000000000 10009097934589637 10000000000000000 128 515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10009097934589637/10000000000000000 : ℝ)) (X := (25091575813589818127/25000000000000000000 : ℝ)) (by norm_num) 515 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(79241720953421/12500000000000000000 : ℝ) ≤ ((39418550962844624987/39430000000000000000 : ℝ)+2*(566651418267/197150000000000 : ℝ)*(2553/50000 : ℝ))^(515/128 : ℝ) := by
    rw [show (39418550962844624987/39430000000000000000 : ℝ)+2*(566651418267/197150000000000 : ℝ)*(2553/50000 : ℝ)=(2000006302379473/2000000000000000 : ℝ) by norm_num, show 1+2*(79241720953421/12500000000000000000 : ℝ)=(6250079241720953421/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(91575813589818127/50000000000000000000 : ℝ)+(79241720953421/12500000000000000000 : ℝ) ≤ ((39418550962844624987/39430000000000000000 : ℝ)+(566651418267/197150000000000 : ℝ)*((10439/50000 : ℝ)+(2553/50000 : ℝ)))^(515/128 : ℝ) := by
    rw [show (39418550962844624987/39430000000000000000 : ℝ)+(566651418267/197150000000000 : ℝ)*((10439/50000 : ℝ)+(2553/50000 : ℝ))=(10004564723243501/10000000000000000 : ℝ) by norm_num, show 1+(91575813589818127/50000000000000000000 : ℝ)+(79241720953421/12500000000000000000 : ℝ)=(50091892780473631811/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(91575813589818127/50000000000000000000 : ℝ) ≤ ((39418550962844624987/39430000000000000000 : ℝ)+2*(566651418267/197150000000000 : ℝ)*(10439/50000 : ℝ))^(515/128 : ℝ) := by
    rw [show (39418550962844624987/39430000000000000000 : ℝ)+2*(566651418267/197150000000000 : ℝ)*(10439/50000 : ℝ)=(10009097934589637/10000000000000000 : ℝ) by norm_num, show 1+2*(91575813589818127/50000000000000000000 : ℝ)=(25091575813589818127/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (39418550962844624987/39430000000000000000 : ℝ)*(X 1 0+X 2 0)+(566651418267/197150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (515/128 : ℝ)) (lo := (2553/50000 : ℝ)) (hi := (10439/50000 : ℝ)) (c := (39418550962844624987/39430000000000000000 : ℝ)) (alpha := (566651418267/197150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (39418550962844624987/39430000000000000000 : ℝ)*(X 0 1+X 2 1)+(566651418267/197150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (515/128 : ℝ)) (lo := (2553/50000 : ℝ)) (hi := (10439/50000 : ℝ)) (c := (39418550962844624987/39430000000000000000 : ℝ)) (alpha := (566651418267/197150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (39418550962844624987/39430000000000000000 : ℝ)*(X 0 2+X 1 2)+(566651418267/197150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (515/128 : ℝ)) (lo := (2553/50000 : ℝ)) (hi := (10439/50000 : ℝ)) (c := (39418550962844624987/39430000000000000000 : ℝ)) (alpha := (566651418267/197150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-273972463/1250000000 : ℝ)*X 0 0+(1382421183/2500000000 : ℝ)*X 0 1+(5142631981/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((537801613/1000000000 : ℝ)*X 1 0+(-1196894299/5000000000 : ℝ)*X 1 1+(5142634591/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((215120713/400000000 : ℝ)*X 2 0+(321414487/625000000 : ℝ)*X 2 1+(-2393789987/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4365108227/10000000000 : ℝ)*X 0 0+(4003747651/10000000000 : ℝ)*X 0 1+(4759612213/10000000000 : ℝ)*X 0 2+(4365108227/10000000000 : ℝ)*X 1 0+(4003747651/10000000000 : ℝ)*X 1 1+(4759612213/10000000000 : ℝ)*X 1 2+(4365108227/10000000000 : ℝ)*X 2 0+(4003747651/10000000000 : ℝ)*X 2 1+(4759612213/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-273989043/1250000000 : ℝ)*X 0 0+(5145483337/10000000000 : ℝ)*X 0 1+(5526802811/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5280446157/10000000000 : ℝ)*X 1 0+(-2009619383/10000000000 : ℝ)*X 1 1+(1381700719/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1056089277/2000000000 : ℝ)*X 2 0+(1381700679/2500000000 : ℝ)*X 2 1+(-1004809647/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((873073877/2000000000 : ℝ)*X 0 0+(475404017/1000000000 : ℝ)*X 0 1+(4009376459/10000000000 : ℝ)*X 0 2+(873073877/2000000000 : ℝ)*X 1 0+(475404017/1000000000 : ℝ)*X 1 1+(4009376459/10000000000 : ℝ)*X 1 2+(873073877/2000000000 : ℝ)*X 2 0+(475404017/1000000000 : ℝ)*X 2 1+(4009376459/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1048_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2128184768269878916312601799/197150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (171205507/50000000000000 : ℝ)*(base19) + (757974259/50000000000000 : ℝ)*(base23) + (110322233/50000000000000 : ℝ)*(upper2) + (77136059/100000000000000 : ℝ)*(upper3) + (195334260601053/10000000000000 : ℝ)*(major0) + (195334260601053/10000000000000 : ℝ)*(major1) + (195334260601053/10000000000000 : ℝ)*(major2) + (8073898652807/312500000000 : ℝ)*(sp0) + (645916775262223/25000000000000 : ℝ)*(sp1) + (645915778662873/25000000000000 : ℝ)*(sp2) + (1323002049718417/100000000000000 : ℝ)*(sp3) + (19874561667/100000000000000 : ℝ)*(sp4) + (2812859897/100000000000000 : ℝ)*(sp6) + (7679508881/50000000000000 : ℝ)*(sp7) + (1323017408736179/100000000000000 : ℝ)*(f.failure) + (1291833721729953/50000000000000 : ℝ)*(f.sum) + (13889414850001/3943000000000000000000000000 : ℝ)*base65 + (4756336280311288689/394300000000000000000000000000000 : ℝ)*base68 + (2638215229918288689/394300000000000000000000000000000 : ℝ)*base70 + (2821095525930188689/394300000000000000000000000000000 : ℝ)*base72 + (4367700211709/3943000000000000000000000000 : ℝ)*base74 + (1003590874286788689/394300000000000000000000000000000 : ℝ)*base76 + (1310666006005688689/394300000000000000000000000000000 : ℝ)*base78 + (4247452486206388689/394300000000000000000000000000000 : ℝ)*base80 + (10777072323253/3943000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (84833179/10000000000000000000000 : ℝ)*base89 + (84833179/10000000000000000000000 : ℝ)*base91 + (84833179/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (144467166119654832875960769/30804687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (436702439/50000000000000 : ℝ)*(base19) + (260823779/25000000000000 : ℝ)*(base23) + (31776699/25000000000000 : ℝ)*(upper3) + (8119587/50000000000000 : ℝ)*(lower4) + (52799841/50000000000000 : ℝ)*(upper5) + (61958772434571/3125000000000 : ℝ)*(major0) + (61958772434571/3125000000000 : ℝ)*(major1) + (61958772434571/3125000000000 : ℝ)*(major2) + (91311057/1250000000000 : ℝ)*(sp1) + (2176657229/25000000000000 : ℝ)*(sp2) + (655618222569811/25000000000000 : ℝ)*(sp4) + (1311232355994903/50000000000000 : ℝ)*(sp5) + (655615785088803/25000000000000 : ℝ)*(sp6) + (167861048650917/12500000000000 : ℝ)*(sp7) + (167861048650917/12500000000000 : ℝ)*(f.failure) + (655618222569811/25000000000000 : ℝ)*(f.sum) + (351273585261/2464375000000000000000000000 : ℝ)*base65 + (832885939675500577/123218750000000000000000000000000 : ℝ)*base67 + (240917874564499423/123218750000000000000000000000000 : ℝ)*base70 + (465349994306063077/123218750000000000000000000000000 : ℝ)*base71 + (28304140602859/9857500000000000000000000000 : ℝ)*base73 + (660163330858125577/123218750000000000000000000000000 : ℝ)*base75 + (669165145641875577/123218750000000000000000000000000 : ℝ)*base77 + (811261537489625577/123218750000000000000000000000000 : ℝ)*base79 + (11487032194903/4928750000000000000000000000 : ℝ)*base82 + (12718083/1250000000000000000000 : ℝ)*base90 + (12718083/1250000000000000000000 : ℝ)*base92 + (12718083/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1048_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147643001/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10439/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2553/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4311/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16801/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1048_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1048_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147643001/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4311/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16801/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1048_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1048_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1048_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (515/128 : ℝ) ≤ p) (hpb : p ≤ (8241/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147643001/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4311/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16801/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1048_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

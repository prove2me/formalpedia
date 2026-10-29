-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1573_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:28:29.316657+00:00
-- url     : https://prove2.me/submissions/8aa4bae2-af9f-4172-b341-8a6a676cdc79

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
theorem support_rectangle_w1573_s3_0 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-890641773/5000000000 : ℝ)*x 0 + (2713513009/5000000000 : ℝ)*x 1 + (5218706509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (890641773/5000000000 : ℝ)^4643 ≤ (2733173274301/25000000000000 : ℝ)^3619 := by
    have hnat : (890641773 : ℕ)^4643*25000000000000^3619 ≤ 2733173274301^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      890641773 5000000000 2733173274301 25000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713513009/5000000000 : ℝ)^4643 ≤ (45651589621631/100000000000000 : ℝ)^3619 := by
    have hnat : (2713513009 : ℕ)^4643*100000000000000^3619 ≤ 45651589621631^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713513009 5000000000 45651589621631 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218706509/10000000000 : ℝ)^4643 ≤ (43415717269603/100000000000000 : ℝ)^3619 := by
    have hnat : (5218706509 : ℕ)^4643*100000000000000^3619 ≤ 43415717269603^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218706509 10000000000 43415717269603 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-890641773/5000000000 : ℝ), (2713513009/5000000000 : ℝ), (5218706509/10000000000 : ℝ)] ![(2733173274301/25000000000000 : ℝ), (45651589621631/100000000000000 : ℝ), (43415717269603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-890641773/5000000000 : ℝ)|^4643 ≤ (2733173274301/25000000000000 : ℝ)^3619
        have hw : |(-890641773/5000000000 : ℝ)|=(890641773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713513009/5000000000 : ℝ)|^4643 ≤ (45651589621631/100000000000000 : ℝ)^3619
        have hw : |(2713513009/5000000000 : ℝ)|=(2713513009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218706509/10000000000 : ℝ)|^4643 ≤ (43415717269603/100000000000000 : ℝ)^3619
        have hw : |(5218706509/10000000000 : ℝ)|=(5218706509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s3_1 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (106968689/200000000 : ℝ)*x 0 + (-1887887009/10000000000 : ℝ)*x 1 + (5218706509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106968689/200000000 : ℝ)^4643 ≤ (22402584473557/50000000000000 : ℝ)^3619 := by
    have hnat : (106968689 : ℕ)^4643*50000000000000^3619 ≤ 22402584473557^3619*200000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106968689 200000000 22402584473557 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1887887009/10000000000 : ℝ)^4643 ≤ (5889556883547/50000000000000 : ℝ)^3619 := by
    have hnat : (1887887009 : ℕ)^4643*50000000000000^3619 ≤ 5889556883547^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1887887009 10000000000 5889556883547 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218706509/10000000000 : ℝ)^4643 ≤ (43415717269603/100000000000000 : ℝ)^3619 := by
    have hnat : (5218706509 : ℕ)^4643*100000000000000^3619 ≤ 43415717269603^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218706509 10000000000 43415717269603 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106968689/200000000 : ℝ), (-1887887009/10000000000 : ℝ), (5218706509/10000000000 : ℝ)] ![(22402584473557/50000000000000 : ℝ), (5889556883547/50000000000000 : ℝ), (43415717269603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106968689/200000000 : ℝ)|^4643 ≤ (22402584473557/50000000000000 : ℝ)^3619
        have hw : |(106968689/200000000 : ℝ)|=(106968689/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1887887009/10000000000 : ℝ)|^4643 ≤ (5889556883547/50000000000000 : ℝ)^3619
        have hw : |(-1887887009/10000000000 : ℝ)|=(1887887009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218706509/10000000000 : ℝ)|^4643 ≤ (43415717269603/100000000000000 : ℝ)^3619
        have hw : |(5218706509/10000000000 : ℝ)|=(5218706509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s3_2 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348434467/10000000000 : ℝ)*x 0 + (5218706497/10000000000 : ℝ)*x 1 + (-1887887001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348434467/10000000000 : ℝ)^4643 ≤ (44805169129823/100000000000000 : ℝ)^3619 := by
    have hnat : (5348434467 : ℕ)^4643*100000000000000^3619 ≤ 44805169129823^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348434467 10000000000 44805169129823 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218706497/10000000000 : ℝ)^4643 ≤ (1736628685661/4000000000000 : ℝ)^3619 := by
    have hnat : (5218706497 : ℕ)^4643*4000000000000^3619 ≤ 1736628685661^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218706497 10000000000 1736628685661 4000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1887887001/10000000000 : ℝ)^4643 ≤ (11779113703057/100000000000000 : ℝ)^3619 := by
    have hnat : (1887887001 : ℕ)^4643*100000000000000^3619 ≤ 11779113703057^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1887887001 10000000000 11779113703057 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348434467/10000000000 : ℝ), (5218706497/10000000000 : ℝ), (-1887887001/10000000000 : ℝ)] ![(44805169129823/100000000000000 : ℝ), (1736628685661/4000000000000 : ℝ), (11779113703057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348434467/10000000000 : ℝ)|^4643 ≤ (44805169129823/100000000000000 : ℝ)^3619
        have hw : |(5348434467/10000000000 : ℝ)|=(5348434467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218706497/10000000000 : ℝ)|^4643 ≤ (1736628685661/4000000000000 : ℝ)^3619
        have hw : |(5218706497/10000000000 : ℝ)|=(5218706497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1887887001/10000000000 : ℝ)|^4643 ≤ (11779113703057/100000000000000 : ℝ)^3619
        have hw : |(-1887887001/10000000000 : ℝ)|=(1887887001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s3_3 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (424203421/1000000000 : ℝ)*x 0 + (1000359109/2500000000 : ℝ)*x 1 + (140443521/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (424203421/1000000000 : ℝ)^4643 ≤ (16640480971487/50000000000000 : ℝ)^3619 := by
    have hnat : (424203421 : ℕ)^4643*50000000000000^3619 ≤ 16640480971487^3619*1000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424203421 1000000000 16640480971487 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1000359109/2500000000 : ℝ)^4643 ≤ (7719736774539/25000000000000 : ℝ)^3619 := by
    have hnat : (1000359109 : ℕ)^4643*25000000000000^3619 ≤ 7719736774539^3619*2500000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000359109 2500000000 7719736774539 25000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (140443521/312500000 : ℝ)^4643 ≤ (7168018189547/20000000000000 : ℝ)^3619 := by
    have hnat : (140443521 : ℕ)^4643*20000000000000^3619 ≤ 7168018189547^3619*312500000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140443521 312500000 7168018189547 20000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(424203421/1000000000 : ℝ), (1000359109/2500000000 : ℝ), (140443521/312500000 : ℝ)] ![(16640480971487/50000000000000 : ℝ), (7719736774539/25000000000000 : ℝ), (7168018189547/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(424203421/1000000000 : ℝ)|^4643 ≤ (16640480971487/50000000000000 : ℝ)^3619
        have hw : |(424203421/1000000000 : ℝ)|=(424203421/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1000359109/2500000000 : ℝ)|^4643 ≤ (7719736774539/25000000000000 : ℝ)^3619
        have hw : |(1000359109/2500000000 : ℝ)|=(1000359109/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(140443521/312500000 : ℝ)|^4643 ≤ (7168018189547/20000000000000 : ℝ)^3619
        have hw : |(140443521/312500000 : ℝ)|=(140443521/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s3_4 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-445327813/2500000000 : ℝ)*x 0 + (65247607/125000000 : ℝ)*x 1 + (217036633/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (445327813/2500000000 : ℝ)^4643 ≤ (10932911259143/100000000000000 : ℝ)^3619 := by
    have hnat : (445327813 : ℕ)^4643*100000000000000^3619 ≤ 10932911259143^3619*2500000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      445327813 2500000000 10932911259143 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65247607/125000000 : ℝ)^4643 ≤ (43427480019809/100000000000000 : ℝ)^3619 := by
    have hnat : (65247607 : ℕ)^4643*100000000000000^3619 ≤ 43427480019809^3619*125000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65247607 125000000 43427480019809 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217036633/400000000 : ℝ)^4643 ≤ (22819804352911/50000000000000 : ℝ)^3619 := by
    have hnat : (217036633 : ℕ)^4643*50000000000000^3619 ≤ 22819804352911^3619*400000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217036633 400000000 22819804352911 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-445327813/2500000000 : ℝ), (65247607/125000000 : ℝ), (217036633/400000000 : ℝ)] ![(10932911259143/100000000000000 : ℝ), (43427480019809/100000000000000 : ℝ), (22819804352911/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-445327813/2500000000 : ℝ)|^4643 ≤ (10932911259143/100000000000000 : ℝ)^3619
        have hw : |(-445327813/2500000000 : ℝ)|=(445327813/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(65247607/125000000 : ℝ)|^4643 ≤ (43427480019809/100000000000000 : ℝ)^3619
        have hw : |(65247607/125000000 : ℝ)|=(65247607/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(217036633/400000000 : ℝ)|^4643 ≤ (22819804352911/50000000000000 : ℝ)^3619
        have hw : |(217036633/400000000 : ℝ)|=(217036633/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s3_5 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293299387/10000000000 : ℝ)*x 0 + (-67227111/400000000 : ℝ)*x 1 + (542591591/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293299387/10000000000 : ℝ)^4643 ≤ (22106732816603/50000000000000 : ℝ)^3619 := by
    have hnat : (5293299387 : ℕ)^4643*50000000000000^3619 ≤ 22106732816603^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293299387 10000000000 22106732816603 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67227111/400000000 : ℝ)^4643 ≤ (2029384946287/20000000000000 : ℝ)^3619 := by
    have hnat : (67227111 : ℕ)^4643*20000000000000^3619 ≤ 2029384946287^3619*400000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67227111 400000000 2029384946287 20000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542591591/1000000000 : ℝ)^4643 ≤ (22819804811547/50000000000000 : ℝ)^3619 := by
    have hnat : (542591591 : ℕ)^4643*50000000000000^3619 ≤ 22819804811547^3619*1000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542591591 1000000000 22819804811547 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293299387/10000000000 : ℝ), (-67227111/400000000 : ℝ), (542591591/1000000000 : ℝ)] ![(22106732816603/50000000000000 : ℝ), (2029384946287/20000000000000 : ℝ), (22819804811547/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293299387/10000000000 : ℝ)|^4643 ≤ (22106732816603/50000000000000 : ℝ)^3619
        have hw : |(5293299387/10000000000 : ℝ)|=(5293299387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-67227111/400000000 : ℝ)|^4643 ≤ (2029384946287/20000000000000 : ℝ)^3619
        have hw : |(-67227111/400000000 : ℝ)|=(67227111/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(542591591/1000000000 : ℝ)|^4643 ≤ (22819804811547/50000000000000 : ℝ)^3619
        have hw : |(542591591/1000000000 : ℝ)|=(542591591/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s3_6 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058659963/2000000000 : ℝ)*x 0 + (2712957781/5000000000 : ℝ)*x 1 + (-420169417/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058659963/2000000000 : ℝ)^4643 ≤ (690835472183/1562500000000 : ℝ)^3619 := by
    have hnat : (1058659963 : ℕ)^4643*1562500000000^3619 ≤ 690835472183^3619*2000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058659963 2000000000 690835472183 1562500000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2712957781/5000000000 : ℝ)^4643 ≤ (11409901466919/25000000000000 : ℝ)^3619 := by
    have hnat : (2712957781 : ℕ)^4643*25000000000000^3619 ≤ 11409901466919^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712957781 5000000000 11409901466919 25000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (420169417/2500000000 : ℝ)^4643 ≤ (5073461951323/50000000000000 : ℝ)^3619 := by
    have hnat : (420169417 : ℕ)^4643*50000000000000^3619 ≤ 5073461951323^3619*2500000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420169417 2500000000 5073461951323 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058659963/2000000000 : ℝ), (2712957781/5000000000 : ℝ), (-420169417/2500000000 : ℝ)] ![(690835472183/1562500000000 : ℝ), (11409901466919/25000000000000 : ℝ), (5073461951323/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058659963/2000000000 : ℝ)|^4643 ≤ (690835472183/1562500000000 : ℝ)^3619
        have hw : |(1058659963/2000000000 : ℝ)|=(1058659963/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2712957781/5000000000 : ℝ)|^4643 ≤ (11409901466919/25000000000000 : ℝ)^3619
        have hw : |(2712957781/5000000000 : ℝ)|=(2712957781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-420169417/2500000000 : ℝ)|^4643 ≤ (5073461951323/50000000000000 : ℝ)^3619
        have hw : |(-420169417/2500000000 : ℝ)|=(420169417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s3_7 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530262569/1250000000 : ℝ)*x 0 + (4491586323/10000000000 : ℝ)*x 1 + (200203097/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530262569/1250000000 : ℝ)^4643 ≤ (8320407426099/25000000000000 : ℝ)^3619 := by
    have hnat : (530262569 : ℕ)^4643*25000000000000^3619 ≤ 8320407426099^3619*1250000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530262569 1250000000 8320407426099 25000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4491586323/10000000000 : ℝ)^4643 ≤ (7162685400037/20000000000000 : ℝ)^3619 := by
    have hnat : (4491586323 : ℕ)^4643*20000000000000^3619 ≤ 7162685400037^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491586323 10000000000 7162685400037 20000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (200203097/500000000 : ℝ)^4643 ≤ (6180988657031/20000000000000 : ℝ)^3619 := by
    have hnat : (200203097 : ℕ)^4643*20000000000000^3619 ≤ 6180988657031^3619*500000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200203097 500000000 6180988657031 20000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530262569/1250000000 : ℝ), (4491586323/10000000000 : ℝ), (200203097/500000000 : ℝ)] ![(8320407426099/25000000000000 : ℝ), (7162685400037/20000000000000 : ℝ), (6180988657031/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530262569/1250000000 : ℝ)|^4643 ≤ (8320407426099/25000000000000 : ℝ)^3619
        have hw : |(530262569/1250000000 : ℝ)|=(530262569/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4491586323/10000000000 : ℝ)|^4643 ≤ (7162685400037/20000000000000 : ℝ)^3619
        have hw : |(4491586323/10000000000 : ℝ)|=(4491586323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(200203097/500000000 : ℝ)|^4643 ≤ (6180988657031/20000000000000 : ℝ)^3619
        have hw : |(200203097/500000000 : ℝ)|=(200203097/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1573_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21033669/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3951/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2709/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (111/1000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7759/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3951/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2709/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3951/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2709/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3951/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2709/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3951/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2709/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3951/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2709/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3951/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2709/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2709/25000 : ℝ) ^ (4641/1024 : ℝ) ≤ (4224814344245947/100000000000000000000 : ℝ) := by
    have hpowers : (2709/25000 : ℝ)^4641 ≤ (4224814344245947/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2709 : ℕ)^4641*100000000000000000000^1024 ≤ 4224814344245947^1024*25000^4641 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2709 25000 4224814344245947 100000000000000000000 4641 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2709/25000 : ℝ)) (X := (4224814344245947/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4641 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3951/25000 : ℝ) ^ (4641/1024 : ℝ) ≤ (2921060976545301/12500000000000000000 : ℝ) := by
    have hpowers : (3951/25000 : ℝ)^4641 ≤ (2921060976545301/12500000000000000000 : ℝ)^1024 := by
      have hnat : (3951 : ℕ)^4641*12500000000000000000^1024 ≤ 2921060976545301^1024*25000^4641 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3951 25000 2921060976545301 12500000000000000000 4641 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3951/25000 : ℝ)) (X := (2921060976545301/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4641 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004224814344245947/50000000000000000000 : ℝ) ≤ (5000093214123013/5000000000000000 : ℝ) ^ (4641/1024 : ℝ) := by
    have hpowers : (50004224814344245947/50000000000000000000 : ℝ)^1024 ≤ (5000093214123013/5000000000000000 : ℝ)^4641 := by
      have hnat : (50004224814344245947 : ℕ)^1024*5000000000000000^4641 ≤ 5000093214123013^4641*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004224814344245947 50000000000000000000 5000093214123013 5000000000000000 1024 4641 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000093214123013/5000000000000000 : ℝ)) (X := (50004224814344245947/50000000000000000000 : ℝ)) (by norm_num) 4641 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20005518660431321671/20000000000000000000 : ℝ) ≤ (10000608758968331/10000000000000000 : ℝ) ^ (4641/1024 : ℝ) := by
    have hpowers : (20005518660431321671/20000000000000000000 : ℝ)^1024 ≤ (10000608758968331/10000000000000000 : ℝ)^4641 := by
      have hnat : (20005518660431321671 : ℕ)^1024*10000000000000000^4641 ≤ 10000608758968331^4641*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20005518660431321671 20000000000000000000 10000608758968331 10000000000000000 1024 4641 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000608758968331/10000000000000000 : ℝ)) (X := (20005518660431321671/20000000000000000000 : ℝ)) (by norm_num) 4641 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6252921060976545301/6250000000000000000 : ℝ) ≤ (2500257772422659/2500000000000000 : ℝ) ^ (4641/1024 : ℝ) := by
    have hpowers : (6252921060976545301/6250000000000000000 : ℝ)^1024 ≤ (2500257772422659/2500000000000000 : ℝ)^4641 := by
      have hnat : (6252921060976545301 : ℕ)^1024*2500000000000000^4641 ≤ 2500257772422659^4641*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252921060976545301 6250000000000000000 2500257772422659 2500000000000000 1024 4641 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500257772422659/2500000000000000 : ℝ)) (X := (6252921060976545301/6250000000000000000 : ℝ)) (by norm_num) 4641 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4224814344245947/100000000000000000000 : ℝ) ≤ ((229961914000520663/230000000000000000 : ℝ)+2*(28155381487/33120000000000 : ℝ)*(2709/25000 : ℝ))^(4641/1024 : ℝ) := by
    rw [show (229961914000520663/230000000000000000 : ℝ)+2*(28155381487/33120000000000 : ℝ)*(2709/25000 : ℝ)=(5000093214123013/5000000000000000 : ℝ) by norm_num, show 1+2*(4224814344245947/100000000000000000000 : ℝ)=(50004224814344245947/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2921060976545301/12500000000000000000 : ℝ)+(4224814344245947/100000000000000000000 : ℝ) ≤ ((229961914000520663/230000000000000000 : ℝ)+(28155381487/33120000000000 : ℝ)*((3951/25000 : ℝ)+(2709/25000 : ℝ)))^(4641/1024 : ℝ) := by
    rw [show (229961914000520663/230000000000000000 : ℝ)+(28155381487/33120000000000 : ℝ)*((3951/25000 : ℝ)+(2709/25000 : ℝ))=(10000608758968331/10000000000000000 : ℝ) by norm_num, show 1+(2921060976545301/12500000000000000000 : ℝ)+(4224814344245947/100000000000000000000 : ℝ)=(20005518660431321671/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2921060976545301/12500000000000000000 : ℝ) ≤ ((229961914000520663/230000000000000000 : ℝ)+2*(28155381487/33120000000000 : ℝ)*(3951/25000 : ℝ))^(4641/1024 : ℝ) := by
    rw [show (229961914000520663/230000000000000000 : ℝ)+2*(28155381487/33120000000000 : ℝ)*(3951/25000 : ℝ)=(2500257772422659/2500000000000000 : ℝ) by norm_num, show 1+2*(2921060976545301/12500000000000000000 : ℝ)=(6252921060976545301/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (229961914000520663/230000000000000000 : ℝ)*(X 1 0+X 2 0)+(28155381487/33120000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4641/1024 : ℝ)) (lo := (2709/25000 : ℝ)) (hi := (3951/25000 : ℝ)) (c := (229961914000520663/230000000000000000 : ℝ)) (alpha := (28155381487/33120000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (229961914000520663/230000000000000000 : ℝ)*(X 0 1+X 2 1)+(28155381487/33120000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4641/1024 : ℝ)) (lo := (2709/25000 : ℝ)) (hi := (3951/25000 : ℝ)) (c := (229961914000520663/230000000000000000 : ℝ)) (alpha := (28155381487/33120000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (229961914000520663/230000000000000000 : ℝ)*(X 0 2+X 1 2)+(28155381487/33120000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4641/1024 : ℝ)) (lo := (2709/25000 : ℝ)) (hi := (3951/25000 : ℝ)) (c := (229961914000520663/230000000000000000 : ℝ)) (alpha := (28155381487/33120000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-890641773/5000000000 : ℝ)*X 0 0+(2713513009/5000000000 : ℝ)*X 0 1+(5218706509/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((106968689/200000000 : ℝ)*X 1 0+(-1887887009/10000000000 : ℝ)*X 1 1+(5218706509/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348434467/10000000000 : ℝ)*X 2 0+(5218706497/10000000000 : ℝ)*X 2 1+(-1887887001/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((424203421/1000000000 : ℝ)*X 0 0+(1000359109/2500000000 : ℝ)*X 0 1+(140443521/312500000 : ℝ)*X 0 2+(424203421/1000000000 : ℝ)*X 1 0+(1000359109/2500000000 : ℝ)*X 1 1+(140443521/312500000 : ℝ)*X 1 2+(424203421/1000000000 : ℝ)*X 2 0+(1000359109/2500000000 : ℝ)*X 2 1+(140443521/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-445327813/2500000000 : ℝ)*X 0 0+(65247607/125000000 : ℝ)*X 0 1+(217036633/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293299387/10000000000 : ℝ)*X 1 0+(-67227111/400000000 : ℝ)*X 1 1+(542591591/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1058659963/2000000000 : ℝ)*X 2 0+(2712957781/5000000000 : ℝ)*X 2 1+(-420169417/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((530262569/1250000000 : ℝ)*X 0 0+(4491586323/10000000000 : ℝ)*X 0 1+(200203097/500000000 : ℝ)*X 0 2+(530262569/1250000000 : ℝ)*X 1 0+(4491586323/10000000000 : ℝ)*X 1 1+(200203097/500000000 : ℝ)*X 1 2+(530262569/1250000000 : ℝ)*X 2 0+(4491586323/10000000000 : ℝ)*X 2 1+(200203097/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (471959882643667478383/92000000000000000000000000 : ℝ) := by norm_num
    linear_combination (854258693/100000000000000 : ℝ)*(base19) + (205996487/25000000000000 : ℝ)*(base23) + (3043971/12500000000000 : ℝ)*(lower2) + (115563797/100000000000000 : ℝ)*(upper3) + (92438207/100000000000000 : ℝ)*(upper5) + (341487992926591/10000000000000 : ℝ)*(major0) + (341487992926591/10000000000000 : ℝ)*(major1) + (341487992926591/10000000000000 : ℝ)*(major2) + (4800332657059773/100000000000000 : ℝ)*(sp0) + (4800345937414441/100000000000000 : ℝ)*(sp1) + (2400172983843593/50000000000000 : ℝ)*(sp2) + (2029406701346429/100000000000000 : ℝ)*(sp3) + (14134613361/100000000000000 : ℝ)*(sp4) + (1238902459/20000000000000 : ℝ)*(sp7) + (507353223964681/25000000000000 : ℝ)*(f.failure) + (2400173395836567/50000000000000 : ℝ)*(f.sum) + (662751653377/165600000000000000000000000 : ℝ)*base65 + (44699391297810997/20700000000000000000000000000000 : ℝ)*base67 + (139212831969089003/20700000000000000000000000000000 : ℝ)*base70 + (25447588326089003/20700000000000000000000000000000 : ℝ)*base72 + (819054627601/165600000000000000000000000 : ℝ)*base73 + (26101586960010997/20700000000000000000000000000000 : ℝ)*base75 + (104864140245510997/20700000000000000000000000000000 : ℝ)*base77 + (82636728419789003/20700000000000000000000000000000 : ℝ)*base80 + (1106590543229/828000000000000000000000000 : ℝ)*base81 + (905411/312500000000000000000 : ℝ)*base90 + (905411/312500000000000000000 : ℝ)*base92 + (905411/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (72690689402471480387/12000000000000000000000000 : ℝ) := by norm_num
    linear_combination (602832421/100000000000000 : ℝ)*(base19) + (1502427519/100000000000000 : ℝ)*(base23) + (100086607/50000000000000 : ℝ)*(upper3) + (48809467/25000000000000 : ℝ)*(lower4) + (50206959/100000000000000 : ℝ)*(upper5) + (1725754531685741/50000000000000 : ℝ)*(major0) + (1725754531685741/50000000000000 : ℝ)*(major1) + (1725754531685741/50000000000000 : ℝ)*(major2) + (2818598451/50000000000000 : ℝ)*(sp1) + (4732364919/25000000000000 : ℝ)*(sp2) + (1212959218380769/25000000000000 : ℝ)*(sp4) + (606478829186719/12500000000000 : ℝ)*(sp5) + (121295411040897/2500000000000 : ℝ)*(sp6) + (1025590525650649/50000000000000 : ℝ)*(sp7) + (1025590525650649/50000000000000 : ℝ)*(f.failure) + (1212959218380769/25000000000000 : ℝ)*(f.sum) + (45328855409/7200000000000000000000000 : ℝ)*base65 + (14324053125734089/4500000000000000000000000000000 : ℝ)*base67 + (24470437901265911/4500000000000000000000000000000 : ℝ)*base70 + (4928938601265911/4500000000000000000000000000000 : ℝ)*base72 + (118764013333/36000000000000000000000000 : ℝ)*base73 + (59799479277734089/4500000000000000000000000000000 : ℝ)*base75 + (20617787957265911/4500000000000000000000000000000 : ℝ)*base78 + (48488282751734089/4500000000000000000000000000000 : ℝ)*base79 + (6605704063/7200000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1798819/625000000000000000000 : ℝ)*base90 + (1798819/625000000000000000000 : ℝ)*base92 + (1798819/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1573_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21033669/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3951/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2709/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (111/1000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7759/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1573_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1573_s4_0 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-890750437/5000000000 : ℝ)*x 0 + (1356391109/2500000000 : ℝ)*x 1 + (652502991/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (890750437/5000000000 : ℝ)^4643 ≤ (10934404402051/100000000000000 : ℝ)^3619 := by
    have hnat : (890750437 : ℕ)^4643*100000000000000^3619 ≤ 10934404402051^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      890750437 5000000000 10934404402051 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356391109/2500000000 : ℝ)^4643 ≤ (22817908375547/50000000000000 : ℝ)^3619 := by
    have hnat : (1356391109 : ℕ)^4643*50000000000000^3619 ≤ 22817908375547^3619*2500000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356391109 2500000000 22817908375547 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (652502991/1250000000 : ℝ)^4643 ≤ (21714889416987/50000000000000 : ℝ)^3619 := by
    have hnat : (652502991 : ℕ)^4643*50000000000000^3619 ≤ 21714889416987^3619*1250000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652502991 1250000000 21714889416987 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-890750437/5000000000 : ℝ), (1356391109/2500000000 : ℝ), (652502991/1250000000 : ℝ)] ![(10934404402051/100000000000000 : ℝ), (22817908375547/50000000000000 : ℝ), (21714889416987/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-890750437/5000000000 : ℝ)|^4643 ≤ (10934404402051/100000000000000 : ℝ)^3619
        have hw : |(-890750437/5000000000 : ℝ)|=(890750437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1356391109/2500000000 : ℝ)|^4643 ≤ (22817908375547/50000000000000 : ℝ)^3619
        have hw : |(1356391109/2500000000 : ℝ)|=(1356391109/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(652502991/1250000000 : ℝ)|^4643 ≤ (21714889416987/50000000000000 : ℝ)^3619
        have hw : |(652502991/1250000000 : ℝ)|=(652502991/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s4_1 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348047219/10000000000 : ℝ)*x 0 + (-943325067/5000000000 : ℝ)*x 1 + (5220023941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348047219/10000000000 : ℝ)^4643 ≤ (2800062949087/6250000000000 : ℝ)^3619 := by
    have hnat : (5348047219 : ℕ)^4643*6250000000000^3619 ≤ 2800062949087^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348047219 10000000000 2800062949087 6250000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (943325067/5000000000 : ℝ)^4643 ≤ (5884606916907/50000000000000 : ℝ)^3619 := by
    have hnat : (943325067 : ℕ)^4643*50000000000000^3619 ≤ 5884606916907^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      943325067 5000000000 5884606916907 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5220023941/10000000000 : ℝ)^4643 ≤ (8685955794547/20000000000000 : ℝ)^3619 := by
    have hnat : (5220023941 : ℕ)^4643*20000000000000^3619 ≤ 8685955794547^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220023941 10000000000 8685955794547 20000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348047219/10000000000 : ℝ), (-943325067/5000000000 : ℝ), (5220023941/10000000000 : ℝ)] ![(2800062949087/6250000000000 : ℝ), (5884606916907/50000000000000 : ℝ), (8685955794547/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348047219/10000000000 : ℝ)|^4643 ≤ (2800062949087/6250000000000 : ℝ)^3619
        have hw : |(5348047219/10000000000 : ℝ)|=(5348047219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-943325067/5000000000 : ℝ)|^4643 ≤ (5884606916907/50000000000000 : ℝ)^3619
        have hw : |(-943325067/5000000000 : ℝ)|=(943325067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5220023941/10000000000 : ℝ)|^4643 ≤ (8685955794547/20000000000000 : ℝ)^3619
        have hw : |(5220023941/10000000000 : ℝ)|=(5220023941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s4_2 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348047223/10000000000 : ℝ)*x 0 + (5220023937/10000000000 : ℝ)*x 1 + (-1886650133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348047223/10000000000 : ℝ)^4643 ≤ (44801007228381/100000000000000 : ℝ)^3619 := by
    have hnat : (5348047223 : ℕ)^4643*100000000000000^3619 ≤ 44801007228381^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348047223 10000000000 44801007228381 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5220023937/10000000000 : ℝ)^4643 ≤ (43429778930039/100000000000000 : ℝ)^3619 := by
    have hnat : (5220023937 : ℕ)^4643*100000000000000^3619 ≤ 43429778930039^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220023937 10000000000 43429778930039 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1886650133/10000000000 : ℝ)^4643 ≤ (11769213825811/100000000000000 : ℝ)^3619 := by
    have hnat : (1886650133 : ℕ)^4643*100000000000000^3619 ≤ 11769213825811^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1886650133 10000000000 11769213825811 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348047223/10000000000 : ℝ), (5220023937/10000000000 : ℝ), (-1886650133/10000000000 : ℝ)] ![(44801007228381/100000000000000 : ℝ), (43429778930039/100000000000000 : ℝ), (11769213825811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348047223/10000000000 : ℝ)|^4643 ≤ (44801007228381/100000000000000 : ℝ)^3619
        have hw : |(5348047223/10000000000 : ℝ)|=(5348047223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5220023937/10000000000 : ℝ)|^4643 ≤ (43429778930039/100000000000000 : ℝ)^3619
        have hw : |(5220023937/10000000000 : ℝ)|=(5220023937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1886650133/10000000000 : ℝ)|^4643 ≤ (11769213825811/100000000000000 : ℝ)^3619
        have hw : |(-1886650133/10000000000 : ℝ)|=(1886650133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s4_3 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2121086007/5000000000 : ℝ)*x 0 + (2002353949/5000000000 : ℝ)*x 1 + (4490890681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2121086007/5000000000 : ℝ)^4643 ≤ (33282349004177/100000000000000 : ℝ)^3619 := by
    have hnat : (2121086007 : ℕ)^4643*100000000000000^3619 ≤ 33282349004177^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121086007 5000000000 33282349004177 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2002353949/5000000000 : ℝ)^4643 ≤ (6182267983699/20000000000000 : ℝ)^3619 := by
    have hnat : (2002353949 : ℕ)^4643*20000000000000^3619 ≤ 6182267983699^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2002353949 5000000000 6182267983699 20000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4490890681/10000000000 : ℝ)^4643 ≤ (8951577764097/25000000000000 : ℝ)^3619 := by
    have hnat : (4490890681 : ℕ)^4643*25000000000000^3619 ≤ 8951577764097^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490890681 10000000000 8951577764097 25000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2121086007/5000000000 : ℝ), (2002353949/5000000000 : ℝ), (4490890681/10000000000 : ℝ)] ![(33282349004177/100000000000000 : ℝ), (6182267983699/20000000000000 : ℝ), (8951577764097/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2121086007/5000000000 : ℝ)|^4643 ≤ (33282349004177/100000000000000 : ℝ)^3619
        have hw : |(2121086007/5000000000 : ℝ)|=(2121086007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2002353949/5000000000 : ℝ)|^4643 ≤ (6182267983699/20000000000000 : ℝ)^3619
        have hw : |(2002353949/5000000000 : ℝ)|=(2002353949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4490890681/10000000000 : ℝ)|^4643 ≤ (8951577764097/25000000000000 : ℝ)^3619
        have hw : |(4490890681/10000000000 : ℝ)|=(4490890681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s4_4 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1781527647/10000000000 : ℝ)*x 0 + (1305274189/2500000000 : ℝ)*x 1 + (5424483669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1781527647/10000000000 : ℝ)^4643 ≤ (2186923044929/20000000000000 : ℝ)^3619 := by
    have hnat : (1781527647 : ℕ)^4643*20000000000000^3619 ≤ 2186923044929^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1781527647 10000000000 2186923044929 20000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1305274189/2500000000 : ℝ)^4643 ≤ (43441230480943/100000000000000 : ℝ)^3619 := by
    have hnat : (1305274189 : ℕ)^4643*100000000000000^3619 ≤ 43441230480943^3619*2500000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305274189 2500000000 43441230480943 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5424483669/10000000000 : ℝ)^4643 ≤ (1140603856827/2500000000000 : ℝ)^3619 := by
    have hnat : (5424483669 : ℕ)^4643*2500000000000^3619 ≤ 1140603856827^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424483669 10000000000 1140603856827 2500000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1781527647/10000000000 : ℝ), (1305274189/2500000000 : ℝ), (5424483669/10000000000 : ℝ)] ![(2186923044929/20000000000000 : ℝ), (43441230480943/100000000000000 : ℝ), (1140603856827/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1781527647/10000000000 : ℝ)|^4643 ≤ (2186923044929/20000000000000 : ℝ)^3619
        have hw : |(-1781527647/10000000000 : ℝ)|=(1781527647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1305274189/2500000000 : ℝ)|^4643 ≤ (43441230480943/100000000000000 : ℝ)^3619
        have hw : |(1305274189/2500000000 : ℝ)|=(1305274189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5424483669/10000000000 : ℝ)|^4643 ≤ (1140603856827/2500000000000 : ℝ)^3619
        have hw : |(5424483669/10000000000 : ℝ)|=(5424483669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s4_5 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661706021/1250000000 : ℝ)*x 0 + (-1682190391/10000000000 : ℝ)*x 1 + (1356120917/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661706021/1250000000 : ℝ)^4643 ≤ (44217203252537/100000000000000 : ℝ)^3619 := by
    have hnat : (661706021 : ℕ)^4643*100000000000000^3619 ≤ 44217203252537^3619*1250000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661706021 1250000000 44217203252537 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1682190391/10000000000 : ℝ)^4643 ≤ (2539660619191/25000000000000 : ℝ)^3619 := by
    have hnat : (1682190391 : ℕ)^4643*25000000000000^3619 ≤ 2539660619191^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1682190391 10000000000 2539660619191 25000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356120917/2500000000 : ℝ)^4643 ≤ (45624154262289/100000000000000 : ℝ)^3619 := by
    have hnat : (1356120917 : ℕ)^4643*100000000000000^3619 ≤ 45624154262289^3619*2500000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356120917 2500000000 45624154262289 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661706021/1250000000 : ℝ), (-1682190391/10000000000 : ℝ), (1356120917/2500000000 : ℝ)] ![(44217203252537/100000000000000 : ℝ), (2539660619191/25000000000000 : ℝ), (45624154262289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661706021/1250000000 : ℝ)|^4643 ≤ (44217203252537/100000000000000 : ℝ)^3619
        have hw : |(661706021/1250000000 : ℝ)|=(661706021/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1682190391/10000000000 : ℝ)|^4643 ≤ (2539660619191/25000000000000 : ℝ)^3619
        have hw : |(-1682190391/10000000000 : ℝ)|=(1682190391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356120917/2500000000 : ℝ)|^4643 ≤ (45624154262289/100000000000000 : ℝ)^3619
        have hw : |(1356120917/2500000000 : ℝ)|=(1356120917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s4_6 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646824083/5000000000 : ℝ)*x 0 + (216979347/400000000 : ℝ)*x 1 + (-1682190383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646824083/5000000000 : ℝ)^4643 ≤ (345446900243/781250000000 : ℝ)^3619 := by
    have hnat : (2646824083 : ℕ)^4643*781250000000^3619 ≤ 345446900243^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646824083 5000000000 345446900243 781250000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216979347/400000000 : ℝ)^4643 ≤ (1425754823057/3125000000000 : ℝ)^3619 := by
    have hnat : (216979347 : ℕ)^4643*3125000000000^3619 ≤ 1425754823057^3619*400000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216979347 400000000 1425754823057 3125000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1682190383/10000000000 : ℝ)^4643 ≤ (5079321207391/50000000000000 : ℝ)^3619 := by
    have hnat : (1682190383 : ℕ)^4643*50000000000000^3619 ≤ 5079321207391^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1682190383 10000000000 5079321207391 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646824083/5000000000 : ℝ), (216979347/400000000 : ℝ), (-1682190383/10000000000 : ℝ)] ![(345446900243/781250000000 : ℝ), (1425754823057/3125000000000 : ℝ), (5079321207391/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646824083/5000000000 : ℝ)|^4643 ≤ (345446900243/781250000000 : ℝ)^3619
        have hw : |(2646824083/5000000000 : ℝ)|=(2646824083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216979347/400000000 : ℝ)|^4643 ≤ (1425754823057/3125000000000 : ℝ)^3619
        have hw : |(216979347/400000000 : ℝ)|=(216979347/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1682190383/10000000000 : ℝ)|^4643 ≤ (5079321207391/50000000000000 : ℝ)^3619
        have hw : |(-1682190383/10000000000 : ℝ)|=(1682190383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s4_7 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2121117673/5000000000 : ℝ)*x 0 + (4488353139/10000000000 : ℝ)*x 1 + (1001816061/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2121117673/5000000000 : ℝ)^4643 ≤ (1664149323721/5000000000000 : ℝ)^3619 := by
    have hnat : (2121117673 : ℕ)^4643*5000000000000^3619 ≤ 1664149323721^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121117673 5000000000 1664149323721 5000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4488353139/10000000000 : ℝ)^4643 ≤ (35780356374339/100000000000000 : ℝ)^3619 := by
    have hnat : (4488353139 : ℕ)^4643*100000000000000^3619 ≤ 35780356374339^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488353139 10000000000 35780356374339 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1001816061/2500000000 : ℝ)^4643 ≤ (15468328566901/50000000000000 : ℝ)^3619 := by
    have hnat : (1001816061 : ℕ)^4643*50000000000000^3619 ≤ 15468328566901^3619*2500000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001816061 2500000000 15468328566901 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2121117673/5000000000 : ℝ), (4488353139/10000000000 : ℝ), (1001816061/2500000000 : ℝ)] ![(1664149323721/5000000000000 : ℝ), (35780356374339/100000000000000 : ℝ), (15468328566901/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2121117673/5000000000 : ℝ)|^4643 ≤ (1664149323721/5000000000000 : ℝ)^3619
        have hw : |(2121117673/5000000000 : ℝ)|=(2121117673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4488353139/10000000000 : ℝ)|^4643 ≤ (35780356374339/100000000000000 : ℝ)^3619
        have hw : |(4488353139/10000000000 : ℝ)|=(4488353139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1001816061/2500000000 : ℝ)|^4643 ≤ (15468328566901/50000000000000 : ℝ)^3619
        have hw : |(1001816061/2500000000 : ℝ)|=(1001816061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1573_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21033669/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7759/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (111/1000 : ℝ)*pair X i i ≤ pair X i h) :
    (1391/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (484/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7759/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (111/1000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7759/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (111/1000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7759/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (111/1000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7759/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (111/1000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7759/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (111/1000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7759/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (111/1000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (111/1000 : ℝ) ^ (4641/1024 : ℝ) ≤ (4711806488034213/100000000000000000000 : ℝ) := by
    have hpowers : (111/1000 : ℝ)^4641 ≤ (4711806488034213/100000000000000000000 : ℝ)^1024 := by
      have hnat : (111 : ℕ)^4641*100000000000000000000^1024 ≤ 4711806488034213^1024*1000^4641 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        111 1000 4711806488034213 100000000000000000000 4641 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (111/1000 : ℝ)) (X := (4711806488034213/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4641 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7759/50000 : ℝ) ^ (4641/1024 : ℝ) ≤ (21512172986721909/100000000000000000000 : ℝ) := by
    have hpowers : (7759/50000 : ℝ)^4641 ≤ (21512172986721909/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7759 : ℕ)^4641*100000000000000000000^1024 ≤ 21512172986721909^1024*50000^4641 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7759 50000 21512172986721909 100000000000000000000 4641 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7759/50000 : ℝ)) (X := (21512172986721909/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4641 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004711806488034213/50000000000000000000 : ℝ) ≤ (500010395847177/500000000000000 : ℝ) ^ (4641/1024 : ℝ) := by
    have hpowers : (50004711806488034213/50000000000000000000 : ℝ)^1024 ≤ (500010395847177/500000000000000 : ℝ)^4641 := by
      have hnat : (50004711806488034213 : ℕ)^1024*500000000000000^4641 ≤ 500010395847177^4641*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004711806488034213 50000000000000000000 500010395847177 500000000000000 1024 4641 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500010395847177/500000000000000 : ℝ)) (X := (50004711806488034213/50000000000000000000 : ℝ)) (by norm_num) 4641 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50013111989737378061/50000000000000000000 : ℝ) ≤ (10000578552279307/10000000000000000 : ℝ) ^ (4641/1024 : ℝ) := by
    have hpowers : (50013111989737378061/50000000000000000000 : ℝ)^1024 ≤ (10000578552279307/10000000000000000 : ℝ)^4641 := by
      have hnat : (50013111989737378061 : ℕ)^1024*10000000000000000^4641 ≤ 10000578552279307^4641*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013111989737378061 50000000000000000000 10000578552279307 10000000000000000 1024 4641 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000578552279307/10000000000000000 : ℝ)) (X := (50013111989737378061/50000000000000000000 : ℝ)) (by norm_num) 4641 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50021512172986721909/50000000000000000000 : ℝ) ≤ (5000474593807537/5000000000000000 : ℝ) ^ (4641/1024 : ℝ) := by
    have hpowers : (50021512172986721909/50000000000000000000 : ℝ)^1024 ≤ (5000474593807537/5000000000000000 : ℝ)^4641 := by
      have hnat : (50021512172986721909 : ℕ)^1024*5000000000000000^4641 ≤ 5000474593807537^4641*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021512172986721909 50000000000000000000 5000474593807537 5000000000000000 1024 4641 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000474593807537/5000000000000000 : ℝ)) (X := (50021512172986721909/50000000000000000000 : ℝ)) (by norm_num) 4641 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4711806488034213/100000000000000000000 : ℝ) ≤ ((276079315453765827/276125000000000000 : ℝ)+2*(370635335767/441800000000000 : ℝ)*(111/1000 : ℝ))^(4641/1024 : ℝ) := by
    rw [show (276079315453765827/276125000000000000 : ℝ)+2*(370635335767/441800000000000 : ℝ)*(111/1000 : ℝ)=(500010395847177/500000000000000 : ℝ) by norm_num, show 1+2*(4711806488034213/100000000000000000000 : ℝ)=(50004711806488034213/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(21512172986721909/100000000000000000000 : ℝ)+(4711806488034213/100000000000000000000 : ℝ) ≤ ((276079315453765827/276125000000000000 : ℝ)+(370635335767/441800000000000 : ℝ)*((7759/50000 : ℝ)+(111/1000 : ℝ)))^(4641/1024 : ℝ) := by
    rw [show (276079315453765827/276125000000000000 : ℝ)+(370635335767/441800000000000 : ℝ)*((7759/50000 : ℝ)+(111/1000 : ℝ))=(10000578552279307/10000000000000000 : ℝ) by norm_num, show 1+(21512172986721909/100000000000000000000 : ℝ)+(4711806488034213/100000000000000000000 : ℝ)=(50013111989737378061/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(21512172986721909/100000000000000000000 : ℝ) ≤ ((276079315453765827/276125000000000000 : ℝ)+2*(370635335767/441800000000000 : ℝ)*(7759/50000 : ℝ))^(4641/1024 : ℝ) := by
    rw [show (276079315453765827/276125000000000000 : ℝ)+2*(370635335767/441800000000000 : ℝ)*(7759/50000 : ℝ)=(5000474593807537/5000000000000000 : ℝ) by norm_num, show 1+2*(21512172986721909/100000000000000000000 : ℝ)=(50021512172986721909/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (276079315453765827/276125000000000000 : ℝ)*(X 1 0+X 2 0)+(370635335767/441800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4641/1024 : ℝ)) (lo := (111/1000 : ℝ)) (hi := (7759/50000 : ℝ)) (c := (276079315453765827/276125000000000000 : ℝ)) (alpha := (370635335767/441800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (276079315453765827/276125000000000000 : ℝ)*(X 0 1+X 2 1)+(370635335767/441800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4641/1024 : ℝ)) (lo := (111/1000 : ℝ)) (hi := (7759/50000 : ℝ)) (c := (276079315453765827/276125000000000000 : ℝ)) (alpha := (370635335767/441800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (276079315453765827/276125000000000000 : ℝ)*(X 0 2+X 1 2)+(370635335767/441800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4641/1024 : ℝ)) (lo := (111/1000 : ℝ)) (hi := (7759/50000 : ℝ)) (c := (276079315453765827/276125000000000000 : ℝ)) (alpha := (370635335767/441800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-890750437/5000000000 : ℝ)*X 0 0+(1356391109/2500000000 : ℝ)*X 0 1+(652502991/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348047219/10000000000 : ℝ)*X 1 0+(-943325067/5000000000 : ℝ)*X 1 1+(5220023941/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348047223/10000000000 : ℝ)*X 2 0+(5220023937/10000000000 : ℝ)*X 2 1+(-1886650133/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2121086007/5000000000 : ℝ)*X 0 0+(2002353949/5000000000 : ℝ)*X 0 1+(4490890681/10000000000 : ℝ)*X 0 2+(2121086007/5000000000 : ℝ)*X 1 0+(2002353949/5000000000 : ℝ)*X 1 1+(4490890681/10000000000 : ℝ)*X 1 2+(2121086007/5000000000 : ℝ)*X 2 0+(2002353949/5000000000 : ℝ)*X 2 1+(4490890681/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1781527647/10000000000 : ℝ)*X 0 0+(1305274189/2500000000 : ℝ)*X 0 1+(5424483669/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((661706021/1250000000 : ℝ)*X 1 0+(-1682190391/10000000000 : ℝ)*X 1 1+(1356120917/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2646824083/5000000000 : ℝ)*X 2 0+(216979347/400000000 : ℝ)*X 2 1+(-1682190383/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2121117673/5000000000 : ℝ)*X 0 0+(4488353139/10000000000 : ℝ)*X 0 1+(1001816061/2500000000 : ℝ)*X 0 2+(2121117673/5000000000 : ℝ)*X 1 0+(4488353139/10000000000 : ℝ)*X 1 1+(1001816061/2500000000 : ℝ)*X 1 2+(2121117673/5000000000 : ℝ)*X 2 0+(4488353139/10000000000 : ℝ)*X 2 1+(1001816061/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10456783837819532523081813/1380625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (318419473/25000000000000 : ℝ)*(base19) + (1195753477/100000000000000 : ℝ)*(base23) + (872409/2000000000000 : ℝ)*(lower2) + (187511499/100000000000000 : ℝ)*(upper3) + (130023509/100000000000000 : ℝ)*(upper5) + (43263257166669/1250000000000 : ℝ)*(major0) + (43263257166669/1250000000000 : ℝ)*(major1) + (43263257166669/1250000000000 : ℝ)*(major2) + (4865242606031917/100000000000000 : ℝ)*(sp0) + (1216315561848029/25000000000000 : ℝ)*(sp1) + (4865262325316531/100000000000000 : ℝ)*(sp2) + (82273919658119/4000000000000 : ℝ)*(sp3) + (20915038091/100000000000000 : ℝ)*(sp4) + (9381679073/100000000000000 : ℝ)*(sp7) + (2056857373132049/100000000000000 : ℝ)*(f.failure) + (608157940133751/12500000000000 : ℝ)*(f.sum) + (8863396313227/2209000000000000000000000000 : ℝ)*base65 + (2396131623572927/1380625000000000000000000000000 : ℝ)*base67 + (488117830401151/690312500000000000000000000000 : ℝ)*base69 + (99965321073931/172578125000000000000000000000 : ℝ)*base72 + (8869681846007/2209000000000000000000000000 : ℝ)*base73 + (7436865790859177/1380625000000000000000000000000 : ℝ)*base75 + (1123089807267073/1380625000000000000000000000000 : ℝ)*base78 + (1831528599760263/345156250000000000000000000000 : ℝ)*base79 + (312914537927/552250000000000000000000000 : ℝ)*base81 + (11957781/1250000000000000000000 : ℝ)*base89 + (11957781/1250000000000000000000 : ℝ)*base91 + (11957781/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (168937996983136846963161819/13806250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (961738991/50000000000000 : ℝ)*(base19) + (2088336443/100000000000000 : ℝ)*(base23) + (263294913/100000000000000 : ℝ)*(upper3) + (2250519/3125000000000 : ℝ)*(lower4) + (240202203/100000000000000 : ℝ)*(upper5) + (3497676691371087/100000000000000 : ℝ)*(major0) + (3497676691371087/100000000000000 : ℝ)*(major1) + (3497676691371087/100000000000000 : ℝ)*(major2) + (30143046481/100000000000000 : ℝ)*(sp1) + (2070489927/6250000000000 : ℝ)*(sp2) + (2458367590773589/50000000000000 : ℝ)*(sp4) + (983340623004543/20000000000000 : ℝ)*(sp5) + (4916699965371903/100000000000000 : ℝ)*(sp6) + (519654448329231/25000000000000 : ℝ)*(sp7) + (519654448329231/25000000000000 : ℝ)*(f.failure) + (2458367590773589/50000000000000 : ℝ)*(f.sum) + (19164812034309/22090000000000000000000000000 : ℝ)*base65 + (132090528605525213/13806250000000000000000000000000 : ℝ)*base68 + (132136400340562713/13806250000000000000000000000000 : ℝ)*base70 + (74520387369468963/13806250000000000000000000000000 : ℝ)*base72 + (21914831702801/22090000000000000000000000000 : ℝ)*base74 + (149370523510756463/13806250000000000000000000000000 : ℝ)*base76 + (10317348669437287/13806250000000000000000000000000 : ℝ)*base77 + (64834079512206463/13806250000000000000000000000000 : ℝ)*base80 + (33878377571139/22090000000000000000000000000 : ℝ)*base81 + (1003539/312500000000000000000 : ℝ)*base89 + (1003539/312500000000000000000 : ℝ)*base91 + (1003539/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1573_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21033669/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7759/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (111/1000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1391/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (484/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1573_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1573_s5_0 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1781522161/10000000000 : ℝ)*x 0 + (5425421203/10000000000 : ℝ)*x 1 + (522015303/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1781522161/10000000000 : ℝ)^4643 ≤ (10934572025351/100000000000000 : ℝ)^3619 := by
    have hnat : (1781522161 : ℕ)^4643*100000000000000^3619 ≤ 10934572025351^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1781522161 10000000000 10934572025351 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5425421203/10000000000 : ℝ)^4643 ≤ (4563427109643/10000000000000 : ℝ)^3619 := by
    have hnat : (5425421203 : ℕ)^4643*10000000000000^3619 ≤ 4563427109643^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425421203 10000000000 4563427109643 10000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (522015303/1000000000 : ℝ)^4643 ≤ (542889460841/1250000000000 : ℝ)^3619 := by
    have hnat : (522015303 : ℕ)^4643*1250000000000^3619 ≤ 542889460841^3619*1000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522015303 1000000000 542889460841 1250000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1781522161/10000000000 : ℝ), (5425421203/10000000000 : ℝ), (522015303/1000000000 : ℝ)] ![(10934572025351/100000000000000 : ℝ), (4563427109643/10000000000000 : ℝ), (542889460841/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1781522161/10000000000 : ℝ)|^4643 ≤ (10934572025351/100000000000000 : ℝ)^3619
        have hw : |(-1781522161/10000000000 : ℝ)|=(1781522161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5425421203/10000000000 : ℝ)|^4643 ≤ (4563427109643/10000000000000 : ℝ)^3619
        have hw : |(5425421203/10000000000 : ℝ)|=(5425421203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(522015303/1000000000 : ℝ)|^4643 ≤ (542889460841/1250000000000 : ℝ)^3619
        have hw : |(522015303/1000000000 : ℝ)|=(522015303/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s5_1 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348009517/10000000000 : ℝ)*x 0 + (-1886527213/10000000000 : ℝ)*x 1 + (1044030813/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348009517/10000000000 : ℝ)^4643 ≤ (44800601988037/100000000000000 : ℝ)^3619 := by
    have hnat : (5348009517 : ℕ)^4643*100000000000000^3619 ≤ 44800601988037^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348009517 10000000000 44800601988037 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1886527213/10000000000 : ℝ)^4643 ≤ (5884115037921/50000000000000 : ℝ)^3619 := by
    have hnat : (1886527213 : ℕ)^4643*50000000000000^3619 ≤ 5884115037921^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1886527213 10000000000 5884115037921 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1044030813/2000000000 : ℝ)^4643 ≤ (43431167914897/100000000000000 : ℝ)^3619 := by
    have hnat : (1044030813 : ℕ)^4643*100000000000000^3619 ≤ 43431167914897^3619*2000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044030813 2000000000 43431167914897 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348009517/10000000000 : ℝ), (-1886527213/10000000000 : ℝ), (1044030813/2000000000 : ℝ)] ![(44800601988037/100000000000000 : ℝ), (5884115037921/50000000000000 : ℝ), (43431167914897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348009517/10000000000 : ℝ)|^4643 ≤ (44800601988037/100000000000000 : ℝ)^3619
        have hw : |(5348009517/10000000000 : ℝ)|=(5348009517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1886527213/10000000000 : ℝ)|^4643 ≤ (5884115037921/50000000000000 : ℝ)^3619
        have hw : |(-1886527213/10000000000 : ℝ)|=(1886527213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1044030813/2000000000 : ℝ)|^4643 ≤ (43431167914897/100000000000000 : ℝ)^3619
        have hw : |(1044030813/2000000000 : ℝ)|=(1044030813/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s5_2 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267400477/500000000 : ℝ)*x 0 + (5220154169/10000000000 : ℝ)*x 1 + (-471631761/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267400477/500000000 : ℝ)^4643 ≤ (44800602235227/100000000000000 : ℝ)^3619 := by
    have hnat : (267400477 : ℕ)^4643*100000000000000^3619 ≤ 44800602235227^3619*500000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267400477 500000000 44800602235227 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5220154169/10000000000 : ℝ)^4643 ≤ (10857792256249/25000000000000 : ℝ)^3619 := by
    have hnat : (5220154169 : ℕ)^4643*25000000000000^3619 ≤ 10857792256249^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220154169 10000000000 10857792256249 25000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (471631761/2500000000 : ℝ)^4643 ≤ (5884114361659/50000000000000 : ℝ)^3619 := by
    have hnat : (471631761 : ℕ)^4643*50000000000000^3619 ≤ 5884114361659^3619*2500000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471631761 2500000000 5884114361659 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267400477/500000000 : ℝ), (5220154169/10000000000 : ℝ), (-471631761/2500000000 : ℝ)] ![(44800602235227/100000000000000 : ℝ), (10857792256249/25000000000000 : ℝ), (5884114361659/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267400477/500000000 : ℝ)|^4643 ≤ (44800602235227/100000000000000 : ℝ)^3619
        have hw : |(267400477/500000000 : ℝ)|=(267400477/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5220154169/10000000000 : ℝ)|^4643 ≤ (10857792256249/25000000000000 : ℝ)^3619
        have hw : |(5220154169/10000000000 : ℝ)|=(5220154169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-471631761/2500000000 : ℝ)|^4643 ≤ (5884114361659/50000000000000 : ℝ)^3619
        have hw : |(-471631761/2500000000 : ℝ)|=(471631761/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s5_3 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2121093127/5000000000 : ℝ)*x 0 + (1001257959/2500000000 : ℝ)*x 1 + (4490563059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2121093127/5000000000 : ℝ)^4643 ≤ (33282492337111/100000000000000 : ℝ)^3619 := by
    have hnat : (2121093127 : ℕ)^4643*100000000000000^3619 ≤ 33282492337111^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121093127 5000000000 33282492337111 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1001257959/2500000000 : ℝ)^4643 ≤ (3091454784163/10000000000000 : ℝ)^3619 := by
    have hnat : (1001257959 : ℕ)^4643*10000000000000^3619 ≤ 3091454784163^3619*2500000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001257959 2500000000 3091454784163 10000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4490563059/10000000000 : ℝ)^4643 ≤ (35802959814529/100000000000000 : ℝ)^3619 := by
    have hnat : (4490563059 : ℕ)^4643*100000000000000^3619 ≤ 35802959814529^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490563059 10000000000 35802959814529 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2121093127/5000000000 : ℝ), (1001257959/2500000000 : ℝ), (4490563059/10000000000 : ℝ)] ![(33282492337111/100000000000000 : ℝ), (3091454784163/10000000000000 : ℝ), (35802959814529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2121093127/5000000000 : ℝ)|^4643 ≤ (33282492337111/100000000000000 : ℝ)^3619
        have hw : |(2121093127/5000000000 : ℝ)|=(2121093127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1001257959/2500000000 : ℝ)|^4643 ≤ (3091454784163/10000000000000 : ℝ)^3619
        have hw : |(1001257959/2500000000 : ℝ)|=(1001257959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4490563059/10000000000 : ℝ)|^4643 ≤ (35802959814529/100000000000000 : ℝ)^3619
        have hw : |(4490563059/10000000000 : ℝ)|=(4490563059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s5_4 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-890774331/5000000000 : ℝ)*x 0 + (2610612169/5000000000 : ℝ)*x 1 + (5424342123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (890774331/5000000000 : ℝ)^4643 ≤ (10934780706797/100000000000000 : ℝ)^3619 := by
    have hnat : (890774331 : ℕ)^4643*100000000000000^3619 ≤ 10934780706797^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      890774331 5000000000 10934780706797 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2610612169/5000000000 : ℝ)^4643 ≤ (10860648092229/25000000000000 : ℝ)^3619 := by
    have hnat : (2610612169 : ℕ)^4643*25000000000000^3619 ≤ 10860648092229^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610612169 5000000000 10860648092229 25000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5424342123/10000000000 : ℝ)^4643 ≤ (11405656727297/25000000000000 : ℝ)^3619 := by
    have hnat : (5424342123 : ℕ)^4643*25000000000000^3619 ≤ 11405656727297^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424342123 10000000000 11405656727297 25000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-890774331/5000000000 : ℝ), (2610612169/5000000000 : ℝ), (5424342123/10000000000 : ℝ)] ![(10934780706797/100000000000000 : ℝ), (10860648092229/25000000000000 : ℝ), (11405656727297/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-890774331/5000000000 : ℝ)|^4643 ≤ (10934780706797/100000000000000 : ℝ)^3619
        have hw : |(-890774331/5000000000 : ℝ)|=(890774331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2610612169/5000000000 : ℝ)|^4643 ≤ (10860648092229/25000000000000 : ℝ)^3619
        have hw : |(2610612169/5000000000 : ℝ)|=(2610612169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5424342123/10000000000 : ℝ)|^4643 ≤ (11405656727297/25000000000000 : ℝ)^3619
        have hw : |(5424342123/10000000000 : ℝ)|=(5424342123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s5_5 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058736547/2000000000 : ℝ)*x 0 + (-841169857/5000000000 : ℝ)*x 1 + (5424342123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058736547/2000000000 : ℝ)^4643 ≤ (11054393421111/25000000000000 : ℝ)^3619 := by
    have hnat : (1058736547 : ℕ)^4643*25000000000000^3619 ≤ 11054393421111^3619*2000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058736547 2000000000 11054393421111 25000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (841169857/5000000000 : ℝ)^4643 ≤ (5079899697663/50000000000000 : ℝ)^3619 := by
    have hnat : (841169857 : ℕ)^4643*50000000000000^3619 ≤ 5079899697663^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      841169857 5000000000 5079899697663 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5424342123/10000000000 : ℝ)^4643 ≤ (11405656727297/25000000000000 : ℝ)^3619 := by
    have hnat : (5424342123 : ℕ)^4643*25000000000000^3619 ≤ 11405656727297^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424342123 10000000000 11405656727297 25000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058736547/2000000000 : ℝ), (-841169857/5000000000 : ℝ), (5424342123/10000000000 : ℝ)] ![(11054393421111/25000000000000 : ℝ), (5079899697663/50000000000000 : ℝ), (11405656727297/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058736547/2000000000 : ℝ)|^4643 ≤ (11054393421111/25000000000000 : ℝ)^3619
        have hw : |(1058736547/2000000000 : ℝ)|=(1058736547/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-841169857/5000000000 : ℝ)|^4643 ≤ (5079899697663/50000000000000 : ℝ)^3619
        have hw : |(-841169857/5000000000 : ℝ)|=(841169857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5424342123/10000000000 : ℝ)|^4643 ≤ (11405656727297/25000000000000 : ℝ)^3619
        have hw : |(5424342123/10000000000 : ℝ)|=(5424342123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s5_6 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058736547/2000000000 : ℝ)*x 0 + (2712171061/5000000000 : ℝ)*x 1 + (-841169857/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058736547/2000000000 : ℝ)^4643 ≤ (11054393421111/25000000000000 : ℝ)^3619 := by
    have hnat : (1058736547 : ℕ)^4643*25000000000000^3619 ≤ 11054393421111^3619*2000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058736547 2000000000 11054393421111 25000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2712171061/5000000000 : ℝ)^4643 ≤ (45622626898397/100000000000000 : ℝ)^3619 := by
    have hnat : (2712171061 : ℕ)^4643*100000000000000^3619 ≤ 45622626898397^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712171061 5000000000 45622626898397 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (841169857/5000000000 : ℝ)^4643 ≤ (5079899697663/50000000000000 : ℝ)^3619 := by
    have hnat : (841169857 : ℕ)^4643*50000000000000^3619 ≤ 5079899697663^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      841169857 5000000000 5079899697663 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058736547/2000000000 : ℝ), (2712171061/5000000000 : ℝ), (-841169857/5000000000 : ℝ)] ![(11054393421111/25000000000000 : ℝ), (45622626898397/100000000000000 : ℝ), (5079899697663/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058736547/2000000000 : ℝ)|^4643 ≤ (11054393421111/25000000000000 : ℝ)^3619
        have hw : |(1058736547/2000000000 : ℝ)|=(1058736547/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2712171061/5000000000 : ℝ)|^4643 ≤ (45622626898397/100000000000000 : ℝ)^3619
        have hw : |(2712171061/5000000000 : ℝ)|=(2712171061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-841169857/5000000000 : ℝ)|^4643 ≤ (5079899697663/50000000000000 : ℝ)^3619
        have hw : |(-841169857/5000000000 : ℝ)|=(841169857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s5_7 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4242248627/10000000000 : ℝ)*x 0 + (4488033241/10000000000 : ℝ)*x 1 + (4007581067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4242248627/10000000000 : ℝ)^4643 ≤ (6656624031017/20000000000000 : ℝ)^3619 := by
    have hnat : (4242248627 : ℕ)^4643*20000000000000^3619 ≤ 6656624031017^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242248627 10000000000 6656624031017 20000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4488033241/10000000000 : ℝ)^4643 ≤ (17888542331841/50000000000000 : ℝ)^3619 := by
    have hnat : (4488033241 : ℕ)^4643*50000000000000^3619 ≤ 17888542331841^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488033241 10000000000 17888542331841 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4007581067/10000000000 : ℝ)^4643 ≤ (15469897581799/50000000000000 : ℝ)^3619 := by
    have hnat : (4007581067 : ℕ)^4643*50000000000000^3619 ≤ 15469897581799^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4007581067 10000000000 15469897581799 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4242248627/10000000000 : ℝ), (4488033241/10000000000 : ℝ), (4007581067/10000000000 : ℝ)] ![(6656624031017/20000000000000 : ℝ), (17888542331841/50000000000000 : ℝ), (15469897581799/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4242248627/10000000000 : ℝ)|^4643 ≤ (6656624031017/20000000000000 : ℝ)^3619
        have hw : |(4242248627/10000000000 : ℝ)|=(4242248627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4488033241/10000000000 : ℝ)|^4643 ≤ (17888542331841/50000000000000 : ℝ)^3619
        have hw : |(4488033241/10000000000 : ℝ)|=(4488033241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4007581067/10000000000 : ℝ)|^4643 ≤ (15469897581799/50000000000000 : ℝ)^3619
        have hw : |(4007581067/10000000000 : ℝ)|=(4007581067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1573_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21033669/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (484/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1391/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11131/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (484/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1391/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (484/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1391/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (484/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1391/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (484/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1391/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (484/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1391/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (484/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1391/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1391/12500 : ℝ) ^ (4641/1024 : ℝ) ≤ (2382957695355173/50000000000000000000 : ℝ) := by
    have hpowers : (1391/12500 : ℝ)^4641 ≤ (2382957695355173/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1391 : ℕ)^4641*50000000000000000000^1024 ≤ 2382957695355173^1024*12500^4641 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1391 12500 2382957695355173 50000000000000000000 4641 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1391/12500 : ℝ)) (X := (2382957695355173/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4641 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (484/3125 : ℝ) ^ (4641/1024 : ℝ) ≤ (1066216424638197/5000000000000000000 : ℝ) := by
    have hpowers : (484/3125 : ℝ)^4641 ≤ (1066216424638197/5000000000000000000 : ℝ)^1024 := by
      have hnat : (484 : ℕ)^4641*5000000000000000000^1024 ≤ 1066216424638197^1024*3125^4641 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        484 3125 1066216424638197 5000000000000000000 4641 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (484/3125 : ℝ)) (X := (1066216424638197/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4641 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002382957695355173/25000000000000000000 : ℝ) ≤ (10000210304507599/10000000000000000 : ℝ) ^ (4641/1024 : ℝ) := by
    have hpowers : (25002382957695355173/25000000000000000000 : ℝ)^1024 ≤ (10000210304507599/10000000000000000 : ℝ)^4641 := by
      have hnat : (25002382957695355173 : ℕ)^1024*10000000000000000^4641 ≤ 10000210304507599^4641*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002382957695355173 25000000000000000000 10000210304507599 10000000000000000 1024 4641 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000210304507599/10000000000000000 : ℝ)) (X := (25002382957695355173/25000000000000000000 : ℝ)) (by norm_num) 4641 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50013045121941737143/50000000000000000000 : ℝ) ≤ (10000575602110493/10000000000000000 : ℝ) ^ (4641/1024 : ℝ) := by
    have hpowers : (50013045121941737143/50000000000000000000 : ℝ)^1024 ≤ (10000575602110493/10000000000000000 : ℝ)^4641 := by
      have hnat : (50013045121941737143 : ℕ)^1024*10000000000000000^4641 ≤ 10000575602110493^4641*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013045121941737143 50000000000000000000 10000575602110493 10000000000000000 1024 4641 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000575602110493/10000000000000000 : ℝ)) (X := (50013045121941737143/50000000000000000000 : ℝ)) (by norm_num) 4641 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501066216424638197/2500000000000000000 : ℝ) ≤ (10000940899713387/10000000000000000 : ℝ) ^ (4641/1024 : ℝ) := by
    have hpowers : (2501066216424638197/2500000000000000000 : ℝ)^1024 ≤ (10000940899713387/10000000000000000 : ℝ)^4641 := by
      have hnat : (2501066216424638197 : ℕ)^1024*10000000000000000^4641 ≤ 10000940899713387^4641*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501066216424638197 2500000000000000000 10000940899713387 10000000000000000 1024 4641 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000940899713387/10000000000000000 : ℝ)) (X := (2501066216424638197/2500000000000000000 : ℝ)) (by norm_num) 4641 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2382957695355173/50000000000000000000 : ℝ) ≤ ((5449098358025390347/5450000000000000000 : ℝ)+2*(182648801447/218000000000000 : ℝ)*(1391/12500 : ℝ))^(4641/1024 : ℝ) := by
    rw [show (5449098358025390347/5450000000000000000 : ℝ)+2*(182648801447/218000000000000 : ℝ)*(1391/12500 : ℝ)=(10000210304507599/10000000000000000 : ℝ) by norm_num, show 1+2*(2382957695355173/50000000000000000000 : ℝ)=(25002382957695355173/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1066216424638197/5000000000000000000 : ℝ)+(2382957695355173/50000000000000000000 : ℝ) ≤ ((5449098358025390347/5450000000000000000 : ℝ)+(182648801447/218000000000000 : ℝ)*((484/3125 : ℝ)+(1391/12500 : ℝ)))^(4641/1024 : ℝ) := by
    rw [show (5449098358025390347/5450000000000000000 : ℝ)+(182648801447/218000000000000 : ℝ)*((484/3125 : ℝ)+(1391/12500 : ℝ))=(10000575602110493/10000000000000000 : ℝ) by norm_num, show 1+(1066216424638197/5000000000000000000 : ℝ)+(2382957695355173/50000000000000000000 : ℝ)=(50013045121941737143/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1066216424638197/5000000000000000000 : ℝ) ≤ ((5449098358025390347/5450000000000000000 : ℝ)+2*(182648801447/218000000000000 : ℝ)*(484/3125 : ℝ))^(4641/1024 : ℝ) := by
    rw [show (5449098358025390347/5450000000000000000 : ℝ)+2*(182648801447/218000000000000 : ℝ)*(484/3125 : ℝ)=(10000940899713387/10000000000000000 : ℝ) by norm_num, show 1+2*(1066216424638197/5000000000000000000 : ℝ)=(2501066216424638197/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5449098358025390347/5450000000000000000 : ℝ)*(X 1 0+X 2 0)+(182648801447/218000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4641/1024 : ℝ)) (lo := (1391/12500 : ℝ)) (hi := (484/3125 : ℝ)) (c := (5449098358025390347/5450000000000000000 : ℝ)) (alpha := (182648801447/218000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5449098358025390347/5450000000000000000 : ℝ)*(X 0 1+X 2 1)+(182648801447/218000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4641/1024 : ℝ)) (lo := (1391/12500 : ℝ)) (hi := (484/3125 : ℝ)) (c := (5449098358025390347/5450000000000000000 : ℝ)) (alpha := (182648801447/218000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5449098358025390347/5450000000000000000 : ℝ)*(X 0 2+X 1 2)+(182648801447/218000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4641/1024 : ℝ)) (lo := (1391/12500 : ℝ)) (hi := (484/3125 : ℝ)) (c := (5449098358025390347/5450000000000000000 : ℝ)) (alpha := (182648801447/218000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1781522161/10000000000 : ℝ)*X 0 0+(5425421203/10000000000 : ℝ)*X 0 1+(522015303/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348009517/10000000000 : ℝ)*X 1 0+(-1886527213/10000000000 : ℝ)*X 1 1+(1044030813/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267400477/500000000 : ℝ)*X 2 0+(5220154169/10000000000 : ℝ)*X 2 1+(-471631761/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2121093127/5000000000 : ℝ)*X 0 0+(1001257959/2500000000 : ℝ)*X 0 1+(4490563059/10000000000 : ℝ)*X 0 2+(2121093127/5000000000 : ℝ)*X 1 0+(1001257959/2500000000 : ℝ)*X 1 1+(4490563059/10000000000 : ℝ)*X 1 2+(2121093127/5000000000 : ℝ)*X 2 0+(1001257959/2500000000 : ℝ)*X 2 1+(4490563059/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-890774331/5000000000 : ℝ)*X 0 0+(2610612169/5000000000 : ℝ)*X 0 1+(5424342123/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1058736547/2000000000 : ℝ)*X 1 0+(-841169857/5000000000 : ℝ)*X 1 1+(5424342123/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1058736547/2000000000 : ℝ)*X 2 0+(2712171061/5000000000 : ℝ)*X 2 1+(-841169857/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4242248627/10000000000 : ℝ)*X 0 0+(4488033241/10000000000 : ℝ)*X 0 1+(4007581067/10000000000 : ℝ)*X 0 2+(4242248627/10000000000 : ℝ)*X 1 0+(4488033241/10000000000 : ℝ)*X 1 1+(4007581067/10000000000 : ℝ)*X 1 2+(4242248627/10000000000 : ℝ)*X 2 0+(4488033241/10000000000 : ℝ)*X 2 1+(4007581067/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3601448205945231776595717/1703125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (375041051/20000000000000 : ℝ)*(base19) + (109513563/6250000000000 : ℝ)*(base23) + (76979359/100000000000000 : ℝ)*(lower2) + (129774903/100000000000000 : ℝ)*(upper3) + (200271029/100000000000000 : ℝ)*(upper5) + (21660671326181/625000000000 : ℝ)*(major0) + (21660671326181/625000000000 : ℝ)*(major1) + (21660671326181/625000000000 : ℝ)*(major2) + (2435866798793071/50000000000000 : ℝ)*(sp0) + (19487175830379/400000000000 : ℝ)*(sp1) + (4871794080582997/100000000000000 : ℝ)*(sp2) + (64362794306209/3125000000000 : ℝ)*(sp3) + (7779401733/12500000000000 : ℝ)*(sp4) + (7424447/78125000000 : ℝ)*(sp7) + (2059618921090847/100000000000000 : ℝ)*(f.failure) + (974359166560001/20000000000000 : ℝ)*(f.sum) + (470374559683/272500000000000000000000000 : ℝ)*base65 + (31066212612693/3406250000000000000000000000000 : ℝ)*base68 + (35312296091425193/3406250000000000000000000000000 : ℝ)*base70 + (20951648203987693/3406250000000000000000000000000 : ℝ)*base72 + (74531866623/272500000000000000000000000 : ℝ)*base73 + (20253452927737693/3406250000000000000000000000000 : ℝ)*base76 + (15534209181324807/3406250000000000000000000000000 : ℝ)*base77 + (40778242031831443/3406250000000000000000000000000 : ℝ)*base80 + (139469455181/136250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (5272357/1250000000000000000000 : ℝ)*base90 + (5272357/1250000000000000000000 : ℝ)*base92 + (5272357/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (425026698089152491829282533/34062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6106487/312500000000 : ℝ)*(base19) + (529511729/25000000000000 : ℝ)*(base23) + (636907541/100000000000000 : ℝ)*(lower1) + (257210719/100000000000000 : ℝ)*(upper3) + (18586141/25000000000000 : ℝ)*(lower4) + (128730691/50000000000000 : ℝ)*(upper5) + (437786153861513/12500000000000 : ℝ)*(major0) + (437786153861513/12500000000000 : ℝ)*(major1) + (437786153861513/12500000000000 : ℝ)*(major2) + (2292886761/100000000000000 : ℝ)*(sp2) + (615402386021247/12500000000000 : ℝ)*(sp4) + (615402141761767/12500000000000 : ℝ)*(sp5) + (4923214677236299/100000000000000 : ℝ)*(sp6) + (2081358957685951/100000000000000 : ℝ)*(sp7) + (2081358957685951/100000000000000 : ℝ)*(f.failure) + (615402386021247/12500000000000 : ℝ)*(f.sum) + (17918376506003/2725000000000000000000000000 : ℝ)*base66 + (828415122569084989/68125000000000000000000000000000 : ℝ)*base68 + (148951066177834989/68125000000000000000000000000000 : ℝ)*base70 + (177692490832834989/68125000000000000000000000000000 : ℝ)*base72 + (7464766718453/2725000000000000000000000000 : ℝ)*base74 + (6012860375622165011/68125000000000000000000000000000 : ℝ)*base75 + (34041100960959989/68125000000000000000000000000000 : ℝ)*base78 + (1275280299499040011/68125000000000000000000000000000 : ℝ)*base79 + (2597825866953/2725000000000000000000000000 : ℝ)*base82 + (715781/1250000000000000000000 : ℝ)*base90 + (715781/1250000000000000000000 : ℝ)*base92 + (715781/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1573_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21033669/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (484/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1391/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11131/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1573_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1573_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21033669/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3951/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2709/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11131/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1573_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1573_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1573_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21033669/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3951/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2709/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11131/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1573_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

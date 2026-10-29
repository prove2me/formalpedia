-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1752_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:19:34.591602+00:00
-- url     : https://prove2.me/submissions/cfb3e8b1-8d91-4633-af60-0c63d68f9750

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
theorem support_rectangle_w1752_s0_0 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-583828137/5000000000 : ℝ)*x 0 + (2812116361/5000000000 : ℝ)*x 1 + (2490446757/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (583828137/5000000000 : ℝ)^5807 ≤ (7372843592551/100000000000000 : ℝ)^4783 := by
    have hnat : (583828137 : ℕ)^5807*100000000000000^4783 ≤ 7372843592551^4783*5000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      583828137 5000000000 7372843592551 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2812116361/5000000000 : ℝ)^5807 ≤ (49722612328533/100000000000000 : ℝ)^4783 := by
    have hnat : (2812116361 : ℕ)^5807*100000000000000^4783 ≤ 49722612328533^4783*5000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2812116361 5000000000 49722612328533 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2490446757/5000000000 : ℝ)^5807 ≤ (42904544067761/100000000000000 : ℝ)^4783 := by
    have hnat : (2490446757 : ℕ)^5807*100000000000000^4783 ≤ 42904544067761^4783*5000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2490446757 5000000000 42904544067761 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-583828137/5000000000 : ℝ), (2812116361/5000000000 : ℝ), (2490446757/5000000000 : ℝ)] ![(7372843592551/100000000000000 : ℝ), (49722612328533/100000000000000 : ℝ), (42904544067761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-583828137/5000000000 : ℝ)|^5807 ≤ (7372843592551/100000000000000 : ℝ)^4783
        have hw : |(-583828137/5000000000 : ℝ)|=(583828137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2812116361/5000000000 : ℝ)|^5807 ≤ (49722612328533/100000000000000 : ℝ)^4783
        have hw : |(2812116361/5000000000 : ℝ)|=(2812116361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2490446757/5000000000 : ℝ)|^5807 ≤ (42904544067761/100000000000000 : ℝ)^4783
        have hw : |(2490446757/5000000000 : ℝ)|=(2490446757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1752_s0_1 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5369471603/10000000000 : ℝ)*x 0 + (-378113527/2500000000 : ℝ)*x 1 + (996178801/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369471603/10000000000 : ℝ)^5807 ≤ (23500774463033/50000000000000 : ℝ)^4783 := by
    have hnat : (5369471603 : ℕ)^5807*50000000000000^4783 ≤ 23500774463033^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369471603 10000000000 23500774463033 50000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (378113527/2500000000 : ℝ)^5807 ≤ (5046950929291/50000000000000 : ℝ)^4783 := by
    have hnat : (378113527 : ℕ)^5807*50000000000000^4783 ≤ 5046950929291^4783*2500000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      378113527 2500000000 5046950929291 50000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (996178801/2000000000 : ℝ)^5807 ≤ (343236393621/800000000000 : ℝ)^4783 := by
    have hnat : (996178801 : ℕ)^5807*800000000000^4783 ≤ 343236393621^4783*2000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      996178801 2000000000 343236393621 800000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369471603/10000000000 : ℝ), (-378113527/2500000000 : ℝ), (996178801/2000000000 : ℝ)] ![(23500774463033/50000000000000 : ℝ), (5046950929291/50000000000000 : ℝ), (343236393621/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369471603/10000000000 : ℝ)|^5807 ≤ (23500774463033/50000000000000 : ℝ)^4783
        have hw : |(5369471603/10000000000 : ℝ)|=(5369471603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-378113527/2500000000 : ℝ)|^5807 ≤ (5046950929291/50000000000000 : ℝ)^4783
        have hw : |(-378113527/2500000000 : ℝ)|=(378113527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(996178801/2000000000 : ℝ)|^5807 ≤ (343236393621/800000000000 : ℝ)^4783
        have hw : |(996178801/2000000000 : ℝ)|=(996178801/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1752_s0_2 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5369473607/10000000000 : ℝ)*x 0 + (4980892873/10000000000 : ℝ)*x 1 + (-75622647/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369473607/10000000000 : ℝ)^5807 ≤ (47001570223623/100000000000000 : ℝ)^4783 := by
    have hnat : (5369473607 : ℕ)^5807*100000000000000^4783 ≤ 47001570223623^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369473607 10000000000 47001570223623 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4980892873/10000000000 : ℝ)^5807 ≤ (42904537364201/100000000000000 : ℝ)^4783 := by
    have hnat : (4980892873 : ℕ)^5807*100000000000000^4783 ≤ 42904537364201^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4980892873 10000000000 42904537364201 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (75622647/500000000 : ℝ)^5807 ≤ (10093892394661/100000000000000 : ℝ)^4783 := by
    have hnat : (75622647 : ℕ)^5807*100000000000000^4783 ≤ 10093892394661^4783*500000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75622647 500000000 10093892394661 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369473607/10000000000 : ℝ), (4980892873/10000000000 : ℝ), (-75622647/500000000 : ℝ)] ![(47001570223623/100000000000000 : ℝ), (42904537364201/100000000000000 : ℝ), (10093892394661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369473607/10000000000 : ℝ)|^5807 ≤ (47001570223623/100000000000000 : ℝ)^4783
        have hw : |(5369473607/10000000000 : ℝ)|=(5369473607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4980892873/10000000000 : ℝ)|^5807 ≤ (42904537364201/100000000000000 : ℝ)^4783
        have hw : |(4980892873/10000000000 : ℝ)|=(4980892873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-75622647/500000000 : ℝ)|^5807 ≤ (10093892394661/100000000000000 : ℝ)^4783
        have hw : |(-75622647/500000000 : ℝ)|=(75622647/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1752_s0_3 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1987298707/5000000000 : ℝ)*x 0 + (1492852797/5000000000 : ℝ)*x 1 + (5116711419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1987298707/5000000000 : ℝ)^5807 ≤ (32621594453973/100000000000000 : ℝ)^4783 := by
    have hnat : (1987298707 : ℕ)^5807*100000000000000^4783 ≤ 32621594453973^4783*5000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1987298707 5000000000 32621594453973 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1492852797/5000000000 : ℝ)^5807 ≤ (4609872983493/20000000000000 : ℝ)^4783 := by
    have hnat : (1492852797 : ℕ)^5807*20000000000000^4783 ≤ 4609872983493^4783*5000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1492852797 5000000000 4609872983493 20000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5116711419/10000000000 : ℝ)^5807 ≤ (44329040617677/100000000000000 : ℝ)^4783 := by
    have hnat : (5116711419 : ℕ)^5807*100000000000000^4783 ≤ 44329040617677^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5116711419 10000000000 44329040617677 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1987298707/5000000000 : ℝ), (1492852797/5000000000 : ℝ), (5116711419/10000000000 : ℝ)] ![(32621594453973/100000000000000 : ℝ), (4609872983493/20000000000000 : ℝ), (44329040617677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1987298707/5000000000 : ℝ)|^5807 ≤ (32621594453973/100000000000000 : ℝ)^4783
        have hw : |(1987298707/5000000000 : ℝ)|=(1987298707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1492852797/5000000000 : ℝ)|^5807 ≤ (4609872983493/20000000000000 : ℝ)^4783
        have hw : |(1492852797/5000000000 : ℝ)|=(1492852797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5116711419/10000000000 : ℝ)|^5807 ≤ (44329040617677/100000000000000 : ℝ)^4783
        have hw : |(5116711419/10000000000 : ℝ)|=(5116711419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1752_s0_4 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-292244761/2500000000 : ℝ)*x 0 + (999446139/2000000000 : ℝ)*x 1 + (5607359077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (292244761/2500000000 : ℝ)^5807 ≤ (7382985238193/100000000000000 : ℝ)^4783 := by
    have hnat : (292244761 : ℕ)^5807*100000000000000^4783 ≤ 7382985238193^4783*2500000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      292244761 2500000000 7382985238193 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (999446139/2000000000 : ℝ)^5807 ≤ (43075457787501/100000000000000 : ℝ)^4783 := by
    have hnat : (999446139 : ℕ)^5807*100000000000000^4783 ≤ 43075457787501^4783*2000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999446139 2000000000 43075457787501 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5607359077/10000000000 : ℝ)^5807 ≤ (9908311392601/20000000000000 : ℝ)^4783 := by
    have hnat : (5607359077 : ℕ)^5807*20000000000000^4783 ≤ 9908311392601^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5607359077 10000000000 9908311392601 20000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-292244761/2500000000 : ℝ), (999446139/2000000000 : ℝ), (5607359077/10000000000 : ℝ)] ![(7382985238193/100000000000000 : ℝ), (43075457787501/100000000000000 : ℝ), (9908311392601/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-292244761/2500000000 : ℝ)|^5807 ≤ (7382985238193/100000000000000 : ℝ)^4783
        have hw : |(-292244761/2500000000 : ℝ)|=(292244761/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(999446139/2000000000 : ℝ)|^5807 ≤ (43075457787501/100000000000000 : ℝ)^4783
        have hw : |(999446139/2000000000 : ℝ)|=(999446139/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5607359077/10000000000 : ℝ)|^5807 ≤ (9908311392601/20000000000000 : ℝ)^4783
        have hw : |(5607359077/10000000000 : ℝ)|=(5607359077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1752_s0_5 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5197966877/10000000000 : ℝ)*x 0 + (-44299377/500000000 : ℝ)*x 1 + (2803679581/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5197966877/10000000000 : ℝ)^5807 ≤ (4518516328427/10000000000000 : ℝ)^4783 := by
    have hnat : (5197966877 : ℕ)^5807*10000000000000^4783 ≤ 4518516328427^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5197966877 10000000000 4518516328427 10000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (44299377/500000000 : ℝ)^5807 ≤ (5273278822917/100000000000000 : ℝ)^4783 := by
    have hnat : (44299377 : ℕ)^5807*100000000000000^4783 ≤ 5273278822917^4783*500000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44299377 500000000 5273278822917 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2803679581/5000000000 : ℝ)^5807 ≤ (49541557874767/100000000000000 : ℝ)^4783 := by
    have hnat : (2803679581 : ℕ)^5807*100000000000000^4783 ≤ 49541557874767^4783*5000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2803679581 5000000000 49541557874767 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5197966877/10000000000 : ℝ), (-44299377/500000000 : ℝ), (2803679581/5000000000 : ℝ)] ![(4518516328427/10000000000000 : ℝ), (5273278822917/100000000000000 : ℝ), (49541557874767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5197966877/10000000000 : ℝ)|^5807 ≤ (4518516328427/10000000000000 : ℝ)^4783
        have hw : |(5197966877/10000000000 : ℝ)|=(5197966877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-44299377/500000000 : ℝ)|^5807 ≤ (5273278822917/100000000000000 : ℝ)^4783
        have hw : |(-44299377/500000000 : ℝ)|=(44299377/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2803679581/5000000000 : ℝ)|^5807 ≤ (49541557874767/100000000000000 : ℝ)^4783
        have hw : |(2803679581/5000000000 : ℝ)|=(2803679581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1752_s0_6 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (649745803/1250000000 : ℝ)*x 0 + (1121471839/2000000000 : ℝ)*x 1 + (-442994077/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (649745803/1250000000 : ℝ)^5807 ≤ (9037031700669/20000000000000 : ℝ)^4783 := by
    have hnat : (649745803 : ℕ)^5807*20000000000000^4783 ≤ 9037031700669^4783*1250000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649745803 1250000000 9037031700669 20000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1121471839/2000000000 : ℝ)^5807 ≤ (24770779114373/50000000000000 : ℝ)^4783 := by
    have hnat : (1121471839 : ℕ)^5807*50000000000000^4783 ≤ 24770779114373^4783*2000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121471839 2000000000 24770779114373 50000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (442994077/5000000000 : ℝ)^5807 ≤ (5273283259749/100000000000000 : ℝ)^4783 := by
    have hnat : (442994077 : ℕ)^5807*100000000000000^4783 ≤ 5273283259749^4783*5000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442994077 5000000000 5273283259749 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(649745803/1250000000 : ℝ), (1121471839/2000000000 : ℝ), (-442994077/5000000000 : ℝ)] ![(9037031700669/20000000000000 : ℝ), (24770779114373/50000000000000 : ℝ), (5273283259749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(649745803/1250000000 : ℝ)|^5807 ≤ (9037031700669/20000000000000 : ℝ)^4783
        have hw : |(649745803/1250000000 : ℝ)|=(649745803/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1121471839/2000000000 : ℝ)|^5807 ≤ (24770779114373/50000000000000 : ℝ)^4783
        have hw : |(1121471839/2000000000 : ℝ)|=(1121471839/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-442994077/5000000000 : ℝ)|^5807 ≤ (5273283259749/100000000000000 : ℝ)^4783
        have hw : |(-442994077/5000000000 : ℝ)|=(442994077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1752_s0_7 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1989489893/5000000000 : ℝ)*x 0 + (1265648567/2500000000 : ℝ)*x 1 + (760399461/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1989489893/5000000000 : ℝ)^5807 ≤ (32665268554071/100000000000000 : ℝ)^4783 := by
    have hnat : (1989489893 : ℕ)^5807*100000000000000^4783 ≤ 32665268554071^4783*5000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989489893 5000000000 32665268554071 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1265648567/2500000000 : ℝ)^5807 ≤ (21880231059379/50000000000000 : ℝ)^4783 := by
    have hnat : (1265648567 : ℕ)^5807*50000000000000^4783 ≤ 21880231059379^4783*2500000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1265648567 2500000000 21880231059379 50000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (760399461/2500000000 : ℝ)^5807 ≤ (942970772253/4000000000000 : ℝ)^4783 := by
    have hnat : (760399461 : ℕ)^5807*4000000000000^4783 ≤ 942970772253^4783*2500000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      760399461 2500000000 942970772253 4000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1989489893/5000000000 : ℝ), (1265648567/2500000000 : ℝ), (760399461/2500000000 : ℝ)] ![(32665268554071/100000000000000 : ℝ), (21880231059379/50000000000000 : ℝ), (942970772253/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1989489893/5000000000 : ℝ)|^5807 ≤ (32665268554071/100000000000000 : ℝ)^4783
        have hw : |(1989489893/5000000000 : ℝ)|=(1989489893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1265648567/2500000000 : ℝ)|^5807 ≤ (21880231059379/50000000000000 : ℝ)^4783
        have hw : |(1265648567/2500000000 : ℝ)|=(1265648567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(760399461/2500000000 : ℝ)|^5807 ≤ (942970772253/4000000000000 : ℝ)^4783
        have hw : |(760399461/2500000000 : ℝ)|=(760399461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1752_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (215620517/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1361/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10359/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (5791/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5791 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5791*1^1024 ≤ 0^1024*1^5791 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5791 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5791 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5791/1024 : ℝ) ≤ (280873291417137421/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5791 ≤ (280873291417137421/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5791*50000000000000000000^1024 ≤ 280873291417137421^1024*5^5791 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 280873291417137421 50000000000000000000 5791 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (280873291417137421/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5791 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5791/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5791 := by
      have hnat : (1 : ℕ)^1024*1^5791 ≤ 1^5791*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5791 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5791 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50280873291417137421/50000000000000000000 : ℝ) ≤ (5004955129092301/5000000000000000 : ℝ) ^ (5791/1024 : ℝ) := by
    have hpowers : (50280873291417137421/50000000000000000000 : ℝ)^1024 ≤ (5004955129092301/5000000000000000 : ℝ)^5791 := by
      have hnat : (50280873291417137421 : ℕ)^1024*5000000000000000^5791 ≤ 5004955129092301^5791*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50280873291417137421 50000000000000000000 5004955129092301 5000000000000000 1024 5791 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004955129092301/5000000000000000 : ℝ)) (X := (50280873291417137421/50000000000000000000 : ℝ)) (by norm_num) 5791 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25280873291417137421/25000000000000000000 : ℝ) ≤ (2504955129092301/2500000000000000 : ℝ) ^ (5791/1024 : ℝ) := by
    have hpowers : (25280873291417137421/25000000000000000000 : ℝ)^1024 ≤ (2504955129092301/2500000000000000 : ℝ)^5791 := by
      have hnat : (25280873291417137421 : ℕ)^1024*2500000000000000^5791 ≤ 2504955129092301^5791*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25280873291417137421 25000000000000000000 2504955129092301 2500000000000000 1024 5791 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2504955129092301/2500000000000000 : ℝ)) (X := (25280873291417137421/25000000000000000000 : ℝ)) (by norm_num) 5791 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(4955129092301/2000000000000000 : ℝ)*(0 : ℝ))^(5791/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(4955129092301/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(280873291417137421/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(4955129092301/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5791/1024 : ℝ) := by
    rw [show (1 : ℝ)+(4955129092301/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5004955129092301/5000000000000000 : ℝ) by norm_num, show 1+(280873291417137421/50000000000000000000 : ℝ)+(0 : ℝ)=(50280873291417137421/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(280873291417137421/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(4955129092301/2000000000000000 : ℝ)*(2/5 : ℝ))^(5791/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(4955129092301/2000000000000000 : ℝ)*(2/5 : ℝ)=(2504955129092301/2500000000000000 : ℝ) by norm_num, show 1+2*(280873291417137421/50000000000000000000 : ℝ)=(25280873291417137421/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(4955129092301/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5791/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4955129092301/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(4955129092301/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5791/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4955129092301/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(4955129092301/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5791/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4955129092301/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-583828137/5000000000 : ℝ)*X 0 0+(2812116361/5000000000 : ℝ)*X 0 1+(2490446757/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5369471603/10000000000 : ℝ)*X 1 0+(-378113527/2500000000 : ℝ)*X 1 1+(996178801/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5369473607/10000000000 : ℝ)*X 2 0+(4980892873/10000000000 : ℝ)*X 2 1+(-75622647/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1987298707/5000000000 : ℝ)*X 0 0+(1492852797/5000000000 : ℝ)*X 0 1+(5116711419/10000000000 : ℝ)*X 0 2+(1987298707/5000000000 : ℝ)*X 1 0+(1492852797/5000000000 : ℝ)*X 1 1+(5116711419/10000000000 : ℝ)*X 1 2+(1987298707/5000000000 : ℝ)*X 2 0+(1492852797/5000000000 : ℝ)*X 2 1+(5116711419/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-292244761/2500000000 : ℝ)*X 0 0+(999446139/2000000000 : ℝ)*X 0 1+(5607359077/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5197966877/10000000000 : ℝ)*X 1 0+(-44299377/500000000 : ℝ)*X 1 1+(2803679581/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((649745803/1250000000 : ℝ)*X 2 0+(1121471839/2000000000 : ℝ)*X 2 1+(-442994077/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1989489893/5000000000 : ℝ)*X 0 0+(1265648567/2500000000 : ℝ)*X 0 1+(760399461/2500000000 : ℝ)*X 0 2+(1989489893/5000000000 : ℝ)*X 1 0+(1265648567/2500000000 : ℝ)*X 1 1+(760399461/2500000000 : ℝ)*X 1 2+(1989489893/5000000000 : ℝ)*X 2 0+(1265648567/2500000000 : ℝ)*X 2 1+(760399461/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (376194391366882813317/160000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18463433/5000000000000 : ℝ)*(base19) + (336866821/50000000000000 : ℝ)*(base23) + (14150809/12500000000000 : ℝ)*(base24) + (87233019/100000000000000 : ℝ)*(upper4) + (144801169/100000000000000 : ℝ)*(upper5) + (1618926884979/160000000000 : ℝ)*(major0) + (1618926884979/160000000000 : ℝ)*(major1) + (1618926884979/160000000000 : ℝ)*(major2) + (388597606294441/25000000000000 : ℝ)*(sp0) + (3035926235713/195312500000 : ℝ)*(sp1) + (1554393815013601/100000000000000 : ℝ)*(sp2) + (234631478036073/50000000000000 : ℝ)*(sp3) + (261048497/6250000000000 : ℝ)*(sp4) + (19396481/2000000000000 : ℝ)*(sp7) + (117315981474049/25000000000000 : ℝ)*(f.failure) + (388598650488429/25000000000000 : ℝ)*(f.sum) + (313441356521/160000000000000000000000000 : ℝ)*base66 + (1284273072361/320000000000000000000000000 : ℝ)*base68 + (1625694286999/320000000000000000000000000 : ℝ)*base69 + (269653922839/320000000000000000000000000 : ℝ)*base71 + (844045765481/160000000000000000000000000 : ℝ)*base74 + (2766062197399/320000000000000000000000000 : ℝ)*base75 + (819713430359/320000000000000000000000000 : ℝ)*base77 + (2174566791639/320000000000000000000000000 : ℝ)*base79 + (705169982761/160000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (7536667/2500000000000000000000 : ℝ)*base90 + (7536667/2500000000000000000000 : ℝ)*base92 + (7536667/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (317246196653482961164923/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1535274281/100000000000000 : ℝ)*(base19) + (1422608971/100000000000000 : ℝ)*(base23) + (36447067/100000000000000 : ℝ)*(upper2) + (66057477/25000000000000 : ℝ)*(upper3) + (234934291/100000000000000 : ℝ)*(upper5) + (1066901963032447/100000000000000 : ℝ)*(major0) + (1066901963032447/100000000000000 : ℝ)*(major1) + (1066901963032447/100000000000000 : ℝ)*(major2) + (338480459/5000000000000 : ℝ)*(sp1) + (694857443/12500000000000 : ℝ)*(sp2) + (1638998313914179/100000000000000 : ℝ)*(sp4) + (819495004515359/50000000000000 : ℝ)*(sp5) + (1638991332445663/100000000000000 : ℝ)*(sp6) + (98961080130649/20000000000000 : ℝ)*(sp7) + (98961080130649/20000000000000 : ℝ)*(f.failure) + (1638998313914179/100000000000000 : ℝ)*(f.sum) + (294323548509453/100000000000000000000000000000 : ℝ)*base66 + (1373264292109453/200000000000000000000000000000 : ℝ)*base68 + (715490791709453/200000000000000000000000000000 : ℝ)*base70 + (1177429238309453/200000000000000000000000000000 : ℝ)*base72 + (288022929109453/100000000000000000000000000000 : ℝ)*base74 + (1346901078309453/200000000000000000000000000000 : ℝ)*base76 + (407195457109453/200000000000000000000000000000 : ℝ)*base78 + (190069650509453/200000000000000000000000000000 : ℝ)*base80 + (130546310909453/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (24925533/2000000000000000000000 : ℝ)*base89 + (24925533/2000000000000000000000 : ℝ)*base91 + (24925533/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1752_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (215620517/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1361/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10359/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1752_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1752_s1_0 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-605073717/5000000000 : ℝ)*x 0 + (1374345697/2500000000 : ℝ)*x 1 + (1015858961/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (605073717/5000000000 : ℝ)^5807 ≤ (96247997307/1250000000000 : ℝ)^4783 := by
    have hnat : (605073717 : ℕ)^5807*1250000000000^4783 ≤ 96247997307^4783*5000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      605073717 5000000000 96247997307 1250000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1374345697/2500000000 : ℝ)^5807 ≤ (4836437308581/10000000000000 : ℝ)^4783 := by
    have hnat : (1374345697 : ℕ)^5807*10000000000000^4783 ≤ 4836437308581^4783*2500000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1374345697 2500000000 4836437308581 10000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1015858961/2000000000 : ℝ)^5807 ≤ (10983946780737/25000000000000 : ℝ)^4783 := by
    have hnat : (1015858961 : ℕ)^5807*25000000000000^4783 ≤ 10983946780737^4783*2000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015858961 2000000000 10983946780737 25000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-605073717/5000000000 : ℝ), (1374345697/2500000000 : ℝ), (1015858961/2000000000 : ℝ)] ![(96247997307/1250000000000 : ℝ), (4836437308581/10000000000000 : ℝ), (10983946780737/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-605073717/5000000000 : ℝ)|^5807 ≤ (96247997307/1250000000000 : ℝ)^4783
        have hw : |(-605073717/5000000000 : ℝ)|=(605073717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1374345697/2500000000 : ℝ)|^5807 ≤ (4836437308581/10000000000000 : ℝ)^4783
        have hw : |(1374345697/2500000000 : ℝ)|=(1374345697/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1015858961/2000000000 : ℝ)|^5807 ≤ (10983946780737/25000000000000 : ℝ)^4783
        have hw : |(1015858961/2000000000 : ℝ)|=(1015858961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1752_s1_1 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (533573227/1000000000 : ℝ)*x 0 + (-142890417/1000000000 : ℝ)*x 1 + (2539647463/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (533573227/1000000000 : ℝ)^5807 ≤ (46643224957841/100000000000000 : ℝ)^4783 := by
    have hnat : (533573227 : ℕ)^5807*100000000000000^4783 ≤ 46643224957841^4783*1000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533573227 1000000000 46643224957841 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (142890417/1000000000 : ℝ)^5807 ≤ (9420986637509/100000000000000 : ℝ)^4783 := by
    have hnat : (142890417 : ℕ)^5807*100000000000000^4783 ≤ 9420986637509^4783*1000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142890417 1000000000 9420986637509 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2539647463/5000000000 : ℝ)^5807 ≤ (21967894196837/50000000000000 : ℝ)^4783 := by
    have hnat : (2539647463 : ℕ)^5807*50000000000000^4783 ≤ 21967894196837^4783*5000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2539647463 5000000000 21967894196837 50000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(533573227/1000000000 : ℝ), (-142890417/1000000000 : ℝ), (2539647463/5000000000 : ℝ)] ![(46643224957841/100000000000000 : ℝ), (9420986637509/100000000000000 : ℝ), (21967894196837/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(533573227/1000000000 : ℝ)|^5807 ≤ (46643224957841/100000000000000 : ℝ)^4783
        have hw : |(533573227/1000000000 : ℝ)|=(533573227/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-142890417/1000000000 : ℝ)|^5807 ≤ (9420986637509/100000000000000 : ℝ)^4783
        have hw : |(-142890417/1000000000 : ℝ)|=(142890417/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2539647463/5000000000 : ℝ)|^5807 ≤ (21967894196837/50000000000000 : ℝ)^4783
        have hw : |(2539647463/5000000000 : ℝ)|=(2539647463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1752_s1_2 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1333933207/2500000000 : ℝ)*x 0 + (1015858873/2000000000 : ℝ)*x 1 + (-714452083/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1333933207/2500000000 : ℝ)^5807 ≤ (23321615440001/50000000000000 : ℝ)^4783 := by
    have hnat : (1333933207 : ℕ)^5807*50000000000000^4783 ≤ 23321615440001^4783*2500000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1333933207 2500000000 23321615440001 50000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1015858873/2000000000 : ℝ)^5807 ≤ (2745986406383/6250000000000 : ℝ)^4783 := by
    have hnat : (1015858873 : ℕ)^5807*6250000000000^4783 ≤ 2745986406383^4783*2000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015858873 2000000000 2745986406383 6250000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (714452083/5000000000 : ℝ)^5807 ≤ (9420986605491/100000000000000 : ℝ)^4783 := by
    have hnat : (714452083 : ℕ)^5807*100000000000000^4783 ≤ 9420986605491^4783*5000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      714452083 5000000000 9420986605491 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1333933207/2500000000 : ℝ), (1015858873/2000000000 : ℝ), (-714452083/5000000000 : ℝ)] ![(23321615440001/50000000000000 : ℝ), (2745986406383/6250000000000 : ℝ), (9420986605491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1333933207/2500000000 : ℝ)|^5807 ≤ (23321615440001/50000000000000 : ℝ)^4783
        have hw : |(1333933207/2500000000 : ℝ)|=(1333933207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1015858873/2000000000 : ℝ)|^5807 ≤ (2745986406383/6250000000000 : ℝ)^4783
        have hw : |(1015858873/2000000000 : ℝ)|=(1015858873/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-714452083/5000000000 : ℝ)|^5807 ≤ (9420986605491/100000000000000 : ℝ)^4783
        have hw : |(-714452083/5000000000 : ℝ)|=(714452083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1752_s1_3 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2007974433/5000000000 : ℝ)*x 0 + (3355680183/10000000000 : ℝ)*x 1 + (948112089/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2007974433/5000000000 : ℝ)^5807 ≤ (33034106220069/100000000000000 : ℝ)^4783 := by
    have hnat : (2007974433 : ℕ)^5807*100000000000000^4783 ≤ 33034106220069^4783*5000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2007974433 5000000000 33034106220069 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3355680183/10000000000 : ℝ)^5807 ≤ (13280798322971/50000000000000 : ℝ)^4783 := by
    have hnat : (3355680183 : ℕ)^5807*50000000000000^4783 ≤ 13280798322971^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3355680183 10000000000 13280798322971 50000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (948112089/2000000000 : ℝ)^5807 ≤ (40404297120933/100000000000000 : ℝ)^4783 := by
    have hnat : (948112089 : ℕ)^5807*100000000000000^4783 ≤ 40404297120933^4783*2000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      948112089 2000000000 40404297120933 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2007974433/5000000000 : ℝ), (3355680183/10000000000 : ℝ), (948112089/2000000000 : ℝ)] ![(33034106220069/100000000000000 : ℝ), (13280798322971/50000000000000 : ℝ), (40404297120933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2007974433/5000000000 : ℝ)|^5807 ≤ (33034106220069/100000000000000 : ℝ)^4783
        have hw : |(2007974433/5000000000 : ℝ)|=(2007974433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3355680183/10000000000 : ℝ)|^5807 ≤ (13280798322971/50000000000000 : ℝ)^4783
        have hw : |(3355680183/10000000000 : ℝ)|=(3355680183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(948112089/2000000000 : ℝ)|^5807 ≤ (40404297120933/100000000000000 : ℝ)^4783
        have hw : |(948112089/2000000000 : ℝ)|=(948112089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1752_s1_4 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1210508527/10000000000 : ℝ)*x 0 + (254310323/500000000 : ℝ)*x 1 + (5490324073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1210508527/10000000000 : ℝ)^5807 ≤ (1540525858741/20000000000000 : ℝ)^4783 := by
    have hnat : (1210508527 : ℕ)^5807*20000000000000^4783 ≤ 1540525858741^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1210508527 10000000000 1540525858741 20000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (254310323/500000000 : ℝ)^5807 ≤ (1760335318429/4000000000000 : ℝ)^4783 := by
    have hnat : (254310323 : ℕ)^5807*4000000000000^4783 ≤ 1760335318429^4783*500000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254310323 500000000 1760335318429 4000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5490324073/10000000000 : ℝ)^5807 ≤ (482889877351/1000000000000 : ℝ)^4783 := by
    have hnat : (5490324073 : ℕ)^5807*1000000000000^4783 ≤ 482889877351^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490324073 10000000000 482889877351 1000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1210508527/10000000000 : ℝ), (254310323/500000000 : ℝ), (5490324073/10000000000 : ℝ)] ![(1540525858741/20000000000000 : ℝ), (1760335318429/4000000000000 : ℝ), (482889877351/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1210508527/10000000000 : ℝ)|^5807 ≤ (1540525858741/20000000000000 : ℝ)^4783
        have hw : |(-1210508527/10000000000 : ℝ)|=(1210508527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(254310323/500000000 : ℝ)|^5807 ≤ (1760335318429/4000000000000 : ℝ)^4783
        have hw : |(254310323/500000000 : ℝ)|=(254310323/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5490324073/10000000000 : ℝ)|^5807 ≤ (482889877351/1000000000000 : ℝ)^4783
        have hw : |(5490324073/10000000000 : ℝ)|=(5490324073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1752_s1_5 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5224947263/10000000000 : ℝ)*x 0 + (-1017874977/10000000000 : ℝ)*x 1 + (5490324043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5224947263/10000000000 : ℝ)^5807 ≤ (45470070116631/100000000000000 : ℝ)^4783 := by
    have hnat : (5224947263 : ℕ)^5807*100000000000000^4783 ≤ 45470070116631^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224947263 10000000000 45470070116631 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1017874977/10000000000 : ℝ)^5807 ≤ (6240942452761/100000000000000 : ℝ)^4783 := by
    have hnat : (1017874977 : ℕ)^5807*100000000000000^4783 ≤ 6240942452761^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1017874977 10000000000 6240942452761 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5490324043/10000000000 : ℝ)^5807 ≤ (48288987414751/100000000000000 : ℝ)^4783 := by
    have hnat : (5490324043 : ℕ)^5807*100000000000000^4783 ≤ 48288987414751^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490324043 10000000000 48288987414751 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5224947263/10000000000 : ℝ), (-1017874977/10000000000 : ℝ), (5490324043/10000000000 : ℝ)] ![(45470070116631/100000000000000 : ℝ), (6240942452761/100000000000000 : ℝ), (48288987414751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5224947263/10000000000 : ℝ)|^5807 ≤ (45470070116631/100000000000000 : ℝ)^4783
        have hw : |(5224947263/10000000000 : ℝ)|=(5224947263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1017874977/10000000000 : ℝ)|^5807 ≤ (6240942452761/100000000000000 : ℝ)^4783
        have hw : |(-1017874977/10000000000 : ℝ)|=(1017874977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5490324043/10000000000 : ℝ)|^5807 ≤ (48288987414751/100000000000000 : ℝ)^4783
        have hw : |(5490324043/10000000000 : ℝ)|=(5490324043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1752_s1_6 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2612473593/5000000000 : ℝ)*x 0 + (5490323987/10000000000 : ℝ)*x 1 + (-508937583/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2612473593/5000000000 : ℝ)^5807 ≤ (22735034651539/50000000000000 : ℝ)^4783 := by
    have hnat : (2612473593 : ℕ)^5807*50000000000000^4783 ≤ 22735034651539^4783*5000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612473593 5000000000 22735034651539 50000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5490323987/10000000000 : ℝ)^5807 ≤ (48288986816767/100000000000000 : ℝ)^4783 := by
    have hnat : (5490323987 : ℕ)^5807*100000000000000^4783 ≤ 48288986816767^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490323987 10000000000 48288986816767 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (508937583/5000000000 : ℝ)^5807 ≤ (39005899123/625000000000 : ℝ)^4783 := by
    have hnat : (508937583 : ℕ)^5807*625000000000^4783 ≤ 39005899123^4783*5000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508937583 5000000000 39005899123 625000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2612473593/5000000000 : ℝ), (5490323987/10000000000 : ℝ), (-508937583/5000000000 : ℝ)] ![(22735034651539/50000000000000 : ℝ), (48288986816767/100000000000000 : ℝ), (39005899123/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2612473593/5000000000 : ℝ)|^5807 ≤ (22735034651539/50000000000000 : ℝ)^4783
        have hw : |(2612473593/5000000000 : ℝ)|=(2612473593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5490323987/10000000000 : ℝ)|^5807 ≤ (48288986816767/100000000000000 : ℝ)^4783
        have hw : |(5490323987/10000000000 : ℝ)|=(5490323987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-508937583/5000000000 : ℝ)|^5807 ≤ (39005899123/625000000000 : ℝ)^4783
        have hw : |(-508937583/5000000000 : ℝ)|=(508937583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1752_s1_7 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2008571497/5000000000 : ℝ)*x 0 + (4717664181/10000000000 : ℝ)*x 1 + (3379063113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2008571497/5000000000 : ℝ)^5807 ≤ (3304603210283/10000000000000 : ℝ)^4783 := by
    have hnat : (2008571497 : ℕ)^5807*10000000000000^4783 ≤ 3304603210283^4783*5000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008571497 5000000000 3304603210283 10000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4717664181/10000000000 : ℝ)^5807 ≤ (10041873277187/25000000000000 : ℝ)^4783 := by
    have hnat : (4717664181 : ℕ)^5807*25000000000000^4783 ≤ 10041873277187^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4717664181 10000000000 10041873277187 25000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3379063113/10000000000 : ℝ)^5807 ≤ (26786474777811/100000000000000 : ℝ)^4783 := by
    have hnat : (3379063113 : ℕ)^5807*100000000000000^4783 ≤ 26786474777811^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3379063113 10000000000 26786474777811 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2008571497/5000000000 : ℝ), (4717664181/10000000000 : ℝ), (3379063113/10000000000 : ℝ)] ![(3304603210283/10000000000000 : ℝ), (10041873277187/25000000000000 : ℝ), (26786474777811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2008571497/5000000000 : ℝ)|^5807 ≤ (3304603210283/10000000000000 : ℝ)^4783
        have hw : |(2008571497/5000000000 : ℝ)|=(2008571497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4717664181/10000000000 : ℝ)|^5807 ≤ (10041873277187/25000000000000 : ℝ)^4783
        have hw : |(4717664181/10000000000 : ℝ)|=(4717664181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3379063113/10000000000 : ℝ)|^5807 ≤ (26786474777811/100000000000000 : ℝ)^4783
        have hw : |(3379063113/10000000000 : ℝ)|=(3379063113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1752_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (215620517/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10359/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1361/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2253/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18001/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10359/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1361/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10359/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1361/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10359/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1361/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10359/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1361/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10359/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1361/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10359/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1361/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1361/20000 : ℝ) ^ (5791/1024 : ℝ) ≤ (12539895816571/50000000000000000000 : ℝ) := by
    have hpowers : (1361/20000 : ℝ)^5791 ≤ (12539895816571/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1361 : ℕ)^5791*50000000000000000000^1024 ≤ 12539895816571^1024*20000^5791 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1361 20000 12539895816571 50000000000000000000 5791 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1361/20000 : ℝ)) (X := (12539895816571/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5791 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (10359/50000 : ℝ) ^ (5791/1024 : ℝ) ≤ (13606926389176781/100000000000000000000 : ℝ) := by
    have hpowers : (10359/50000 : ℝ)^5791 ≤ (13606926389176781/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10359 : ℕ)^5791*100000000000000000000^1024 ≤ 13606926389176781^1024*50000^5791 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10359 50000 13606926389176781 100000000000000000000 5791 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10359/50000 : ℝ)) (X := (13606926389176781/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5791 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000012539895816571/25000000000000000000 : ℝ) ≤ (5000000443476107/5000000000000000 : ℝ) ^ (5791/1024 : ℝ) := by
    have hpowers : (25000012539895816571/25000000000000000000 : ℝ)^1024 ≤ (5000000443476107/5000000000000000 : ℝ)^5791 := by
      have hnat : (25000012539895816571 : ℕ)^1024*5000000000000000^5791 ≤ 5000000443476107^5791*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000012539895816571 25000000000000000000 5000000443476107 5000000000000000 1024 5791 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000443476107/5000000000000000 : ℝ)) (X := (25000012539895816571/25000000000000000000 : ℝ)) (by norm_num) 5791 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100013632006180809923/100000000000000000000 : ℝ) ≤ (10000241035938161/10000000000000000 : ℝ) ^ (5791/1024 : ℝ) := by
    have hpowers : (100013632006180809923/100000000000000000000 : ℝ)^1024 ≤ (10000241035938161/10000000000000000 : ℝ)^5791 := by
      have hnat : (100013632006180809923 : ℕ)^1024*10000000000000000^5791 ≤ 10000241035938161^5791*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100013632006180809923 100000000000000000000 10000241035938161 10000000000000000 1024 5791 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000241035938161/10000000000000000 : ℝ)) (X := (100013632006180809923/100000000000000000000 : ℝ)) (by norm_num) 5791 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50013606926389176781/50000000000000000000 : ℝ) ≤ (2500120296231027/2500000000000000 : ℝ) ^ (5791/1024 : ℝ) := by
    have hpowers : (50013606926389176781/50000000000000000000 : ℝ)^1024 ≤ (2500120296231027/2500000000000000 : ℝ)^5791 := by
      have hnat : (50013606926389176781 : ℕ)^1024*2500000000000000^5791 ≤ 2500120296231027^5791*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013606926389176781 50000000000000000000 2500120296231027 2500000000000000 1024 5791 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500120296231027/2500000000000000 : ℝ)) (X := (50013606926389176781/50000000000000000000 : ℝ)) (by norm_num) 5791 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(12539895816571/50000000000000000000 : ℝ) ≤ ((17390842989058426839/17391250000000000000 : ℝ)+2*(240148985947/1391300000000000 : ℝ)*(1361/20000 : ℝ))^(5791/1024 : ℝ) := by
    rw [show (17390842989058426839/17391250000000000000 : ℝ)+2*(240148985947/1391300000000000 : ℝ)*(1361/20000 : ℝ)=(5000000443476107/5000000000000000 : ℝ) by norm_num, show 1+2*(12539895816571/50000000000000000000 : ℝ)=(25000012539895816571/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13606926389176781/100000000000000000000 : ℝ)+(12539895816571/50000000000000000000 : ℝ) ≤ ((17390842989058426839/17391250000000000000 : ℝ)+(240148985947/1391300000000000 : ℝ)*((10359/50000 : ℝ)+(1361/20000 : ℝ)))^(5791/1024 : ℝ) := by
    rw [show (17390842989058426839/17391250000000000000 : ℝ)+(240148985947/1391300000000000 : ℝ)*((10359/50000 : ℝ)+(1361/20000 : ℝ))=(10000241035938161/10000000000000000 : ℝ) by norm_num, show 1+(13606926389176781/100000000000000000000 : ℝ)+(12539895816571/50000000000000000000 : ℝ)=(100013632006180809923/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13606926389176781/100000000000000000000 : ℝ) ≤ ((17390842989058426839/17391250000000000000 : ℝ)+2*(240148985947/1391300000000000 : ℝ)*(10359/50000 : ℝ))^(5791/1024 : ℝ) := by
    rw [show (17390842989058426839/17391250000000000000 : ℝ)+2*(240148985947/1391300000000000 : ℝ)*(10359/50000 : ℝ)=(2500120296231027/2500000000000000 : ℝ) by norm_num, show 1+2*(13606926389176781/100000000000000000000 : ℝ)=(50013606926389176781/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17390842989058426839/17391250000000000000 : ℝ)*(X 1 0+X 2 0)+(240148985947/1391300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5791/1024 : ℝ)) (lo := (1361/20000 : ℝ)) (hi := (10359/50000 : ℝ)) (c := (17390842989058426839/17391250000000000000 : ℝ)) (alpha := (240148985947/1391300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17390842989058426839/17391250000000000000 : ℝ)*(X 0 1+X 2 1)+(240148985947/1391300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5791/1024 : ℝ)) (lo := (1361/20000 : ℝ)) (hi := (10359/50000 : ℝ)) (c := (17390842989058426839/17391250000000000000 : ℝ)) (alpha := (240148985947/1391300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17390842989058426839/17391250000000000000 : ℝ)*(X 0 2+X 1 2)+(240148985947/1391300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5791/1024 : ℝ)) (lo := (1361/20000 : ℝ)) (hi := (10359/50000 : ℝ)) (c := (17390842989058426839/17391250000000000000 : ℝ)) (alpha := (240148985947/1391300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-605073717/5000000000 : ℝ)*X 0 0+(1374345697/2500000000 : ℝ)*X 0 1+(1015858961/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((533573227/1000000000 : ℝ)*X 1 0+(-142890417/1000000000 : ℝ)*X 1 1+(2539647463/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1333933207/2500000000 : ℝ)*X 2 0+(1015858873/2000000000 : ℝ)*X 2 1+(-714452083/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2007974433/5000000000 : ℝ)*X 0 0+(3355680183/10000000000 : ℝ)*X 0 1+(948112089/2000000000 : ℝ)*X 0 2+(2007974433/5000000000 : ℝ)*X 1 0+(3355680183/10000000000 : ℝ)*X 1 1+(948112089/2000000000 : ℝ)*X 1 2+(2007974433/5000000000 : ℝ)*X 2 0+(3355680183/10000000000 : ℝ)*X 2 1+(948112089/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1210508527/10000000000 : ℝ)*X 0 0+(254310323/500000000 : ℝ)*X 0 1+(5490324073/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5224947263/10000000000 : ℝ)*X 1 0+(-1017874977/10000000000 : ℝ)*X 1 1+(5490324043/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2612473593/5000000000 : ℝ)*X 2 0+(5490323987/10000000000 : ℝ)*X 2 1+(-508937583/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2008571497/5000000000 : ℝ)*X 0 0+(4717664181/10000000000 : ℝ)*X 0 1+(3379063113/10000000000 : ℝ)*X 0 2+(2008571497/5000000000 : ℝ)*X 1 0+(4717664181/10000000000 : ℝ)*X 1 1+(3379063113/10000000000 : ℝ)*X 1 2+(2008571497/5000000000 : ℝ)*X 2 0+(4717664181/10000000000 : ℝ)*X 2 1+(3379063113/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (261897426242308674300993/34782500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1153298397/100000000000000 : ℝ)*(base19) + (643162621/50000000000000 : ℝ)*(base23) + (15621513/25000000000000 : ℝ)*(lower2) + (115904567/50000000000000 : ℝ)*(upper3) + (87835519/50000000000000 : ℝ)*(upper5) + (389243558069393/25000000000000 : ℝ)*(major0) + (389243558069393/25000000000000 : ℝ)*(major1) + (389243558069393/25000000000000 : ℝ)*(major2) + (149490582701181/6250000000000 : ℝ)*(sp0) + (1195928520611259/50000000000000 : ℝ)*(sp1) + (298982113524459/12500000000000 : ℝ)*(sp2) + (361043361670361/50000000000000 : ℝ)*(sp3) + (8871302019/100000000000000 : ℝ)*(sp4) + (823926921/25000000000000 : ℝ)*(sp7) + (361045009524203/50000000000000 : ℝ)*(f.failure) + (478371638904183/20000000000000 : ℝ)*(f.sum) + (184926349841431/69565000000000000000000000000 : ℝ)*base66 + (2225728601063911273/434781250000000000000000000000000 : ℝ)*base68 + (795931560932755023/434781250000000000000000000000000 : ℝ)*base70 + (44977655130776227/434781250000000000000000000000000 : ℝ)*base71 + (101642993155433/34782500000000000000000000000 : ℝ)*base74 + (976150563398786273/434781250000000000000000000000000 : ℝ)*base76 + (134253656142401227/434781250000000000000000000000000 : ℝ)*base77 + (456270195054963727/434781250000000000000000000000000 : ℝ)*base79 + (17627713443133/34782500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (25127049/5000000000000000000000 : ℝ)*base90 + (25127049/5000000000000000000000 : ℝ)*base92 + (25127049/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3961262557388783823711111843/869562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (726036631/100000000000000 : ℝ)*(base19) + (33388039/4000000000000 : ℝ)*(base23) + (94906621/100000000000000 : ℝ)*(upper2) + (49538933/50000000000000 : ℝ)*(upper3) + (63028143/25000000000000 : ℝ)*(upper5) + (1610788066703079/100000000000000 : ℝ)*(major0) + (1610788066703079/100000000000000 : ℝ)*(major1) + (1610788066703079/100000000000000 : ℝ)*(major2) + (1343685481/25000000000000 : ℝ)*(sp1) + (22830051/625000000000 : ℝ)*(sp2) + (618632075754479/25000000000000 : ℝ)*(sp4) + (1237261101119681/50000000000000 : ℝ)*(sp5) + (1237261907754391/50000000000000 : ℝ)*(sp6) + (373523839269683/50000000000000 : ℝ)*(sp7) + (373523839269683/50000000000000 : ℝ)*(f.failure) + (618632075754479/25000000000000 : ℝ)*(f.sum) + (18124972042133/69565000000000000000000000000 : ℝ)*base65 + (128722089782949781/1739125000000000000000000000000000 : ℝ)*base67 + (2912171443650449781/1739125000000000000000000000000000 : ℝ)*base69 + (1569653270603550219/1739125000000000000000000000000000 : ℝ)*base72 + (11554894860167/69565000000000000000000000000 : ℝ)*base74 + (10995900436097800219/1739125000000000000000000000000000 : ℝ)*base76 + (7840955839678300219/1739125000000000000000000000000000 : ℝ)*base78 + (15338110462300219/1739125000000000000000000000000000 : ℝ)*base80 + (20547787844723/69565000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (886111/5000000000000000000000 : ℝ)*base89 + (886111/5000000000000000000000 : ℝ)*base91 + (886111/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1752_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (215620517/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10359/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1361/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2253/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18001/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1752_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1752_s2_0 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-242216843/2000000000 : ℝ)*x 0 + (2747187021/5000000000 : ℝ)*x 1 + (2540832753/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (242216843/2000000000 : ℝ)^5807 ≤ (7707076956691/100000000000000 : ℝ)^4783 := by
    have hnat : (242216843 : ℕ)^5807*100000000000000^4783 ≤ 7707076956691^4783*2000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      242216843 2000000000 7707076956691 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2747187021/5000000000 : ℝ)^5807 ≤ (9666447575683/20000000000000 : ℝ)^4783 := by
    have hnat : (2747187021 : ℕ)^5807*20000000000000^4783 ≤ 9666447575683^4783*5000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2747187021 5000000000 9666447575683 20000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2540832753/5000000000 : ℝ)^5807 ≤ (8792137029769/20000000000000 : ℝ)^4783 := by
    have hnat : (2540832753 : ℕ)^5807*20000000000000^4783 ≤ 8792137029769^4783*5000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2540832753 5000000000 8792137029769 20000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-242216843/2000000000 : ℝ), (2747187021/5000000000 : ℝ), (2540832753/5000000000 : ℝ)] ![(7707076956691/100000000000000 : ℝ), (9666447575683/20000000000000 : ℝ), (8792137029769/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-242216843/2000000000 : ℝ)|^5807 ≤ (7707076956691/100000000000000 : ℝ)^4783
        have hw : |(-242216843/2000000000 : ℝ)|=(242216843/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2747187021/5000000000 : ℝ)|^5807 ≤ (9666447575683/20000000000000 : ℝ)^4783
        have hw : |(2747187021/5000000000 : ℝ)|=(2747187021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2540832753/5000000000 : ℝ)|^5807 ≤ (8792137029769/20000000000000 : ℝ)^4783
        have hw : |(2540832753/5000000000 : ℝ)|=(2540832753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1752_s2_1 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5334896299/10000000000 : ℝ)*x 0 + (-1426901997/10000000000 : ℝ)*x 1 + (2540832743/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5334896299/10000000000 : ℝ)^5807 ≤ (23317176393321/50000000000000 : ℝ)^4783 := by
    have hnat : (5334896299 : ℕ)^5807*50000000000000^4783 ≤ 23317176393321^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5334896299 10000000000 23317176393321 50000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1426901997/10000000000 : ℝ)^5807 ≤ (4702481130137/50000000000000 : ℝ)^4783 := by
    have hnat : (1426901997 : ℕ)^5807*50000000000000^4783 ≤ 4702481130137^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1426901997 10000000000 4702481130137 50000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2540832743/5000000000 : ℝ)^5807 ≤ (43960684938787/100000000000000 : ℝ)^4783 := by
    have hnat : (2540832743 : ℕ)^5807*100000000000000^4783 ≤ 43960684938787^4783*5000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2540832743 5000000000 43960684938787 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5334896299/10000000000 : ℝ), (-1426901997/10000000000 : ℝ), (2540832743/5000000000 : ℝ)] ![(23317176393321/50000000000000 : ℝ), (4702481130137/50000000000000 : ℝ), (43960684938787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5334896299/10000000000 : ℝ)|^5807 ≤ (23317176393321/50000000000000 : ℝ)^4783
        have hw : |(5334896299/10000000000 : ℝ)|=(5334896299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1426901997/10000000000 : ℝ)|^5807 ≤ (4702481130137/50000000000000 : ℝ)^4783
        have hw : |(-1426901997/10000000000 : ℝ)|=(1426901997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2540832743/5000000000 : ℝ)|^5807 ≤ (43960684938787/100000000000000 : ℝ)^4783
        have hw : |(2540832743/5000000000 : ℝ)|=(2540832743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1752_s2_2 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5334896267/10000000000 : ℝ)*x 0 + (635208189/1250000000 : ℝ)*x 1 + (-713451003/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5334896267/10000000000 : ℝ)^5807 ≤ (46634352447031/100000000000000 : ℝ)^4783 := by
    have hnat : (5334896267 : ℕ)^5807*100000000000000^4783 ≤ 46634352447031^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5334896267 10000000000 46634352447031 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (635208189/1250000000 : ℝ)^5807 ≤ (21980342605931/50000000000000 : ℝ)^4783 := by
    have hnat : (635208189 : ℕ)^5807*50000000000000^4783 ≤ 21980342605931^4783*1250000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      635208189 1250000000 21980342605931 50000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (713451003/5000000000 : ℝ)^5807 ≤ (1880992466459/20000000000000 : ℝ)^4783 := by
    have hnat : (713451003 : ℕ)^5807*20000000000000^4783 ≤ 1880992466459^4783*5000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      713451003 5000000000 1880992466459 20000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5334896267/10000000000 : ℝ), (635208189/1250000000 : ℝ), (-713451003/5000000000 : ℝ)] ![(46634352447031/100000000000000 : ℝ), (21980342605931/50000000000000 : ℝ), (1880992466459/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5334896267/10000000000 : ℝ)|^5807 ≤ (46634352447031/100000000000000 : ℝ)^4783
        have hw : |(5334896267/10000000000 : ℝ)|=(5334896267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(635208189/1250000000 : ℝ)|^5807 ≤ (21980342605931/50000000000000 : ℝ)^4783
        have hw : |(635208189/1250000000 : ℝ)|=(635208189/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-713451003/5000000000 : ℝ)|^5807 ≤ (1880992466459/20000000000000 : ℝ)^4783
        have hw : |(-713451003/5000000000 : ℝ)|=(713451003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1752_s2_3 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (502089527/1250000000 : ℝ)*x 0 + (841133449/2500000000 : ℝ)*x 1 + (59144917/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (502089527/1250000000 : ℝ)^5807 ≤ (16520884869297/50000000000000 : ℝ)^4783 := by
    have hnat : (502089527 : ℕ)^5807*50000000000000^4783 ≤ 16520884869297^4783*1250000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502089527 1250000000 16520884869297 50000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (841133449/2500000000 : ℝ)^5807 ≤ (13323352103931/50000000000000 : ℝ)^4783 := by
    have hnat : (841133449 : ℕ)^5807*50000000000000^4783 ≤ 13323352103931^4783*2500000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      841133449 2500000000 13323352103931 50000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (59144917/125000000 : ℝ)^5807 ≤ (1612461041667/4000000000000 : ℝ)^4783 := by
    have hnat : (59144917 : ℕ)^5807*4000000000000^4783 ≤ 1612461041667^4783*125000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59144917 125000000 1612461041667 4000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(502089527/1250000000 : ℝ), (841133449/2500000000 : ℝ), (59144917/125000000 : ℝ)] ![(16520884869297/50000000000000 : ℝ), (13323352103931/50000000000000 : ℝ), (1612461041667/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(502089527/1250000000 : ℝ)|^5807 ≤ (16520884869297/50000000000000 : ℝ)^4783
        have hw : |(502089527/1250000000 : ℝ)|=(502089527/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(841133449/2500000000 : ℝ)|^5807 ≤ (13323352103931/50000000000000 : ℝ)^4783
        have hw : |(841133449/2500000000 : ℝ)|=(841133449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(59144917/125000000 : ℝ)|^5807 ≤ (1612461041667/4000000000000 : ℝ)^4783
        have hw : |(59144917/125000000 : ℝ)|=(59144917/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1752_s2_4 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1211431127/10000000000 : ℝ)*x 0 + (5088401763/10000000000 : ℝ)*x 1 + (2743748313/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1211431127/10000000000 : ℝ)^5807 ≤ (7709757355617/100000000000000 : ℝ)^4783 := by
    have hnat : (1211431127 : ℕ)^5807*100000000000000^4783 ≤ 7709757355617^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1211431127 10000000000 7709757355617 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5088401763/10000000000 : ℝ)^5807 ≤ (44031445514973/100000000000000 : ℝ)^4783 := by
    have hnat : (5088401763 : ℕ)^5807*100000000000000^4783 ≤ 44031445514973^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5088401763 10000000000 44031445514973 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2743748313/5000000000 : ℝ)^5807 ≤ (1206469927769/2500000000000 : ℝ)^4783 := by
    have hnat : (2743748313 : ℕ)^5807*2500000000000^4783 ≤ 1206469927769^4783*5000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2743748313 5000000000 1206469927769 2500000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1211431127/10000000000 : ℝ), (5088401763/10000000000 : ℝ), (2743748313/5000000000 : ℝ)] ![(7709757355617/100000000000000 : ℝ), (44031445514973/100000000000000 : ℝ), (1206469927769/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1211431127/10000000000 : ℝ)|^5807 ≤ (7709757355617/100000000000000 : ℝ)^4783
        have hw : |(-1211431127/10000000000 : ℝ)|=(1211431127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5088401763/10000000000 : ℝ)|^5807 ≤ (44031445514973/100000000000000 : ℝ)^4783
        have hw : |(5088401763/10000000000 : ℝ)|=(5088401763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2743748313/5000000000 : ℝ)|^5807 ≤ (1206469927769/2500000000000 : ℝ)^4783
        have hw : |(2743748313/5000000000 : ℝ)|=(2743748313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1752_s2_5 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2612776259/5000000000 : ℝ)*x 0 + (-204214089/2000000000 : ℝ)*x 1 + (685937081/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2612776259/5000000000 : ℝ)^5807 ≤ (22738232546387/50000000000000 : ℝ)^4783 := by
    have hnat : (2612776259 : ℕ)^5807*50000000000000^4783 ≤ 22738232546387^4783*5000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612776259 5000000000 22738232546387 50000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (204214089/2000000000 : ℝ)^5807 ≤ (195773048397/3125000000000 : ℝ)^4783 := by
    have hnat : (204214089 : ℕ)^5807*3125000000000^4783 ≤ 195773048397^4783*2000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204214089 2000000000 195773048397 3125000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (685937081/1250000000 : ℝ)^5807 ≤ (6032349668207/12500000000000 : ℝ)^4783 := by
    have hnat : (685937081 : ℕ)^5807*12500000000000^4783 ≤ 6032349668207^4783*1250000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685937081 1250000000 6032349668207 12500000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2612776259/5000000000 : ℝ), (-204214089/2000000000 : ℝ), (685937081/1250000000 : ℝ)] ![(22738232546387/50000000000000 : ℝ), (195773048397/3125000000000 : ℝ), (6032349668207/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2612776259/5000000000 : ℝ)|^5807 ≤ (22738232546387/50000000000000 : ℝ)^4783
        have hw : |(2612776259/5000000000 : ℝ)|=(2612776259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-204214089/2000000000 : ℝ)|^5807 ≤ (195773048397/3125000000000 : ℝ)^4783
        have hw : |(-204214089/2000000000 : ℝ)|=(204214089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(685937081/1250000000 : ℝ)|^5807 ≤ (6032349668207/12500000000000 : ℝ)^4783
        have hw : |(685937081/1250000000 : ℝ)|=(685937081/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1752_s2_6 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5225551209/10000000000 : ℝ)*x 0 + (5487497959/10000000000 : ℝ)*x 1 + (-510535211/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5225551209/10000000000 : ℝ)^5807 ≤ (45476451262029/100000000000000 : ℝ)^4783 := by
    have hnat : (5225551209 : ℕ)^5807*100000000000000^4783 ≤ 45476451262029^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225551209 10000000000 45476451262029 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5487497959/10000000000 : ℝ)^5807 ≤ (24129405671673/50000000000000 : ℝ)^4783 := by
    have hnat : (5487497959 : ℕ)^5807*50000000000000^4783 ≤ 24129405671673^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5487497959 10000000000 24129405671673 50000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (510535211/5000000000 : ℝ)^5807 ≤ (195773043043/3125000000000 : ℝ)^4783 := by
    have hnat : (510535211 : ℕ)^5807*3125000000000^4783 ≤ 195773043043^4783*5000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      510535211 5000000000 195773043043 3125000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5225551209/10000000000 : ℝ), (5487497959/10000000000 : ℝ), (-510535211/5000000000 : ℝ)] ![(45476451262029/100000000000000 : ℝ), (24129405671673/50000000000000 : ℝ), (195773043043/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5225551209/10000000000 : ℝ)|^5807 ≤ (45476451262029/100000000000000 : ℝ)^4783
        have hw : |(5225551209/10000000000 : ℝ)|=(5225551209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5487497959/10000000000 : ℝ)|^5807 ≤ (24129405671673/50000000000000 : ℝ)^4783
        have hw : |(5487497959/10000000000 : ℝ)|=(5487497959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-510535211/5000000000 : ℝ)|^5807 ≤ (195773043043/3125000000000 : ℝ)^4783
        have hw : |(-510535211/5000000000 : ℝ)|=(510535211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1752_s2_7 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (502233129/1250000000 : ℝ)*x 0 + (4709282119/10000000000 : ℝ)*x 1 + (846828197/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (502233129/1250000000 : ℝ)^5807 ≤ (8263310885251/25000000000000 : ℝ)^4783 := by
    have hnat : (502233129 : ℕ)^5807*25000000000000^4783 ≤ 8263310885251^4783*1250000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502233129 1250000000 8263310885251 25000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4709282119/10000000000 : ℝ)^5807 ≤ (501010791207/1250000000000 : ℝ)^4783 := by
    have hnat : (4709282119 : ℕ)^5807*1250000000000^4783 ≤ 501010791207^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4709282119 10000000000 501010791207 1250000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (846828197/2500000000 : ℝ)^5807 ≤ (6716473286341/25000000000000 : ℝ)^4783 := by
    have hnat : (846828197 : ℕ)^5807*25000000000000^4783 ≤ 6716473286341^4783*2500000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846828197 2500000000 6716473286341 25000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(502233129/1250000000 : ℝ), (4709282119/10000000000 : ℝ), (846828197/2500000000 : ℝ)] ![(8263310885251/25000000000000 : ℝ), (501010791207/1250000000000 : ℝ), (6716473286341/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(502233129/1250000000 : ℝ)|^5807 ≤ (8263310885251/25000000000000 : ℝ)^4783
        have hw : |(502233129/1250000000 : ℝ)|=(502233129/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4709282119/10000000000 : ℝ)|^5807 ≤ (501010791207/1250000000000 : ℝ)^4783
        have hw : |(4709282119/10000000000 : ℝ)|=(4709282119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(846828197/2500000000 : ℝ)|^5807 ≤ (6716473286341/25000000000000 : ℝ)^4783
        have hw : |(846828197/2500000000 : ℝ)|=(846828197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1752_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (215620517/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18001/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2253/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1813/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17937/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18001/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2253/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18001/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2253/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18001/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2253/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18001/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2253/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18001/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2253/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18001/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2253/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2253/25000 : ℝ) ^ (5791/1024 : ℝ) ≤ (30702094757733/25000000000000000000 : ℝ) := by
    have hpowers : (2253/25000 : ℝ)^5791 ≤ (30702094757733/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2253 : ℕ)^5791*25000000000000000000^1024 ≤ 30702094757733^1024*25000^5791 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2253 25000 30702094757733 25000000000000000000 5791 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2253/25000 : ℝ)) (X := (30702094757733/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5791 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18001/100000 : ℝ) ^ (5791/1024 : ℝ) ≤ (6144673672466443/100000000000000000000 : ℝ) := by
    have hpowers : (18001/100000 : ℝ)^5791 ≤ (6144673672466443/100000000000000000000 : ℝ)^1024 := by
      have hnat : (18001 : ℕ)^5791*100000000000000000000^1024 ≤ 6144673672466443^1024*100000^5791 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18001 100000 6144673672466443 100000000000000000000 5791 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18001/100000 : ℝ)) (X := (6144673672466443/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5791 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500030702094757733/12500000000000000000 : ℝ) ≤ (2000000868628237/2000000000000000 : ℝ) ^ (5791/1024 : ℝ) := by
    have hpowers : (12500030702094757733/12500000000000000000 : ℝ)^1024 ≤ (2000000868628237/2000000000000000 : ℝ)^5791 := by
      have hnat : (12500030702094757733 : ℕ)^1024*2000000000000000^5791 ≤ 2000000868628237^5791*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500030702094757733 12500000000000000000 2000000868628237 2000000000000000 1024 5791 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000868628237/2000000000000000 : ℝ)) (X := (12500030702094757733/12500000000000000000 : ℝ)) (by norm_num) 5791 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (800050139856411979/800000000000000000 : ℝ) ≤ (10000110822587981/10000000000000000 : ℝ) ^ (5791/1024 : ℝ) := by
    have hpowers : (800050139856411979/800000000000000000 : ℝ)^1024 ≤ (10000110822587981/10000000000000000 : ℝ)^5791 := by
      have hnat : (800050139856411979 : ℕ)^1024*10000000000000000^5791 ≤ 10000110822587981^5791*800000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        800050139856411979 800000000000000000 10000110822587981 10000000000000000 1024 5791 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000110822587981/10000000000000000 : ℝ)) (X := (800050139856411979/800000000000000000 : ℝ)) (by norm_num) 5791 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50006144673672466443/50000000000000000000 : ℝ) ≤ (10000217302034777/10000000000000000 : ℝ) ^ (5791/1024 : ℝ) := by
    have hpowers : (50006144673672466443/50000000000000000000 : ℝ)^1024 ≤ (10000217302034777/10000000000000000 : ℝ)^5791 := by
      have hnat : (50006144673672466443 : ℕ)^1024*10000000000000000^5791 ≤ 10000217302034777^5791*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006144673672466443 50000000000000000000 10000217302034777 10000000000000000 1024 5791 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000217302034777/10000000000000000 : ℝ)) (X := (50006144673672466443/50000000000000000000 : ℝ)) (by norm_num) 5791 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(30702094757733/25000000000000000000 : ℝ) ≤ ((89888119854947060861/89890000000000000000 : ℝ)+2*(26619861699/224725000000000 : ℝ)*(2253/25000 : ℝ))^(5791/1024 : ℝ) := by
    rw [show (89888119854947060861/89890000000000000000 : ℝ)+2*(26619861699/224725000000000 : ℝ)*(2253/25000 : ℝ)=(2000000868628237/2000000000000000 : ℝ) by norm_num, show 1+2*(30702094757733/25000000000000000000 : ℝ)=(12500030702094757733/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6144673672466443/100000000000000000000 : ℝ)+(30702094757733/25000000000000000000 : ℝ) ≤ ((89888119854947060861/89890000000000000000 : ℝ)+(26619861699/224725000000000 : ℝ)*((18001/100000 : ℝ)+(2253/25000 : ℝ)))^(5791/1024 : ℝ) := by
    rw [show (89888119854947060861/89890000000000000000 : ℝ)+(26619861699/224725000000000 : ℝ)*((18001/100000 : ℝ)+(2253/25000 : ℝ))=(10000110822587981/10000000000000000 : ℝ) by norm_num, show 1+(6144673672466443/100000000000000000000 : ℝ)+(30702094757733/25000000000000000000 : ℝ)=(800050139856411979/800000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6144673672466443/100000000000000000000 : ℝ) ≤ ((89888119854947060861/89890000000000000000 : ℝ)+2*(26619861699/224725000000000 : ℝ)*(18001/100000 : ℝ))^(5791/1024 : ℝ) := by
    rw [show (89888119854947060861/89890000000000000000 : ℝ)+2*(26619861699/224725000000000 : ℝ)*(18001/100000 : ℝ)=(10000217302034777/10000000000000000 : ℝ) by norm_num, show 1+2*(6144673672466443/100000000000000000000 : ℝ)=(50006144673672466443/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (89888119854947060861/89890000000000000000 : ℝ)*(X 1 0+X 2 0)+(26619861699/224725000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5791/1024 : ℝ)) (lo := (2253/25000 : ℝ)) (hi := (18001/100000 : ℝ)) (c := (89888119854947060861/89890000000000000000 : ℝ)) (alpha := (26619861699/224725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (89888119854947060861/89890000000000000000 : ℝ)*(X 0 1+X 2 1)+(26619861699/224725000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5791/1024 : ℝ)) (lo := (2253/25000 : ℝ)) (hi := (18001/100000 : ℝ)) (c := (89888119854947060861/89890000000000000000 : ℝ)) (alpha := (26619861699/224725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (89888119854947060861/89890000000000000000 : ℝ)*(X 0 2+X 1 2)+(26619861699/224725000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5791/1024 : ℝ)) (lo := (2253/25000 : ℝ)) (hi := (18001/100000 : ℝ)) (c := (89888119854947060861/89890000000000000000 : ℝ)) (alpha := (26619861699/224725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-242216843/2000000000 : ℝ)*X 0 0+(2747187021/5000000000 : ℝ)*X 0 1+(2540832753/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5334896299/10000000000 : ℝ)*X 1 0+(-1426901997/10000000000 : ℝ)*X 1 1+(2540832743/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5334896267/10000000000 : ℝ)*X 2 0+(635208189/1250000000 : ℝ)*X 2 1+(-713451003/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((502089527/1250000000 : ℝ)*X 0 0+(841133449/2500000000 : ℝ)*X 0 1+(59144917/125000000 : ℝ)*X 0 2+(502089527/1250000000 : ℝ)*X 1 0+(841133449/2500000000 : ℝ)*X 1 1+(59144917/125000000 : ℝ)*X 1 2+(502089527/1250000000 : ℝ)*X 2 0+(841133449/2500000000 : ℝ)*X 2 1+(59144917/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1211431127/10000000000 : ℝ)*X 0 0+(5088401763/10000000000 : ℝ)*X 0 1+(2743748313/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2612776259/5000000000 : ℝ)*X 1 0+(-204214089/2000000000 : ℝ)*X 1 1+(685937081/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5225551209/10000000000 : ℝ)*X 2 0+(5487497959/10000000000 : ℝ)*X 2 1+(-510535211/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((502233129/1250000000 : ℝ)*X 0 0+(4709282119/10000000000 : ℝ)*X 0 1+(846828197/2500000000 : ℝ)*X 0 2+(502233129/1250000000 : ℝ)*X 1 0+(4709282119/10000000000 : ℝ)*X 1 1+(846828197/2500000000 : ℝ)*X 1 2+(502233129/1250000000 : ℝ)*X 2 0+(4709282119/10000000000 : ℝ)*X 2 1+(846828197/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5622987843183416593751255559/2247250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (75858201/20000000000000 : ℝ)*(base19) + (337310181/100000000000000 : ℝ)*(base23) + (14642659/100000000000000 : ℝ)*(lower2) + (28047031/50000000000000 : ℝ)*(upper3) + (15120599/50000000000000 : ℝ)*(upper5) + (1577261331019073/100000000000000 : ℝ)*(major0) + (1577261331019073/100000000000000 : ℝ)*(major1) + (1577261331019073/100000000000000 : ℝ)*(major2) + (2423020759331261/100000000000000 : ℝ)*(sp0) + (151438967194887/6250000000000 : ℝ)*(sp1) + (302877939637377/12500000000000 : ℝ)*(sp2) + (731497793098341/100000000000000 : ℝ)*(sp3) + (193442371/6250000000000 : ℝ)*(sp4) + (46556257/5000000000000 : ℝ)*(sp7) + (731498724223481/100000000000000 : ℝ)*(f.failure) + (2423023854409197/100000000000000 : ℝ)*(f.sum) + (90068299591697/44945000000000000000000000000 : ℝ)*base66 + (25082988365779601853/8989000000000000000000000000000000 : ℝ)*base67 + (63233944328804398147/8989000000000000000000000000000000 : ℝ)*base70 + (22752346541722398147/8989000000000000000000000000000000 : ℝ)*base72 + (34354850276767/11236250000000000000000000000 : ℝ)*base73 + (48841605281394398147/8989000000000000000000000000000000 : ℝ)*base76 + (23106529897218398147/8989000000000000000000000000000000 : ℝ)*base78 + (28976930103538398147/8989000000000000000000000000000000 : ℝ)*base80 + (62257857785193/11236250000000000000000000000 : ℝ)*base82 + (96759677/10000000000000000000000 : ℝ)*base89 + (96759677/10000000000000000000000 : ℝ)*base91 + (96759677/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2151254581078999080680902857/449450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (767737311/100000000000000 : ℝ)*(base19) + (180932059/100000000000000 : ℝ)*(base23) + (2854851/1562500000000 : ℝ)*(lower1) + (16924371/10000000000000 : ℝ)*(upper3) + (694223/50000000000000 : ℝ)*(lower4) + (163105406863679/10000000000000 : ℝ)*(major0) + (163105406863679/10000000000000 : ℝ)*(major1) + (163105406863679/10000000000000 : ℝ)*(major2) + (182581957/10000000000000 : ℝ)*(sp2) + (5784983/2500000000000 : ℝ)*(sp3) + (1252830689121079/50000000000000 : ℝ)*(sp4) + (156603788156553/6250000000000 : ℝ)*(sp5) + (250565937149053/10000000000000 : ℝ)*(sp6) + (378223184042449/50000000000000 : ℝ)*(sp7) + (378223299742109/50000000000000 : ℝ)*(f.failure) + (1252830689121079/50000000000000 : ℝ)*(f.sum) + (15237593689671/4494500000000000000000000000 : ℝ)*base66 + (3040831182658632381/898900000000000000000000000000000 : ℝ)*base68 + (300499135296967619/898900000000000000000000000000000 : ℝ)*base69 + (12207260544776232381/898900000000000000000000000000000 : ℝ)*base72 + (1120921078941/898900000000000000000000000 : ℝ)*base73 + (4330445431447432381/898900000000000000000000000000000 : ℝ)*base76 + (22252530566389367619/898900000000000000000000000000000 : ℝ)*base77 + (29610853172147032381/898900000000000000000000000000000 : ℝ)*base80 + (605973709519/1123625000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (9250353/5000000000000000000000 : ℝ)*base89 + (9250353/5000000000000000000000 : ℝ)*base91 + (9250353/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1752_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (215620517/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18001/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2253/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1813/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17937/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1752_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1752_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (215620517/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1813/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17937/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1752_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1752_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1752_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (215620517/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1813/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17937/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1752_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

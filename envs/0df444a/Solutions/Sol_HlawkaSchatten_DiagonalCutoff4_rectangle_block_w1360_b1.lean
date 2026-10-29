-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1360_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:11:37.012604+00:00
-- url     : https://prove2.me/submissions/88703cd8-e64f-4e37-8a5e-7d060efea847

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
theorem support_rectangle_w1360_s3_0 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1013469777/5000000000 : ℝ)*x 0 + (5424920773/10000000000 : ℝ)*x 1 + (2616521103/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1013469777/5000000000 : ℝ)^135 ≤ (1543122411831/12500000000000 : ℝ)^103 := by
    have hnat : (1013469777 : ℕ)^135*12500000000000^103 ≤ 1543122411831^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1013469777 5000000000 1543122411831 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5424920773/10000000000 : ℝ)^135 ≤ (44861608876921/100000000000000 : ℝ)^103 := by
    have hnat : (5424920773 : ℕ)^135*100000000000000^103 ≤ 44861608876921^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424920773 10000000000 44861608876921 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2616521103/5000000000 : ℝ)^135 ≤ (42793411821989/100000000000000 : ℝ)^103 := by
    have hnat : (2616521103 : ℕ)^135*100000000000000^103 ≤ 42793411821989^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2616521103 5000000000 42793411821989 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1013469777/5000000000 : ℝ), (5424920773/10000000000 : ℝ), (2616521103/5000000000 : ℝ)] ![(1543122411831/12500000000000 : ℝ), (44861608876921/100000000000000 : ℝ), (42793411821989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1013469777/5000000000 : ℝ)|^135 ≤ (1543122411831/12500000000000 : ℝ)^103
        have hw : |(-1013469777/5000000000 : ℝ)|=(1013469777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5424920773/10000000000 : ℝ)|^135 ≤ (44861608876921/100000000000000 : ℝ)^103
        have hw : |(5424920773/10000000000 : ℝ)|=(5424920773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2616521103/5000000000 : ℝ)|^135 ≤ (42793411821989/100000000000000 : ℝ)^103
        have hw : |(2616521103/5000000000 : ℝ)|=(2616521103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s3_1 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5352040197/10000000000 : ℝ)*x 0 + (-265620067/1250000000 : ℝ)*x 1 + (41864337/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352040197/10000000000 : ℝ)^135 ≤ (1762933214457/4000000000000 : ℝ)^103 := by
    have hnat : (5352040197 : ℕ)^135*4000000000000^103 ≤ 1762933214457^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352040197 10000000000 1762933214457 4000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (265620067/1250000000 : ℝ)^135 ≤ (2626651733699/20000000000000 : ℝ)^103 := by
    have hnat : (265620067 : ℕ)^135*20000000000000^103 ≤ 2626651733699^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265620067 1250000000 2626651733699 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41864337/80000000 : ℝ)^135 ≤ (2139670547691/5000000000000 : ℝ)^103 := by
    have hnat : (41864337 : ℕ)^135*5000000000000^103 ≤ 2139670547691^103*80000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41864337 80000000 2139670547691 5000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352040197/10000000000 : ℝ), (-265620067/1250000000 : ℝ), (41864337/80000000 : ℝ)] ![(1762933214457/4000000000000 : ℝ), (2626651733699/20000000000000 : ℝ), (2139670547691/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352040197/10000000000 : ℝ)|^135 ≤ (1762933214457/4000000000000 : ℝ)^103
        have hw : |(5352040197/10000000000 : ℝ)|=(5352040197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-265620067/1250000000 : ℝ)|^135 ≤ (2626651733699/20000000000000 : ℝ)^103
        have hw : |(-265620067/1250000000 : ℝ)|=(265620067/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41864337/80000000 : ℝ)|^135 ≤ (2139670547691/5000000000000 : ℝ)^103
        have hw : |(41864337/80000000 : ℝ)|=(41864337/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s3_2 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5352040399/10000000000 : ℝ)*x 0 + (1046608367/2000000000 : ℝ)*x 1 + (-2124960651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352040399/10000000000 : ℝ)^135 ≤ (8814666508333/20000000000000 : ℝ)^103 := by
    have hnat : (5352040399 : ℕ)^135*20000000000000^103 ≤ 8814666508333^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352040399 10000000000 8814666508333 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1046608367/2000000000 : ℝ)^135 ≤ (42793407845561/100000000000000 : ℝ)^103 := by
    have hnat : (1046608367 : ℕ)^135*100000000000000^103 ≤ 42793407845561^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046608367 2000000000 42793407845561 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2124960651/10000000000 : ℝ)^135 ≤ (6566629800033/50000000000000 : ℝ)^103 := by
    have hnat : (2124960651 : ℕ)^135*50000000000000^103 ≤ 6566629800033^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124960651 10000000000 6566629800033 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352040399/10000000000 : ℝ), (1046608367/2000000000 : ℝ), (-2124960651/10000000000 : ℝ)] ![(8814666508333/20000000000000 : ℝ), (42793407845561/100000000000000 : ℝ), (6566629800033/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352040399/10000000000 : ℝ)|^135 ≤ (8814666508333/20000000000000 : ℝ)^103
        have hw : |(5352040399/10000000000 : ℝ)|=(5352040399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1046608367/2000000000 : ℝ)|^135 ≤ (42793407845561/100000000000000 : ℝ)^103
        have hw : |(1046608367/2000000000 : ℝ)|=(1046608367/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2124960651/10000000000 : ℝ)|^135 ≤ (6566629800033/50000000000000 : ℝ)^103
        have hw : |(-2124960651/10000000000 : ℝ)|=(2124960651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s3_3 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4320975909/10000000000 : ℝ)*x 0 + (4123048847/10000000000 : ℝ)*x 1 + (70744949/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4320975909/10000000000 : ℝ)^135 ≤ (2080868190909/6250000000000 : ℝ)^103 := by
    have hnat : (4320975909 : ℕ)^135*6250000000000^103 ≤ 2080868190909^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320975909 10000000000 2080868190909 6250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4123048847/10000000000 : ℝ)^135 ≤ (15654698622973/50000000000000 : ℝ)^103 := by
    have hnat : (4123048847 : ℕ)^135*50000000000000^103 ≤ 15654698622973^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4123048847 10000000000 15654698622973 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (70744949/156250000 : ℝ)^135 ≤ (884917792089/2500000000000 : ℝ)^103 := by
    have hnat : (70744949 : ℕ)^135*2500000000000^103 ≤ 884917792089^103*156250000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70744949 156250000 884917792089 2500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4320975909/10000000000 : ℝ), (4123048847/10000000000 : ℝ), (70744949/156250000 : ℝ)] ![(2080868190909/6250000000000 : ℝ), (15654698622973/50000000000000 : ℝ), (884917792089/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4320975909/10000000000 : ℝ)|^135 ≤ (2080868190909/6250000000000 : ℝ)^103
        have hw : |(4320975909/10000000000 : ℝ)|=(4320975909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4123048847/10000000000 : ℝ)|^135 ≤ (15654698622973/50000000000000 : ℝ)^103
        have hw : |(4123048847/10000000000 : ℝ)|=(4123048847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(70744949/156250000 : ℝ)|^135 ≤ (884917792089/2500000000000 : ℝ)^103
        have hw : |(70744949/156250000 : ℝ)|=(70744949/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s3_4 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-126684907/625000000 : ℝ)*x 0 + (1046766679/2000000000 : ℝ)*x 1 + (5424124387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (126684907/625000000 : ℝ)^135 ≤ (12345130629607/100000000000000 : ℝ)^103 := by
    have hnat : (126684907 : ℕ)^135*100000000000000^103 ≤ 12345130629607^103*625000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126684907 625000000 12345130629607 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1046766679/2000000000 : ℝ)^135 ≤ (42801892091591/100000000000000 : ℝ)^103 := by
    have hnat : (1046766679 : ℕ)^135*100000000000000^103 ≤ 42801892091591^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046766679 2000000000 42801892091591 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5424124387/10000000000 : ℝ)^135 ≤ (1794119090763/4000000000000 : ℝ)^103 := by
    have hnat : (5424124387 : ℕ)^135*4000000000000^103 ≤ 1794119090763^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424124387 10000000000 1794119090763 4000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-126684907/625000000 : ℝ), (1046766679/2000000000 : ℝ), (5424124387/10000000000 : ℝ)] ![(12345130629607/100000000000000 : ℝ), (42801892091591/100000000000000 : ℝ), (1794119090763/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-126684907/625000000 : ℝ)|^135 ≤ (12345130629607/100000000000000 : ℝ)^103
        have hw : |(-126684907/625000000 : ℝ)|=(126684907/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1046766679/2000000000 : ℝ)|^135 ≤ (42801892091591/100000000000000 : ℝ)^103
        have hw : |(1046766679/2000000000 : ℝ)|=(1046766679/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5424124387/10000000000 : ℝ)|^135 ≤ (1794119090763/4000000000000 : ℝ)^103
        have hw : |(5424124387/10000000000 : ℝ)|=(5424124387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s3_5 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2651257363/5000000000 : ℝ)*x 0 + (-24173477/125000000 : ℝ)*x 1 + (5424124803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651257363/5000000000 : ℝ)^135 ≤ (21769779295597/50000000000000 : ℝ)^103 := by
    have hnat : (2651257363 : ℕ)^135*50000000000000^103 ≤ 21769779295597^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651257363 5000000000 21769779295597 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (24173477/125000000 : ℝ)^135 ≤ (11607459617189/100000000000000 : ℝ)^103 := by
    have hnat : (24173477 : ℕ)^135*100000000000000^103 ≤ 11607459617189^103*125000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24173477 125000000 11607459617189 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5424124803/10000000000 : ℝ)^135 ≤ (44852981777777/100000000000000 : ℝ)^103 := by
    have hnat : (5424124803 : ℕ)^135*100000000000000^103 ≤ 44852981777777^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424124803 10000000000 44852981777777 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651257363/5000000000 : ℝ), (-24173477/125000000 : ℝ), (5424124803/10000000000 : ℝ)] ![(21769779295597/50000000000000 : ℝ), (11607459617189/100000000000000 : ℝ), (44852981777777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651257363/5000000000 : ℝ)|^135 ≤ (21769779295597/50000000000000 : ℝ)^103
        have hw : |(2651257363/5000000000 : ℝ)|=(2651257363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-24173477/125000000 : ℝ)|^135 ≤ (11607459617189/100000000000000 : ℝ)^103
        have hw : |(-24173477/125000000 : ℝ)|=(24173477/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5424124803/10000000000 : ℝ)|^135 ≤ (44852981777777/100000000000000 : ℝ)^103
        have hw : |(5424124803/10000000000 : ℝ)|=(5424124803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s3_6 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (662814451/1250000000 : ℝ)*x 0 + (5424124201/10000000000 : ℝ)*x 1 + (-1933877783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (662814451/1250000000 : ℝ)^135 ≤ (43539568083403/100000000000000 : ℝ)^103 := by
    have hnat : (662814451 : ℕ)^135*100000000000000^103 ≤ 43539568083403^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662814451 1250000000 43539568083403 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5424124201/10000000000 : ℝ)^135 ≤ (22426487626583/50000000000000 : ℝ)^103 := by
    have hnat : (5424124201 : ℕ)^135*50000000000000^103 ≤ 22426487626583^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424124201 10000000000 22426487626583 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1933877783/10000000000 : ℝ)^135 ≤ (11607456651361/100000000000000 : ℝ)^103 := by
    have hnat : (1933877783 : ℕ)^135*100000000000000^103 ≤ 11607456651361^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1933877783 10000000000 11607456651361 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(662814451/1250000000 : ℝ), (5424124201/10000000000 : ℝ), (-1933877783/10000000000 : ℝ)] ![(43539568083403/100000000000000 : ℝ), (22426487626583/50000000000000 : ℝ), (11607456651361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(662814451/1250000000 : ℝ)|^135 ≤ (43539568083403/100000000000000 : ℝ)^103
        have hw : |(662814451/1250000000 : ℝ)|=(662814451/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5424124201/10000000000 : ℝ)|^135 ≤ (22426487626583/50000000000000 : ℝ)^103
        have hw : |(5424124201/10000000000 : ℝ)|=(5424124201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1933877783/10000000000 : ℝ)|^135 ≤ (11607456651361/100000000000000 : ℝ)^103
        have hw : |(-1933877783/10000000000 : ℝ)|=(1933877783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s3_7 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4321014091/10000000000 : ℝ)*x 0 + (4526007729/10000000000 : ℝ)*x 1 + (2062364081/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4321014091/10000000000 : ℝ)^135 ≤ (16647138327937/50000000000000 : ℝ)^103 := by
    have hnat : (4321014091 : ℕ)^135*50000000000000^103 ≤ 16647138327937^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4321014091 10000000000 16647138327937 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4526007729/10000000000 : ℝ)^135 ≤ (141518443391/400000000000 : ℝ)^103 := by
    have hnat : (4526007729 : ℕ)^135*400000000000^103 ≤ 141518443391^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4526007729 10000000000 141518443391 400000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2062364081/5000000000 : ℝ)^135 ≤ (31326112478073/100000000000000 : ℝ)^103 := by
    have hnat : (2062364081 : ℕ)^135*100000000000000^103 ≤ 31326112478073^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062364081 5000000000 31326112478073 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4321014091/10000000000 : ℝ), (4526007729/10000000000 : ℝ), (2062364081/5000000000 : ℝ)] ![(16647138327937/50000000000000 : ℝ), (141518443391/400000000000 : ℝ), (31326112478073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4321014091/10000000000 : ℝ)|^135 ≤ (16647138327937/50000000000000 : ℝ)^103
        have hw : |(4321014091/10000000000 : ℝ)|=(4321014091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4526007729/10000000000 : ℝ)|^135 ≤ (141518443391/400000000000 : ℝ)^103
        have hw : |(4526007729/10000000000 : ℝ)|=(4526007729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2062364081/5000000000 : ℝ)|^135 ≤ (31326112478073/100000000000000 : ℝ)^103
        have hw : |(2062364081/5000000000 : ℝ)|=(2062364081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1360_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1942979/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8017/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9967/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2733/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14993/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8017/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9967/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8017/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9967/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8017/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9967/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8017/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9967/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8017/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9967/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8017/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9967/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9967/100000 : ℝ) ^ (4319/1024 : ℝ) ≤ (186647335442459/3125000000000000000 : ℝ) := by
    have hpowers : (9967/100000 : ℝ)^4319 ≤ (186647335442459/3125000000000000000 : ℝ)^1024 := by
      have hnat : (9967 : ℕ)^4319*3125000000000000000^1024 ≤ 186647335442459^1024*100000^4319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9967 100000 186647335442459 3125000000000000000 4319 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9967/100000 : ℝ)) (X := (186647335442459/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8017/50000 : ℝ) ^ (4319/1024 : ℝ) ≤ (11091410091291857/25000000000000000000 : ℝ) := by
    have hpowers : (8017/50000 : ℝ)^4319 ≤ (11091410091291857/25000000000000000000 : ℝ)^1024 := by
      have hnat : (8017 : ℕ)^4319*25000000000000000000^1024 ≤ 11091410091291857^1024*50000^4319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8017 50000 11091410091291857 25000000000000000000 4319 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8017/50000 : ℝ)) (X := (11091410091291857/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562686647335442459/1562500000000000000 : ℝ) ≤ (10000283203575873/10000000000000000 : ℝ) ^ (4319/1024 : ℝ) := by
    have hpowers : (1562686647335442459/1562500000000000000 : ℝ)^1024 ≤ (10000283203575873/10000000000000000 : ℝ)^4319 := by
      have hnat : (1562686647335442459 : ℕ)^1024*10000000000000000^4319 ≤ 10000283203575873^4319*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562686647335442459 1562500000000000000 10000283203575873 10000000000000000 1024 4319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000283203575873/10000000000000000 : ℝ)) (X := (1562686647335442459/1562500000000000000 : ℝ)) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012584588774831529/25000000000000000000 : ℝ) ≤ (1250149156577661/1250000000000000 : ℝ) ^ (4319/1024 : ℝ) := by
    have hpowers : (25012584588774831529/25000000000000000000 : ℝ)^1024 ≤ (1250149156577661/1250000000000000 : ℝ)^4319 := by
      have hnat : (25012584588774831529 : ℕ)^1024*1250000000000000^4319 ≤ 1250149156577661^4319*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012584588774831529 25000000000000000000 1250149156577661 1250000000000000 1024 4319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250149156577661/1250000000000000 : ℝ)) (X := (25012584588774831529/25000000000000000000 : ℝ)) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12511091410091291857/12500000000000000000 : ℝ) ≤ (10002103301666703/10000000000000000 : ℝ) ^ (4319/1024 : ℝ) := by
    have hpowers : (12511091410091291857/12500000000000000000 : ℝ)^1024 ≤ (10002103301666703/10000000000000000 : ℝ)^4319 := by
      have hnat : (12511091410091291857 : ℕ)^1024*10000000000000000^4319 ≤ 10002103301666703^4319*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12511091410091291857 12500000000000000000 10002103301666703 10000000000000000 1024 4319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002103301666703/10000000000000000 : ℝ)) (X := (12511091410091291857/12500000000000000000 : ℝ)) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(186647335442459/3125000000000000000 : ℝ) ≤ ((60653577278423518881/60670000000000000000 : ℝ)+2*(182009809083/121340000000000 : ℝ)*(9967/100000 : ℝ))^(4319/1024 : ℝ) := by
    rw [show (60653577278423518881/60670000000000000000 : ℝ)+2*(182009809083/121340000000000 : ℝ)*(9967/100000 : ℝ)=(10000283203575873/10000000000000000 : ℝ) by norm_num, show 1+2*(186647335442459/3125000000000000000 : ℝ)=(1562686647335442459/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11091410091291857/25000000000000000000 : ℝ)+(186647335442459/3125000000000000000 : ℝ) ≤ ((60653577278423518881/60670000000000000000 : ℝ)+(182009809083/121340000000000 : ℝ)*((8017/50000 : ℝ)+(9967/100000 : ℝ)))^(4319/1024 : ℝ) := by
    rw [show (60653577278423518881/60670000000000000000 : ℝ)+(182009809083/121340000000000 : ℝ)*((8017/50000 : ℝ)+(9967/100000 : ℝ))=(1250149156577661/1250000000000000 : ℝ) by norm_num, show 1+(11091410091291857/25000000000000000000 : ℝ)+(186647335442459/3125000000000000000 : ℝ)=(25012584588774831529/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11091410091291857/25000000000000000000 : ℝ) ≤ ((60653577278423518881/60670000000000000000 : ℝ)+2*(182009809083/121340000000000 : ℝ)*(8017/50000 : ℝ))^(4319/1024 : ℝ) := by
    rw [show (60653577278423518881/60670000000000000000 : ℝ)+2*(182009809083/121340000000000 : ℝ)*(8017/50000 : ℝ)=(10002103301666703/10000000000000000 : ℝ) by norm_num, show 1+2*(11091410091291857/25000000000000000000 : ℝ)=(12511091410091291857/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (60653577278423518881/60670000000000000000 : ℝ)*(X 1 0+X 2 0)+(182009809083/121340000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4319/1024 : ℝ)) (lo := (9967/100000 : ℝ)) (hi := (8017/50000 : ℝ)) (c := (60653577278423518881/60670000000000000000 : ℝ)) (alpha := (182009809083/121340000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (60653577278423518881/60670000000000000000 : ℝ)*(X 0 1+X 2 1)+(182009809083/121340000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4319/1024 : ℝ)) (lo := (9967/100000 : ℝ)) (hi := (8017/50000 : ℝ)) (c := (60653577278423518881/60670000000000000000 : ℝ)) (alpha := (182009809083/121340000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (60653577278423518881/60670000000000000000 : ℝ)*(X 0 2+X 1 2)+(182009809083/121340000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4319/1024 : ℝ)) (lo := (9967/100000 : ℝ)) (hi := (8017/50000 : ℝ)) (c := (60653577278423518881/60670000000000000000 : ℝ)) (alpha := (182009809083/121340000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1013469777/5000000000 : ℝ)*X 0 0+(5424920773/10000000000 : ℝ)*X 0 1+(2616521103/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352040197/10000000000 : ℝ)*X 1 0+(-265620067/1250000000 : ℝ)*X 1 1+(41864337/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352040399/10000000000 : ℝ)*X 2 0+(1046608367/2000000000 : ℝ)*X 2 1+(-2124960651/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4320975909/10000000000 : ℝ)*X 0 0+(4123048847/10000000000 : ℝ)*X 0 1+(70744949/156250000 : ℝ)*X 0 2+(4320975909/10000000000 : ℝ)*X 1 0+(4123048847/10000000000 : ℝ)*X 1 1+(70744949/156250000 : ℝ)*X 1 2+(4320975909/10000000000 : ℝ)*X 2 0+(4123048847/10000000000 : ℝ)*X 2 1+(70744949/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-126684907/625000000 : ℝ)*X 0 0+(1046766679/2000000000 : ℝ)*X 0 1+(5424124387/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2651257363/5000000000 : ℝ)*X 1 0+(-24173477/125000000 : ℝ)*X 1 1+(5424124803/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((662814451/1250000000 : ℝ)*X 2 0+(5424124201/10000000000 : ℝ)*X 2 1+(-1933877783/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4321014091/10000000000 : ℝ)*X 0 0+(4526007729/10000000000 : ℝ)*X 0 1+(2062364081/5000000000 : ℝ)*X 0 2+(4321014091/10000000000 : ℝ)*X 1 0+(4526007729/10000000000 : ℝ)*X 1 1+(2062364081/5000000000 : ℝ)*X 1 2+(4321014091/10000000000 : ℝ)*X 2 0+(4526007729/10000000000 : ℝ)*X 2 1+(2062364081/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21134256081128421552761509683/3033500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (782619867/50000000000000 : ℝ)*(base19) + (691135167/50000000000000 : ℝ)*(base23) + (426122663/100000000000000 : ℝ)*(lower2) + (2948743/781250000000 : ℝ)*(upper3) + (111460491/50000000000000 : ℝ)*(lower4) + (3841551090348719/100000000000000 : ℝ)*(major0) + (3841551090348719/100000000000000 : ℝ)*(major1) + (3841551090348719/100000000000000 : ℝ)*(major2) + (2605826846143981/50000000000000 : ℝ)*(sp0) + (5211669213390341/100000000000000 : ℝ)*(sp1) + (5211669396359741/100000000000000 : ℝ)*(sp2) + (1235707666325161/50000000000000 : ℝ)*(sp3) + (17086342113/100000000000000 : ℝ)*(sp4) + (1979648153/12500000000000 : ℝ)*(sp7) + (1235715584917773/50000000000000 : ℝ)*(f.failure) + (208466831145203/4000000000000 : ℝ)*(f.sum) + (19735532944949/6067000000000000000000000000 : ℝ)*base66 + (17869436452212163439/6067000000000000000000000000000000 : ℝ)*base67 + (9526999308551836561/6067000000000000000000000000000000 : ℝ)*base70 + (34418080669643836561/6067000000000000000000000000000000 : ℝ)*base72 + (2849038509659/6067000000000000000000000000 : ℝ)*base73 + (69823410651074163439/6067000000000000000000000000000000 : ℝ)*base75 + (16025144593062163439/6067000000000000000000000000000000 : ℝ)*base77 + (36089447554454163439/6067000000000000000000000000000000 : ℝ)*base79 + (24370980361943/3033500000000000000000000000 : ℝ)*base82 + (290767/62500000000000000000 : ℝ)*base89 + (290767/62500000000000000000 : ℝ)*base91 + (290767/62500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (326092821616949527089/94796875000000000000000000 : ℝ) := by norm_num
    linear_combination (118017797/12500000000000 : ℝ)*(base19) + (295851151/12500000000000 : ℝ)*(base23) + (133110053/50000000000000 : ℝ)*(upper3) + (182635621/100000000000000 : ℝ)*(lower4) + (21197903/10000000000000 : ℝ)*(upper5) + (3873571035439017/100000000000000 : ℝ)*(major0) + (3873571035439017/100000000000000 : ℝ)*(major1) + (3873571035439017/100000000000000 : ℝ)*(major2) + (10059003877/50000000000000 : ℝ)*(sp1) + (41972991121/100000000000000 : ℝ)*(sp2) + (262755550539779/5000000000000 : ℝ)*(sp4) + (105101798972909/2000000000000 : ℝ)*(sp5) + (5255066670995251/100000000000000 : ℝ)*(sp6) + (2492030945418747/100000000000000 : ℝ)*(sp7) + (2492030945418747/100000000000000 : ℝ)*(f.failure) + (262755550539779/5000000000000 : ℝ)*(f.sum) + (2339849344909/758375000000000000000000000 : ℝ)*base65 + (2583842680108079977/6067000000000000000000000000000000 : ℝ)*base67 + (15050941264228920023/6067000000000000000000000000000000 : ℝ)*base70 + (46262247245124079977/6067000000000000000000000000000000 : ℝ)*base71 + (7699612429831/3033500000000000000000000000 : ℝ)*base74 + (36934150021608920023/6067000000000000000000000000000000 : ℝ)*base76 + (17065648722358920023/6067000000000000000000000000000000 : ℝ)*base78 + (64107333764246079977/6067000000000000000000000000000000 : ℝ)*base79 + (8092963004159/6067000000000000000000000000 : ℝ)*base82 + (377313/125000000000000000000 : ℝ)*base89 + (377313/125000000000000000000 : ℝ)*base91 + (377313/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1360_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1942979/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8017/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9967/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2733/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14993/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1360_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1360_s4_0 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-25353261/125000000 : ℝ)*x 0 + (5414030377/10000000000 : ℝ)*x 1 + (5243064513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (25353261/125000000 : ℝ)^135 ≤ (3088882005467/25000000000000 : ℝ)^103 := by
    have hnat : (25353261 : ℕ)^135*25000000000000^103 ≤ 3088882005467^103*125000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25353261 125000000 3088882005467 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414030377/10000000000 : ℝ)^135 ≤ (44743607752407/100000000000000 : ℝ)^103 := by
    have hnat : (5414030377 : ℕ)^135*100000000000000^103 ≤ 44743607752407^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414030377 10000000000 44743607752407 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243064513/10000000000 : ℝ)^135 ≤ (42900864204799/100000000000000 : ℝ)^103 := by
    have hnat : (5243064513 : ℕ)^135*100000000000000^103 ≤ 42900864204799^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243064513 10000000000 42900864204799 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-25353261/125000000 : ℝ), (5414030377/10000000000 : ℝ), (5243064513/10000000000 : ℝ)] ![(3088882005467/25000000000000 : ℝ), (44743607752407/100000000000000 : ℝ), (42900864204799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-25353261/125000000 : ℝ)|^135 ≤ (3088882005467/25000000000000 : ℝ)^103
        have hw : |(-25353261/125000000 : ℝ)|=(25353261/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414030377/10000000000 : ℝ)|^135 ≤ (44743607752407/100000000000000 : ℝ)^103
        have hw : |(5414030377/10000000000 : ℝ)|=(5414030377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243064513/10000000000 : ℝ)|^135 ≤ (42900864204799/100000000000000 : ℝ)^103
        have hw : |(5243064513/10000000000 : ℝ)|=(5243064513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s4_1 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2674628733/5000000000 : ℝ)*x 0 + (-1057698627/5000000000 : ℝ)*x 1 + (1048612779/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674628733/5000000000 : ℝ)^135 ≤ (44043298020191/100000000000000 : ℝ)^103 := by
    have hnat : (2674628733 : ℕ)^135*100000000000000^103 ≤ 44043298020191^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674628733 5000000000 44043298020191 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1057698627/5000000000 : ℝ)^135 ≤ (261116887697/2000000000000 : ℝ)^103 := by
    have hnat : (1057698627 : ℕ)^135*2000000000000^103 ≤ 261116887697^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057698627 5000000000 261116887697 2000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048612779/2000000000 : ℝ)^135 ≤ (42900857577053/100000000000000 : ℝ)^103 := by
    have hnat : (1048612779 : ℕ)^135*100000000000000^103 ≤ 42900857577053^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048612779 2000000000 42900857577053 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674628733/5000000000 : ℝ), (-1057698627/5000000000 : ℝ), (1048612779/2000000000 : ℝ)] ![(44043298020191/100000000000000 : ℝ), (261116887697/2000000000000 : ℝ), (42900857577053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674628733/5000000000 : ℝ)|^135 ≤ (44043298020191/100000000000000 : ℝ)^103
        have hw : |(2674628733/5000000000 : ℝ)|=(2674628733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1057698627/5000000000 : ℝ)|^135 ≤ (261116887697/2000000000000 : ℝ)^103
        have hw : |(-1057698627/5000000000 : ℝ)|=(1057698627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048612779/2000000000 : ℝ)|^135 ≤ (42900857577053/100000000000000 : ℝ)^103
        have hw : |(1048612779/2000000000 : ℝ)|=(1048612779/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s4_2 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (42794057/80000000 : ℝ)*x 0 + (5243064399/10000000000 : ℝ)*x 1 + (-1057698521/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42794057/80000000 : ℝ)^135 ≤ (1101082358507/2500000000000 : ℝ)^103 := by
    have hnat : (42794057 : ℕ)^135*2500000000000^103 ≤ 1101082358507^103*80000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42794057 80000000 1101082358507 2500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243064399/10000000000 : ℝ)^135 ≤ (8580172596441/20000000000000 : ℝ)^103 := by
    have hnat : (5243064399 : ℕ)^135*20000000000000^103 ≤ 8580172596441^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243064399 10000000000 8580172596441 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1057698521/5000000000 : ℝ)^135 ≤ (3263960667481/25000000000000 : ℝ)^103 := by
    have hnat : (1057698521 : ℕ)^135*25000000000000^103 ≤ 3263960667481^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057698521 5000000000 3263960667481 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42794057/80000000 : ℝ), (5243064399/10000000000 : ℝ), (-1057698521/5000000000 : ℝ)] ![(1101082358507/2500000000000 : ℝ), (8580172596441/20000000000000 : ℝ), (3263960667481/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42794057/80000000 : ℝ)|^135 ≤ (1101082358507/2500000000000 : ℝ)^103
        have hw : |(42794057/80000000 : ℝ)|=(42794057/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243064399/10000000000 : ℝ)|^135 ≤ (8580172596441/20000000000000 : ℝ)^103
        have hw : |(5243064399/10000000000 : ℝ)|=(5243064399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1057698521/5000000000 : ℝ)|^135 ≤ (3263960667481/25000000000000 : ℝ)^103
        have hw : |(-1057698521/5000000000 : ℝ)|=(1057698521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s4_3 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1080444643/2500000000 : ℝ)*x 0 + (4145001199/10000000000 : ℝ)*x 1 + (4505528083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080444643/2500000000 : ℝ)^135 ≤ (33301997398519/100000000000000 : ℝ)^103 := by
    have hnat : (1080444643 : ℕ)^135*100000000000000^103 ≤ 33301997398519^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080444643 2500000000 33301997398519 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4145001199/10000000000 : ℝ)^135 ≤ (7882017218253/25000000000000 : ℝ)^103 := by
    have hnat : (4145001199 : ℕ)^135*25000000000000^103 ≤ 7882017218253^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4145001199 10000000000 7882017218253 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4505528083/10000000000 : ℝ)^135 ≤ (7033986743791/20000000000000 : ℝ)^103 := by
    have hnat : (4505528083 : ℕ)^135*20000000000000^103 ≤ 7033986743791^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4505528083 10000000000 7033986743791 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1080444643/2500000000 : ℝ), (4145001199/10000000000 : ℝ), (4505528083/10000000000 : ℝ)] ![(33301997398519/100000000000000 : ℝ), (7882017218253/25000000000000 : ℝ), (7033986743791/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1080444643/2500000000 : ℝ)|^135 ≤ (33301997398519/100000000000000 : ℝ)^103
        have hw : |(1080444643/2500000000 : ℝ)|=(1080444643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4145001199/10000000000 : ℝ)|^135 ≤ (7882017218253/25000000000000 : ℝ)^103
        have hw : |(4145001199/10000000000 : ℝ)|=(4145001199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4505528083/10000000000 : ℝ)|^135 ≤ (7033986743791/20000000000000 : ℝ)^103
        have hw : |(4505528083/10000000000 : ℝ)|=(4505528083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s4_4 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-253534269/1250000000 : ℝ)*x 0 + (104873863/200000000 : ℝ)*x 1 + (5413398171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (253534269/1250000000 : ℝ)^135 ≤ (12355633988921/100000000000000 : ℝ)^103 := by
    have hnat : (253534269 : ℕ)^135*100000000000000^103 ≤ 12355633988921^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253534269 1250000000 12355633988921 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104873863/200000000 : ℝ)^135 ≤ (8581521230597/20000000000000 : ℝ)^103 := by
    have hnat : (104873863 : ℕ)^135*20000000000000^103 ≤ 8581521230597^103*200000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104873863 200000000 8581521230597 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413398171/10000000000 : ℝ)^135 ≤ (22368379924783/50000000000000 : ℝ)^103 := by
    have hnat : (5413398171 : ℕ)^135*50000000000000^103 ≤ 22368379924783^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413398171 10000000000 22368379924783 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-253534269/1250000000 : ℝ), (104873863/200000000 : ℝ), (5413398171/10000000000 : ℝ)] ![(12355633988921/100000000000000 : ℝ), (8581521230597/20000000000000 : ℝ), (22368379924783/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-253534269/1250000000 : ℝ)|^135 ≤ (12355633988921/100000000000000 : ℝ)^103
        have hw : |(-253534269/1250000000 : ℝ)|=(253534269/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(104873863/200000000 : ℝ)|^135 ≤ (8581521230597/20000000000000 : ℝ)^103
        have hw : |(104873863/200000000 : ℝ)|=(104873863/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413398171/10000000000 : ℝ)|^135 ≤ (22368379924783/50000000000000 : ℝ)^103
        have hw : |(5413398171/10000000000 : ℝ)|=(5413398171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s4_5 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (530513053/1000000000 : ℝ)*x 0 + (-486265753/2500000000 : ℝ)*x 1 + (1082679613/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530513053/1000000000 : ℝ)^135 ≤ (5445964050003/12500000000000 : ℝ)^103 := by
    have hnat : (530513053 : ℕ)^135*12500000000000^103 ≤ 5445964050003^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530513053 1000000000 5445964050003 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (486265753/2500000000 : ℝ)^135 ≤ (11695528877579/100000000000000 : ℝ)^103 := by
    have hnat : (486265753 : ℕ)^135*100000000000000^103 ≤ 11695528877579^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      486265753 2500000000 11695528877579 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082679613/2000000000 : ℝ)^135 ≤ (44736758701421/100000000000000 : ℝ)^103 := by
    have hnat : (1082679613 : ℕ)^135*100000000000000^103 ≤ 44736758701421^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082679613 2000000000 44736758701421 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530513053/1000000000 : ℝ), (-486265753/2500000000 : ℝ), (1082679613/2000000000 : ℝ)] ![(5445964050003/12500000000000 : ℝ), (11695528877579/100000000000000 : ℝ), (44736758701421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530513053/1000000000 : ℝ)|^135 ≤ (5445964050003/12500000000000 : ℝ)^103
        have hw : |(530513053/1000000000 : ℝ)|=(530513053/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-486265753/2500000000 : ℝ)|^135 ≤ (11695528877579/100000000000000 : ℝ)^103
        have hw : |(-486265753/2500000000 : ℝ)|=(486265753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082679613/2000000000 : ℝ)|^135 ≤ (44736758701421/100000000000000 : ℝ)^103
        have hw : |(1082679613/2000000000 : ℝ)|=(1082679613/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s4_6 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5305130301/10000000000 : ℝ)*x 0 + (1082679653/2000000000 : ℝ)*x 1 + (-38901261/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305130301/10000000000 : ℝ)^135 ≤ (10891927483779/25000000000000 : ℝ)^103 := by
    have hnat : (5305130301 : ℕ)^135*25000000000000^103 ≤ 10891927483779^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305130301 10000000000 10891927483779 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082679653/2000000000 : ℝ)^135 ≤ (44736760867733/100000000000000 : ℝ)^103 := by
    have hnat : (1082679653 : ℕ)^135*100000000000000^103 ≤ 44736760867733^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082679653 2000000000 44736760867733 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (38901261/200000000 : ℝ)^135 ≤ (5847764588529/50000000000000 : ℝ)^103 := by
    have hnat : (38901261 : ℕ)^135*50000000000000^103 ≤ 5847764588529^103*200000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38901261 200000000 5847764588529 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305130301/10000000000 : ℝ), (1082679653/2000000000 : ℝ), (-38901261/200000000 : ℝ)] ![(10891927483779/25000000000000 : ℝ), (44736760867733/100000000000000 : ℝ), (5847764588529/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305130301/10000000000 : ℝ)|^135 ≤ (10891927483779/25000000000000 : ℝ)^103
        have hw : |(5305130301/10000000000 : ℝ)|=(5305130301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082679653/2000000000 : ℝ)|^135 ≤ (44736760867733/100000000000000 : ℝ)^103
        have hw : |(1082679653/2000000000 : ℝ)|=(1082679653/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-38901261/200000000 : ℝ)|^135 ≤ (5847764588529/50000000000000 : ℝ)^103
        have hw : |(-38901261/200000000 : ℝ)|=(38901261/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s4_7 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4321806083/10000000000 : ℝ)*x 0 + (112605049/250000000 : ℝ)*x 1 + (4146334133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4321806083/10000000000 : ℝ)^135 ≤ (33302275248979/100000000000000 : ℝ)^103 := by
    have hnat : (4321806083 : ℕ)^135*100000000000000^103 ≤ 33302275248979^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4321806083 10000000000 33302275248979 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (112605049/250000000 : ℝ)^135 ≤ (35156366640337/100000000000000 : ℝ)^103 := by
    have hnat : (112605049 : ℕ)^135*100000000000000^103 ≤ 35156366640337^103*250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112605049 250000000 35156366640337 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4146334133/10000000000 : ℝ)^135 ≤ (6308271619221/20000000000000 : ℝ)^103 := by
    have hnat : (4146334133 : ℕ)^135*20000000000000^103 ≤ 6308271619221^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4146334133 10000000000 6308271619221 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4321806083/10000000000 : ℝ), (112605049/250000000 : ℝ), (4146334133/10000000000 : ℝ)] ![(33302275248979/100000000000000 : ℝ), (35156366640337/100000000000000 : ℝ), (6308271619221/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4321806083/10000000000 : ℝ)|^135 ≤ (33302275248979/100000000000000 : ℝ)^103
        have hw : |(4321806083/10000000000 : ℝ)|=(4321806083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(112605049/250000000 : ℝ)|^135 ≤ (35156366640337/100000000000000 : ℝ)^103
        have hw : |(112605049/250000000 : ℝ)|=(112605049/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4146334133/10000000000 : ℝ)|^135 ≤ (6308271619221/20000000000000 : ℝ)^103
        have hw : |(4146334133/10000000000 : ℝ)|=(4146334133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1360_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1942979/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14993/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2733/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5573/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7383/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14993/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2733/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14993/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2733/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14993/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2733/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14993/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2733/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14993/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2733/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14993/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2733/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2733/25000 : ℝ) ^ (4319/1024 : ℝ) ≤ (8819679520477231/100000000000000000000 : ℝ) := by
    have hpowers : (2733/25000 : ℝ)^4319 ≤ (8819679520477231/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2733 : ℕ)^4319*100000000000000000000^1024 ≤ 8819679520477231^1024*25000^4319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2733 25000 8819679520477231 100000000000000000000 4319 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2733/25000 : ℝ)) (X := (8819679520477231/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14993/100000 : ℝ) ^ (4319/1024 : ℝ) ≤ (33426013070203423/100000000000000000000 : ℝ) := by
    have hpowers : (14993/100000 : ℝ)^4319 ≤ (33426013070203423/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14993 : ℕ)^4319*100000000000000000000^1024 ≤ 33426013070203423^1024*100000^4319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14993 100000 33426013070203423 100000000000000000000 4319 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14993/100000 : ℝ)) (X := (33426013070203423/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008819679520477231/50000000000000000000 : ℝ) ≤ (2500104546703033/2500000000000000 : ℝ) ^ (4319/1024 : ℝ) := by
    have hpowers : (50008819679520477231/50000000000000000000 : ℝ)^1024 ≤ (2500104546703033/2500000000000000 : ℝ)^4319 := by
      have hnat : (50008819679520477231 : ℕ)^1024*2500000000000000^4319 ≤ 2500104546703033^4319*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008819679520477231 50000000000000000000 2500104546703033 2500000000000000 1024 4319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500104546703033/2500000000000000 : ℝ)) (X := (50008819679520477231/50000000000000000000 : ℝ)) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021122846295340327/50000000000000000000 : ℝ) ≤ (1000100144986689/1000000000000000 : ℝ) ^ (4319/1024 : ℝ) := by
    have hpowers : (50021122846295340327/50000000000000000000 : ℝ)^1024 ≤ (1000100144986689/1000000000000000 : ℝ)^4319 := by
      have hnat : (50021122846295340327 : ℕ)^1024*1000000000000000^4319 ≤ 1000100144986689^4319*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021122846295340327 50000000000000000000 1000100144986689 1000000000000000 1024 4319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000100144986689/1000000000000000 : ℝ)) (X := (50021122846295340327/50000000000000000000 : ℝ)) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033426013070203423/50000000000000000000 : ℝ) ≤ (625099044557603/625000000000000 : ℝ) ^ (4319/1024 : ℝ) := by
    have hpowers : (50033426013070203423/50000000000000000000 : ℝ)^1024 ≤ (625099044557603/625000000000000 : ℝ)^4319 := by
      have hnat : (50033426013070203423 : ℕ)^1024*625000000000000^4319 ≤ 625099044557603^4319*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033426013070203423 50000000000000000000 625099044557603 625000000000000 1024 4319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625099044557603/625000000000000 : ℝ)) (X := (50033426013070203423/50000000000000000000 : ℝ)) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8819679520477231/100000000000000000000 : ℝ) ≤ ((2029947289660741957/2030500000000000000 : ℝ)+2*(291631527379/203050000000000 : ℝ)*(2733/25000 : ℝ))^(4319/1024 : ℝ) := by
    rw [show (2029947289660741957/2030500000000000000 : ℝ)+2*(291631527379/203050000000000 : ℝ)*(2733/25000 : ℝ)=(2500104546703033/2500000000000000 : ℝ) by norm_num, show 1+2*(8819679520477231/100000000000000000000 : ℝ)=(50008819679520477231/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33426013070203423/100000000000000000000 : ℝ)+(8819679520477231/100000000000000000000 : ℝ) ≤ ((2029947289660741957/2030500000000000000 : ℝ)+(291631527379/203050000000000 : ℝ)*((14993/100000 : ℝ)+(2733/25000 : ℝ)))^(4319/1024 : ℝ) := by
    rw [show (2029947289660741957/2030500000000000000 : ℝ)+(291631527379/203050000000000 : ℝ)*((14993/100000 : ℝ)+(2733/25000 : ℝ))=(1000100144986689/1000000000000000 : ℝ) by norm_num, show 1+(33426013070203423/100000000000000000000 : ℝ)+(8819679520477231/100000000000000000000 : ℝ)=(50021122846295340327/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33426013070203423/100000000000000000000 : ℝ) ≤ ((2029947289660741957/2030500000000000000 : ℝ)+2*(291631527379/203050000000000 : ℝ)*(14993/100000 : ℝ))^(4319/1024 : ℝ) := by
    rw [show (2029947289660741957/2030500000000000000 : ℝ)+2*(291631527379/203050000000000 : ℝ)*(14993/100000 : ℝ)=(625099044557603/625000000000000 : ℝ) by norm_num, show 1+2*(33426013070203423/100000000000000000000 : ℝ)=(50033426013070203423/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2029947289660741957/2030500000000000000 : ℝ)*(X 1 0+X 2 0)+(291631527379/203050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4319/1024 : ℝ)) (lo := (2733/25000 : ℝ)) (hi := (14993/100000 : ℝ)) (c := (2029947289660741957/2030500000000000000 : ℝ)) (alpha := (291631527379/203050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2029947289660741957/2030500000000000000 : ℝ)*(X 0 1+X 2 1)+(291631527379/203050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4319/1024 : ℝ)) (lo := (2733/25000 : ℝ)) (hi := (14993/100000 : ℝ)) (c := (2029947289660741957/2030500000000000000 : ℝ)) (alpha := (291631527379/203050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2029947289660741957/2030500000000000000 : ℝ)*(X 0 2+X 1 2)+(291631527379/203050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4319/1024 : ℝ)) (lo := (2733/25000 : ℝ)) (hi := (14993/100000 : ℝ)) (c := (2029947289660741957/2030500000000000000 : ℝ)) (alpha := (291631527379/203050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-25353261/125000000 : ℝ)*X 0 0+(5414030377/10000000000 : ℝ)*X 0 1+(5243064513/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674628733/5000000000 : ℝ)*X 1 0+(-1057698627/5000000000 : ℝ)*X 1 1+(1048612779/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((42794057/80000000 : ℝ)*X 2 0+(5243064399/10000000000 : ℝ)*X 2 1+(-1057698521/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1080444643/2500000000 : ℝ)*X 0 0+(4145001199/10000000000 : ℝ)*X 0 1+(4505528083/10000000000 : ℝ)*X 0 2+(1080444643/2500000000 : ℝ)*X 1 0+(4145001199/10000000000 : ℝ)*X 1 1+(4505528083/10000000000 : ℝ)*X 1 2+(1080444643/2500000000 : ℝ)*X 2 0+(4145001199/10000000000 : ℝ)*X 2 1+(4505528083/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-253534269/1250000000 : ℝ)*X 0 0+(104873863/200000000 : ℝ)*X 0 1+(5413398171/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((530513053/1000000000 : ℝ)*X 1 0+(-486265753/2500000000 : ℝ)*X 1 1+(1082679613/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305130301/10000000000 : ℝ)*X 2 0+(1082679653/2000000000 : ℝ)*X 2 1+(-38901261/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4321806083/10000000000 : ℝ)*X 0 0+(112605049/250000000 : ℝ)*X 0 1+(4146334133/10000000000 : ℝ)*X 0 2+(4321806083/10000000000 : ℝ)*X 1 0+(112605049/250000000 : ℝ)*X 1 1+(4146334133/10000000000 : ℝ)*X 1 2+(4321806083/10000000000 : ℝ)*X 2 0+(112605049/250000000 : ℝ)*X 2 1+(4146334133/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (199710062193450729297660123/20305000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1223457291/100000000000000 : ℝ)*(base19) + (274396597/50000000000000 : ℝ)*(base23) + (33130451/20000000000000 : ℝ)*(lower2) + (4212951/100000000000000 : ℝ)*(lower4) + (1527161/5000000000000 : ℝ)*(lower5) + (862287657282187/20000000000000 : ℝ)*(major0) + (862287657282187/20000000000000 : ℝ)*(major1) + (862287657282187/20000000000000 : ℝ)*(major2) + (1462283489914989/25000000000000 : ℝ)*(sp0) + (2924572841089107/50000000000000 : ℝ)*(sp1) + (5849146356842311/100000000000000 : ℝ)*(sp2) + (173357725789067/6250000000000 : ℝ)*(sp3) + (258919511/2000000000000 : ℝ)*(sp4) + (57267109/1000000000000 : ℝ)*(sp7) + (2773729339335973/100000000000000 : ℝ)*(f.failure) + (1169829381127101/20000000000000 : ℝ)*(f.sum) + (16254287951251/2030500000000000000000000000 : ℝ)*base65 + (49312353261949959/40610000000000000000000000000000 : ℝ)*base67 + (58463172005590041/40610000000000000000000000000000 : ℝ)*base70 + (610939866557469959/40610000000000000000000000000000 : ℝ)*base71 + (8577081224227/2030500000000000000000000000 : ℝ)*base73 + (114229916852689959/40610000000000000000000000000000 : ℝ)*base75 + (195248996725359959/40610000000000000000000000000000 : ℝ)*base77 + (149027706126020041/40610000000000000000000000000000 : ℝ)*base80 + (113221795073/1015250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (733567/125000000000000000000 : ℝ)*base89 + (733567/125000000000000000000 : ℝ)*base91 + (733567/125000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (116979195683099335396505391/10152500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (51792297/2500000000000 : ℝ)*(base19) + (7519831/400000000000 : ℝ)*(base23) + (46291411/50000000000000 : ℝ)*(upper3) + (48875309/100000000000000 : ℝ)*(lower4) + (193425603/100000000000000 : ℝ)*(upper5) + (434345176255121/10000000000000 : ℝ)*(major0) + (434345176255121/10000000000000 : ℝ)*(major1) + (434345176255121/10000000000000 : ℝ)*(major2) + (9336452559/20000000000000 : ℝ)*(sp1) + (1347973689/3125000000000 : ℝ)*(sp2) + (5892578187856969/100000000000000 : ℝ)*(sp4) + (2946264716951147/50000000000000 : ℝ)*(sp5) + (5892533172741171/100000000000000 : ℝ)*(sp6) + (1397162476585957/50000000000000 : ℝ)*(sp7) + (1397162476585957/50000000000000 : ℝ)*(f.failure) + (5892578187856969/100000000000000 : ℝ)*(f.sum) + (10681813046711/2030500000000000000000000000 : ℝ)*base65 + (210204628846548203/20305000000000000000000000000000 : ℝ)*base68 + (118710917560203203/20305000000000000000000000000000 : ℝ)*base70 + (31072951556958203/20305000000000000000000000000000 : ℝ)*base72 + (5056286676233/2030500000000000000000000000 : ℝ)*base74 + (69907426819316797/20305000000000000000000000000000 : ℝ)*base75 + (171242451537163203/20305000000000000000000000000000 : ℝ)*base78 + (285896489382766797/20305000000000000000000000000000 : ℝ)*base79 + (94697066683/101525000000000000000000000 : ℝ)*base82 + (104097/62500000000000000000 : ℝ)*base90 + (104097/62500000000000000000 : ℝ)*base92 + (104097/62500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1360_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1942979/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14993/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2733/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5573/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7383/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1360_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1360_s5_0 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-202848097/1000000000 : ℝ)*x 0 + (5412112237/10000000000 : ℝ)*x 1 + (1048967563/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (202848097/1000000000 : ℝ)^135 ≤ (12357285304717/100000000000000 : ℝ)^103 := by
    have hnat : (202848097 : ℕ)^135*100000000000000^103 ≤ 12357285304717^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202848097 1000000000 12357285304717 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412112237/10000000000 : ℝ)^135 ≤ (44722831689457/100000000000000 : ℝ)^103 := by
    have hnat : (5412112237 : ℕ)^135*100000000000000^103 ≤ 44722831689457^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412112237 10000000000 44722831689457 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048967563/2000000000 : ℝ)^135 ≤ (42919882995623/100000000000000 : ℝ)^103 := by
    have hnat : (1048967563 : ℕ)^135*100000000000000^103 ≤ 42919882995623^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048967563 2000000000 42919882995623 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-202848097/1000000000 : ℝ), (5412112237/10000000000 : ℝ), (1048967563/2000000000 : ℝ)] ![(12357285304717/100000000000000 : ℝ), (44722831689457/100000000000000 : ℝ), (42919882995623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-202848097/1000000000 : ℝ)|^135 ≤ (12357285304717/100000000000000 : ℝ)^103
        have hw : |(-202848097/1000000000 : ℝ)|=(202848097/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412112237/10000000000 : ℝ)|^135 ≤ (44722831689457/100000000000000 : ℝ)^103
        have hw : |(5412112237/10000000000 : ℝ)|=(5412112237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048967563/2000000000 : ℝ)|^135 ≤ (42919882995623/100000000000000 : ℝ)^103
        have hw : |(1048967563/2000000000 : ℝ)|=(1048967563/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s5_1 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1337191567/2500000000 : ℝ)*x 0 + (-2113700417/10000000000 : ℝ)*x 1 + (163901181/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337191567/2500000000 : ℝ)^135 ≤ (44037997319657/100000000000000 : ℝ)^103 := by
    have hnat : (1337191567 : ℕ)^135*100000000000000^103 ≤ 44037997319657^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337191567 2500000000 44037997319657 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2113700417/10000000000 : ℝ)^135 ≤ (3260529978809/25000000000000 : ℝ)^103 := by
    have hnat : (2113700417 : ℕ)^135*25000000000000^103 ≤ 3260529978809^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113700417 10000000000 3260529978809 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163901181/312500000 : ℝ)^135 ≤ (21459941374467/50000000000000 : ℝ)^103 := by
    have hnat : (163901181 : ℕ)^135*50000000000000^103 ≤ 21459941374467^103*312500000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163901181 312500000 21459941374467 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337191567/2500000000 : ℝ), (-2113700417/10000000000 : ℝ), (163901181/312500000 : ℝ)] ![(44037997319657/100000000000000 : ℝ), (3260529978809/25000000000000 : ℝ), (21459941374467/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337191567/2500000000 : ℝ)|^135 ≤ (44037997319657/100000000000000 : ℝ)^103
        have hw : |(1337191567/2500000000 : ℝ)|=(1337191567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2113700417/10000000000 : ℝ)|^135 ≤ (3260529978809/25000000000000 : ℝ)^103
        have hw : |(-2113700417/10000000000 : ℝ)|=(2113700417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163901181/312500000 : ℝ)|^135 ≤ (21459941374467/50000000000000 : ℝ)^103
        have hw : |(163901181/312500000 : ℝ)|=(163901181/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s5_2 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5348766291/10000000000 : ℝ)*x 0 + (1311209447/2500000000 : ℝ)*x 1 + (-264212549/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348766291/10000000000 : ℝ)^135 ≤ (8807599513571/20000000000000 : ℝ)^103 := by
    have hnat : (5348766291 : ℕ)^135*20000000000000^103 ≤ 8807599513571^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348766291 10000000000 8807599513571 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311209447/2500000000 : ℝ)^135 ≤ (42919882706031/100000000000000 : ℝ)^103 := by
    have hnat : (1311209447 : ℕ)^135*100000000000000^103 ≤ 42919882706031^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311209447 2500000000 42919882706031 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (264212549/1250000000 : ℝ)^135 ≤ (2608423942611/20000000000000 : ℝ)^103 := by
    have hnat : (264212549 : ℕ)^135*20000000000000^103 ≤ 2608423942611^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264212549 1250000000 2608423942611 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348766291/10000000000 : ℝ), (1311209447/2500000000 : ℝ), (-264212549/1250000000 : ℝ)] ![(8807599513571/20000000000000 : ℝ), (42919882706031/100000000000000 : ℝ), (2608423942611/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348766291/10000000000 : ℝ)|^135 ≤ (8807599513571/20000000000000 : ℝ)^103
        have hw : |(5348766291/10000000000 : ℝ)|=(5348766291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311209447/2500000000 : ℝ)|^135 ≤ (42919882706031/100000000000000 : ℝ)^103
        have hw : |(1311209447/2500000000 : ℝ)|=(1311209447/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-264212549/1250000000 : ℝ)|^135 ≤ (2608423942611/20000000000000 : ℝ)^103
        have hw : |(-264212549/1250000000 : ℝ)|=(264212549/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s5_3 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4321911517/10000000000 : ℝ)*x 0 + (4148876761/10000000000 : ℝ)*x 1 + (4501619339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4321911517/10000000000 : ℝ)^135 ≤ (8325835024173/25000000000000 : ℝ)^103 := by
    have hnat : (4321911517 : ℕ)^135*25000000000000^103 ≤ 8325835024173^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4321911517 10000000000 8325835024173 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4148876761/10000000000 : ℝ)^135 ≤ (6313342306403/20000000000000 : ℝ)^103 := by
    have hnat : (4148876761 : ℕ)^135*20000000000000^103 ≤ 6313342306403^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4148876761 10000000000 6313342306403 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4501619339/10000000000 : ℝ)^135 ≤ (43912435441/125000000000 : ℝ)^103 := by
    have hnat : (4501619339 : ℕ)^135*125000000000^103 ≤ 43912435441^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4501619339 10000000000 43912435441 125000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4321911517/10000000000 : ℝ), (4148876761/10000000000 : ℝ), (4501619339/10000000000 : ℝ)] ![(8325835024173/25000000000000 : ℝ), (6313342306403/20000000000000 : ℝ), (43912435441/125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4321911517/10000000000 : ℝ)|^135 ≤ (8325835024173/25000000000000 : ℝ)^103
        have hw : |(4321911517/10000000000 : ℝ)|=(4321911517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4148876761/10000000000 : ℝ)|^135 ≤ (6313342306403/20000000000000 : ℝ)^103
        have hw : |(4148876761/10000000000 : ℝ)|=(4148876761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4501619339/10000000000 : ℝ)|^135 ≤ (43912435441/125000000000 : ℝ)^103
        have hw : |(4501619339/10000000000 : ℝ)|=(4501619339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s5_4 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-405698629/2000000000 : ℝ)*x 0 + (2622719913/5000000000 : ℝ)*x 1 + (42277399/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (405698629/2000000000 : ℝ)^135 ≤ (12357382516309/100000000000000 : ℝ)^103 := by
    have hnat : (405698629 : ℕ)^135*100000000000000^103 ≤ 12357382516309^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      405698629 2000000000 12357382516309 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622719913/5000000000 : ℝ)^135 ≤ (10731585015237/25000000000000 : ℝ)^103 := by
    have hnat : (2622719913 : ℕ)^135*25000000000000^103 ≤ 10731585015237^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622719913 5000000000 10731585015237 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42277399/78125000 : ℝ)^135 ≤ (44716277404761/100000000000000 : ℝ)^103 := by
    have hnat : (42277399 : ℕ)^135*100000000000000^103 ≤ 44716277404761^103*78125000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42277399 78125000 44716277404761 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-405698629/2000000000 : ℝ), (2622719913/5000000000 : ℝ), (42277399/78125000 : ℝ)] ![(12357382516309/100000000000000 : ℝ), (10731585015237/25000000000000 : ℝ), (44716277404761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-405698629/2000000000 : ℝ)|^135 ≤ (12357382516309/100000000000000 : ℝ)^103
        have hw : |(-405698629/2000000000 : ℝ)|=(405698629/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622719913/5000000000 : ℝ)|^135 ≤ (10731585015237/25000000000000 : ℝ)^103
        have hw : |(2622719913/5000000000 : ℝ)|=(2622719913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42277399/78125000 : ℝ)|^135 ≤ (44716277404761/100000000000000 : ℝ)^103
        have hw : |(42277399/78125000 : ℝ)|=(42277399/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s5_5 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5305592071/10000000000 : ℝ)*x 0 + (-15576249/80000000 : ℝ)*x 1 + (5411507083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305592071/10000000000 : ℝ)^135 ≤ (8714536079537/20000000000000 : ℝ)^103 := by
    have hnat : (5305592071 : ℕ)^135*20000000000000^103 ≤ 8714536079537^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305592071 10000000000 8714536079537 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (15576249/80000000 : ℝ)^135 ≤ (11711042063793/100000000000000 : ℝ)^103 := by
    have hnat : (15576249 : ℕ)^135*100000000000000^103 ≤ 11711042063793^103*80000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15576249 80000000 11711042063793 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411507083/10000000000 : ℝ)^135 ≤ (5589534690487/12500000000000 : ℝ)^103 := by
    have hnat : (5411507083 : ℕ)^135*12500000000000^103 ≤ 5589534690487^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411507083 10000000000 5589534690487 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305592071/10000000000 : ℝ), (-15576249/80000000 : ℝ), (5411507083/10000000000 : ℝ)] ![(8714536079537/20000000000000 : ℝ), (11711042063793/100000000000000 : ℝ), (5589534690487/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305592071/10000000000 : ℝ)|^135 ≤ (8714536079537/20000000000000 : ℝ)^103
        have hw : |(5305592071/10000000000 : ℝ)|=(5305592071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-15576249/80000000 : ℝ)|^135 ≤ (11711042063793/100000000000000 : ℝ)^103
        have hw : |(-15576249/80000000 : ℝ)|=(15576249/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411507083/10000000000 : ℝ)|^135 ≤ (5589534690487/12500000000000 : ℝ)^103
        have hw : |(5411507083/10000000000 : ℝ)|=(5411507083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s5_6 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5305592093/10000000000 : ℝ)*x 0 + (108230141/200000000 : ℝ)*x 1 + (-97351557/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305592093/10000000000 : ℝ)^135 ≤ (8714536126899/20000000000000 : ℝ)^103 := by
    have hnat : (5305592093 : ℕ)^135*20000000000000^103 ≤ 8714536126899^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305592093 10000000000 8714536126899 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108230141/200000000 : ℝ)^135 ≤ (44716277166493/100000000000000 : ℝ)^103 := by
    have hnat : (108230141 : ℕ)^135*100000000000000^103 ≤ 44716277166493^103*200000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108230141 200000000 44716277166493 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (97351557/500000000 : ℝ)^135 ≤ (5855521091023/50000000000000 : ℝ)^103 := by
    have hnat : (97351557 : ℕ)^135*50000000000000^103 ≤ 5855521091023^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97351557 500000000 5855521091023 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305592093/10000000000 : ℝ), (108230141/200000000 : ℝ), (-97351557/500000000 : ℝ)] ![(8714536126899/20000000000000 : ℝ), (44716277166493/100000000000000 : ℝ), (5855521091023/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305592093/10000000000 : ℝ)|^135 ≤ (8714536126899/20000000000000 : ℝ)^103
        have hw : |(5305592093/10000000000 : ℝ)|=(5305592093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(108230141/200000000 : ℝ)|^135 ≤ (44716277166493/100000000000000 : ℝ)^103
        have hw : |(108230141/200000000 : ℝ)|=(108230141/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-97351557/500000000 : ℝ)|^135 ≤ (5855521091023/50000000000000 : ℝ)^103
        have hw : |(-97351557/500000000 : ℝ)|=(97351557/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s5_7 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (270121071/625000000 : ℝ)*x 0 + (562543727/1250000000 : ℝ)*x 1 + (830030563/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270121071/625000000 : ℝ)^135 ≤ (33303598841139/100000000000000 : ℝ)^103 := by
    have hnat : (270121071 : ℕ)^135*100000000000000^103 ≤ 33303598841139^103*625000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270121071 625000000 33303598841139 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (562543727/1250000000 : ℝ)^135 ≤ (8779240951221/25000000000000 : ℝ)^103 := by
    have hnat : (562543727 : ℕ)^135*25000000000000^103 ≤ 8779240951221^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562543727 1250000000 8779240951221 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (830030563/2000000000 : ℝ)^135 ≤ (31579437333709/100000000000000 : ℝ)^103 := by
    have hnat : (830030563 : ℕ)^135*100000000000000^103 ≤ 31579437333709^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      830030563 2000000000 31579437333709 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(270121071/625000000 : ℝ), (562543727/1250000000 : ℝ), (830030563/2000000000 : ℝ)] ![(33303598841139/100000000000000 : ℝ), (8779240951221/25000000000000 : ℝ), (31579437333709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(270121071/625000000 : ℝ)|^135 ≤ (33303598841139/100000000000000 : ℝ)^103
        have hw : |(270121071/625000000 : ℝ)|=(270121071/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(562543727/1250000000 : ℝ)|^135 ≤ (8779240951221/25000000000000 : ℝ)^103
        have hw : |(562543727/1250000000 : ℝ)|=(562543727/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(830030563/2000000000 : ℝ)|^135 ≤ (31579437333709/100000000000000 : ℝ)^103
        have hw : |(830030563/2000000000 : ℝ)|=(830030563/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1360_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1942979/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7383/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5573/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (699/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (589/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7383/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5573/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7383/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5573/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7383/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5573/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7383/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5573/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7383/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5573/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7383/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5573/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5573/50000 : ℝ) ^ (4319/1024 : ℝ) ≤ (4785573565586749/50000000000000000000 : ℝ) := by
    have hpowers : (5573/50000 : ℝ)^4319 ≤ (4785573565586749/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5573 : ℕ)^4319*50000000000000000000^1024 ≤ 4785573565586749^1024*50000^4319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5573 50000 4785573565586749 50000000000000000000 4319 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5573/50000 : ℝ)) (X := (4785573565586749/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7383/50000 : ℝ) ^ (4319/1024 : ℝ) ≤ (7835721347053217/25000000000000000000 : ℝ) := by
    have hpowers : (7383/50000 : ℝ)^4319 ≤ (7835721347053217/25000000000000000000 : ℝ)^1024 := by
      have hnat : (7383 : ℕ)^4319*25000000000000000000^1024 ≤ 7835721347053217^1024*50000^4319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7383 50000 7835721347053217 25000000000000000000 4319 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7383/50000 : ℝ)) (X := (7835721347053217/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004785573565586749/25000000000000000000 : ℝ) ≤ (10000453815193039/10000000000000000 : ℝ) ^ (4319/1024 : ℝ) := by
    have hpowers : (25004785573565586749/25000000000000000000 : ℝ)^1024 ≤ (10000453815193039/10000000000000000 : ℝ)^4319 := by
      have hnat : (25004785573565586749 : ℕ)^1024*10000000000000000^4319 ≤ 10000453815193039^4319*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004785573565586749 25000000000000000000 10000453815193039 10000000000000000 1024 4319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000453815193039/10000000000000000 : ℝ)) (X := (25004785573565586749/25000000000000000000 : ℝ)) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020457016259693183/50000000000000000000 : ℝ) ≤ (10000969887294321/10000000000000000 : ℝ) ^ (4319/1024 : ℝ) := by
    have hpowers : (50020457016259693183/50000000000000000000 : ℝ)^1024 ≤ (10000969887294321/10000000000000000 : ℝ)^4319 := by
      have hnat : (50020457016259693183 : ℕ)^1024*10000000000000000^4319 ≤ 10000969887294321^4319*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020457016259693183 50000000000000000000 10000969887294321 10000000000000000 1024 4319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000969887294321/10000000000000000 : ℝ)) (X := (50020457016259693183/50000000000000000000 : ℝ)) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507835721347053217/12500000000000000000 : ℝ) ≤ (10001485959395603/10000000000000000 : ℝ) ^ (4319/1024 : ℝ) := by
    have hpowers : (12507835721347053217/12500000000000000000 : ℝ)^1024 ≤ (10001485959395603/10000000000000000 : ℝ)^4319 := by
      have hnat : (12507835721347053217 : ℕ)^1024*10000000000000000^4319 ≤ 10001485959395603^4319*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507835721347053217 12500000000000000000 10001485959395603 10000000000000000 1024 4319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001485959395603/10000000000000000 : ℝ)) (X := (12507835721347053217/12500000000000000000 : ℝ)) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4785573565586749/50000000000000000000 : ℝ) ≤ ((9047534632929255709/9050000000000000000 : ℝ)+2*(258036050641/181000000000000 : ℝ)*(5573/50000 : ℝ))^(4319/1024 : ℝ) := by
    rw [show (9047534632929255709/9050000000000000000 : ℝ)+2*(258036050641/181000000000000 : ℝ)*(5573/50000 : ℝ)=(10000453815193039/10000000000000000 : ℝ) by norm_num, show 1+2*(4785573565586749/50000000000000000000 : ℝ)=(25004785573565586749/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7835721347053217/25000000000000000000 : ℝ)+(4785573565586749/50000000000000000000 : ℝ) ≤ ((9047534632929255709/9050000000000000000 : ℝ)+(258036050641/181000000000000 : ℝ)*((7383/50000 : ℝ)+(5573/50000 : ℝ)))^(4319/1024 : ℝ) := by
    rw [show (9047534632929255709/9050000000000000000 : ℝ)+(258036050641/181000000000000 : ℝ)*((7383/50000 : ℝ)+(5573/50000 : ℝ))=(10000969887294321/10000000000000000 : ℝ) by norm_num, show 1+(7835721347053217/25000000000000000000 : ℝ)+(4785573565586749/50000000000000000000 : ℝ)=(50020457016259693183/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7835721347053217/25000000000000000000 : ℝ) ≤ ((9047534632929255709/9050000000000000000 : ℝ)+2*(258036050641/181000000000000 : ℝ)*(7383/50000 : ℝ))^(4319/1024 : ℝ) := by
    rw [show (9047534632929255709/9050000000000000000 : ℝ)+2*(258036050641/181000000000000 : ℝ)*(7383/50000 : ℝ)=(10001485959395603/10000000000000000 : ℝ) by norm_num, show 1+2*(7835721347053217/25000000000000000000 : ℝ)=(12507835721347053217/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9047534632929255709/9050000000000000000 : ℝ)*(X 1 0+X 2 0)+(258036050641/181000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4319/1024 : ℝ)) (lo := (5573/50000 : ℝ)) (hi := (7383/50000 : ℝ)) (c := (9047534632929255709/9050000000000000000 : ℝ)) (alpha := (258036050641/181000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9047534632929255709/9050000000000000000 : ℝ)*(X 0 1+X 2 1)+(258036050641/181000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4319/1024 : ℝ)) (lo := (5573/50000 : ℝ)) (hi := (7383/50000 : ℝ)) (c := (9047534632929255709/9050000000000000000 : ℝ)) (alpha := (258036050641/181000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9047534632929255709/9050000000000000000 : ℝ)*(X 0 2+X 1 2)+(258036050641/181000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4319/1024 : ℝ)) (lo := (5573/50000 : ℝ)) (hi := (7383/50000 : ℝ)) (c := (9047534632929255709/9050000000000000000 : ℝ)) (alpha := (258036050641/181000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-202848097/1000000000 : ℝ)*X 0 0+(5412112237/10000000000 : ℝ)*X 0 1+(1048967563/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337191567/2500000000 : ℝ)*X 1 0+(-2113700417/10000000000 : ℝ)*X 1 1+(163901181/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348766291/10000000000 : ℝ)*X 2 0+(1311209447/2500000000 : ℝ)*X 2 1+(-264212549/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4321911517/10000000000 : ℝ)*X 0 0+(4148876761/10000000000 : ℝ)*X 0 1+(4501619339/10000000000 : ℝ)*X 0 2+(4321911517/10000000000 : ℝ)*X 1 0+(4148876761/10000000000 : ℝ)*X 1 1+(4501619339/10000000000 : ℝ)*X 1 2+(4321911517/10000000000 : ℝ)*X 2 0+(4148876761/10000000000 : ℝ)*X 2 1+(4501619339/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-405698629/2000000000 : ℝ)*X 0 0+(2622719913/5000000000 : ℝ)*X 0 1+(42277399/78125000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305592071/10000000000 : ℝ)*X 1 0+(-15576249/80000000 : ℝ)*X 1 1+(5411507083/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305592093/10000000000 : ℝ)*X 2 0+(108230141/200000000 : ℝ)*X 2 1+(-97351557/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((270121071/625000000 : ℝ)*X 0 0+(562543727/1250000000 : ℝ)*X 0 1+(830030563/2000000000 : ℝ)*X 0 2+(270121071/625000000 : ℝ)*X 1 0+(562543727/1250000000 : ℝ)*X 1 1+(830030563/2000000000 : ℝ)*X 1 2+(270121071/625000000 : ℝ)*X 2 0+(562543727/1250000000 : ℝ)*X 2 1+(830030563/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (733682059733567353266590223/113125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (574089273/50000000000000 : ℝ)*(base19) + (1086748451/100000000000000 : ℝ)*(base23) + (4660749/10000000000000 : ℝ)*(lower2) + (13209131/10000000000000 : ℝ)*(upper3) + (103409917/100000000000000 : ℝ)*(upper5) + (1101649825286951/25000000000000 : ℝ)*(major0) + (1101649825286951/25000000000000 : ℝ)*(major1) + (1101649825286951/25000000000000 : ℝ)*(major2) + (5978223961224273/100000000000000 : ℝ)*(sp0) + (5978246820847167/100000000000000 : ℝ)*(sp1) + (5978246882277261/100000000000000 : ℝ)*(sp2) + (2834939000669233/100000000000000 : ℝ)*(sp3) + (150048759/625000000000 : ℝ)*(sp4) + (11416414407/100000000000000 : ℝ)*(sp7) + (70873760427091/2500000000000 : ℝ)*(f.failure) + (5978247969025713/100000000000000 : ℝ)*(f.sum) + (4548878027607/4525000000000000000000000000 : ℝ)*base65 + (2377811716252003259/226250000000000000000000000000000 : ℝ)*base67 + (1015055524349246741/226250000000000000000000000000000 : ℝ)*base70 + (2203720033073253259/226250000000000000000000000000000 : ℝ)*base71 + (3583928203633/1131250000000000000000000000 : ℝ)*base73 + (671080429485496741/226250000000000000000000000000000 : ℝ)*base76 + (3805650081454503259/226250000000000000000000000000000 : ℝ)*base77 + (3168541772018253259/226250000000000000000000000000000 : ℝ)*base79 + (11434173324159/2262500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (30911/3125000000000000000 : ℝ)*base90 + (30911/3125000000000000000 : ℝ)*base92 + (30911/3125000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (528286742461386218170501701/226250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27605911/6250000000000 : ℝ)*(base19) + (233847579/50000000000000 : ℝ)*(base23) + (9987/19531250000 : ℝ)*(upper3) + (697837/25000000000000 : ℝ)*(lower4) + (28561/50000000000 : ℝ)*(upper5) + (4438596491194837/100000000000000 : ℝ)*(major0) + (4438596491194837/100000000000000 : ℝ)*(major1) + (4438596491194837/100000000000000 : ℝ)*(major2) + (2372387037/25000000000000 : ℝ)*(sp1) + (8969759451/100000000000000 : ℝ)*(sp2) + (6021657351165613/100000000000000 : ℝ)*(sp4) + (752705927490361/12500000000000 : ℝ)*(sp5) + (1505411978427751/25000000000000 : ℝ)*(sp6) + (713883888347937/25000000000000 : ℝ)*(sp7) + (713883888347937/25000000000000 : ℝ)*(f.failure) + (6021657351165613/100000000000000 : ℝ)*(f.sum) + (4626994388633/9050000000000000000000000000 : ℝ)*base66 + (4039283997609424433/905000000000000000000000000000000 : ℝ)*base67 + (11733717032359424433/905000000000000000000000000000000 : ℝ)*base69 + (10111811613339424433/905000000000000000000000000000000 : ℝ)*base71 + (31557267710083/9050000000000000000000000000 : ℝ)*base74 + (14297482677839424433/905000000000000000000000000000000 : ℝ)*base75 + (6122150877934424433/905000000000000000000000000000000 : ℝ)*base77 + (8387822373640575567/905000000000000000000000000000000 : ℝ)*base80 + (17274273265117/9050000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (278177/31250000000000000000 : ℝ)*base90 + (278177/31250000000000000000 : ℝ)*base92 + (278177/31250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1360_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1942979/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7383/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5573/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (699/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (589/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1360_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1360_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1942979/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8017/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9967/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (699/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (589/4000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1360_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1360_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1360_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1942979/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8017/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9967/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (699/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (589/4000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1360_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

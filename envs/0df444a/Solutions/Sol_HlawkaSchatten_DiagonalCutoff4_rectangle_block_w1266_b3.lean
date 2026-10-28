-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1266_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:19:51.822042+00:00
-- url     : https://prove2.me/submissions/47e3b1ed-94a9-40f5-8c4f-253f846b6954

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
theorem support_rectangle_w1266_box_0 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1986016467/10000000000 : ℝ)*x 0 + (5374475711/10000000000 : ℝ)*x 1 + (2687237891/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1986016467/10000000000 : ℝ)^8459 ≤ (11850121480457/100000000000000 : ℝ)^6411 := by
    have hnat : (1986016467 : ℕ)^8459*100000000000000^6411 ≤ 11850121480457^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1986016467 10000000000 11850121480457 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5374475711/10000000000 : ℝ)^8459 ≤ (4407493886899/10000000000000 : ℝ)^6411 := by
    have hnat : (5374475711 : ℕ)^8459*10000000000000^6411 ≤ 4407493886899^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374475711 10000000000 4407493886899 10000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2687237891/5000000000 : ℝ)^8459 ≤ (44074939637249/100000000000000 : ℝ)^6411 := by
    have hnat : (2687237891 : ℕ)^8459*100000000000000^6411 ≤ 44074939637249^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687237891 5000000000 44074939637249 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1986016467/10000000000 : ℝ), (5374475711/10000000000 : ℝ), (2687237891/5000000000 : ℝ)] ![(11850121480457/100000000000000 : ℝ), (4407493886899/10000000000000 : ℝ), (44074939637249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1986016467/10000000000 : ℝ)|^8459 ≤ (11850121480457/100000000000000 : ℝ)^6411
        have hw : |(-1986016467/10000000000 : ℝ)|=(1986016467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5374475711/10000000000 : ℝ)|^8459 ≤ (4407493886899/10000000000000 : ℝ)^6411
        have hw : |(5374475711/10000000000 : ℝ)|=(5374475711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2687237891/5000000000 : ℝ)|^8459 ≤ (44074939637249/100000000000000 : ℝ)^6411
        have hw : |(2687237891/5000000000 : ℝ)|=(2687237891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_box_1 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (529695669/1000000000 : ℝ)*x 0 + (-2091429859/10000000000 : ℝ)*x 1 + (1074895149/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529695669/1000000000 : ℝ)^8459 ≤ (43238080132039/100000000000000 : ℝ)^6411 := by
    have hnat : (529695669 : ℕ)^8459*100000000000000^6411 ≤ 43238080132039^6411*1000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529695669 1000000000 43238080132039 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2091429859/10000000000 : ℝ)^8459 ≤ (1585872576821/12500000000000 : ℝ)^6411 := by
    have hnat : (2091429859 : ℕ)^8459*12500000000000^6411 ≤ 1585872576821^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2091429859 10000000000 1585872576821 12500000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1074895149/2000000000 : ℝ)^8459 ≤ (44074939236889/100000000000000 : ℝ)^6411 := by
    have hnat : (1074895149 : ℕ)^8459*100000000000000^6411 ≤ 44074939236889^6411*2000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074895149 2000000000 44074939236889 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529695669/1000000000 : ℝ), (-2091429859/10000000000 : ℝ), (1074895149/2000000000 : ℝ)] ![(43238080132039/100000000000000 : ℝ), (1585872576821/12500000000000 : ℝ), (44074939236889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529695669/1000000000 : ℝ)|^8459 ≤ (43238080132039/100000000000000 : ℝ)^6411
        have hw : |(529695669/1000000000 : ℝ)|=(529695669/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2091429859/10000000000 : ℝ)|^8459 ≤ (1585872576821/12500000000000 : ℝ)^6411
        have hw : |(-2091429859/10000000000 : ℝ)|=(2091429859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1074895149/2000000000 : ℝ)|^8459 ≤ (44074939236889/100000000000000 : ℝ)^6411
        have hw : |(1074895149/2000000000 : ℝ)|=(1074895149/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_box_2 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2648478397/5000000000 : ℝ)*x 0 + (671809471/1250000000 : ℝ)*x 1 + (-261428711/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2648478397/5000000000 : ℝ)^8459 ≤ (10809520313041/25000000000000 : ℝ)^6411 := by
    have hnat : (2648478397 : ℕ)^8459*25000000000000^6411 ≤ 10809520313041^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2648478397 5000000000 10809520313041 25000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (671809471/1250000000 : ℝ)^8459 ≤ (44074939485761/100000000000000 : ℝ)^6411 := by
    have hnat : (671809471 : ℕ)^8459*100000000000000^6411 ≤ 44074939485761^6411*1250000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671809471 1250000000 44074939485761 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (261428711/1250000000 : ℝ)^8459 ≤ (12686979245881/100000000000000 : ℝ)^6411 := by
    have hnat : (261428711 : ℕ)^8459*100000000000000^6411 ≤ 12686979245881^6411*1250000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261428711 1250000000 12686979245881 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2648478397/5000000000 : ℝ), (671809471/1250000000 : ℝ), (-261428711/1250000000 : ℝ)] ![(10809520313041/25000000000000 : ℝ), (44074939485761/100000000000000 : ℝ), (12686979245881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2648478397/5000000000 : ℝ)|^8459 ≤ (10809520313041/25000000000000 : ℝ)^6411
        have hw : |(2648478397/5000000000 : ℝ)|=(2648478397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(671809471/1250000000 : ℝ)|^8459 ≤ (44074939485761/100000000000000 : ℝ)^6411
        have hw : |(671809471/1250000000 : ℝ)|=(671809471/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-261428711/1250000000 : ℝ)|^8459 ≤ (12686979245881/100000000000000 : ℝ)^6411
        have hw : |(-261428711/1250000000 : ℝ)|=(261428711/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_box_3 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4453786387/10000000000 : ℝ)*x 0 + (4296374721/10000000000 : ℝ)*x 1 + (2148187293/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4453786387/10000000000 : ℝ)^8459 ≤ (6879322179541/20000000000000 : ℝ)^6411 := by
    have hnat : (4453786387 : ℕ)^8459*20000000000000^6411 ≤ 6879322179541^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4453786387 10000000000 6879322179541 20000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4296374721/10000000000 : ℝ)^8459 ≤ (32801695222097/100000000000000 : ℝ)^6411 := by
    have hnat : (4296374721 : ℕ)^8459*100000000000000^6411 ≤ 32801695222097^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4296374721 10000000000 32801695222097 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2148187293/5000000000 : ℝ)^8459 ≤ (32801693862153/100000000000000 : ℝ)^6411 := by
    have hnat : (2148187293 : ℕ)^8459*100000000000000^6411 ≤ 32801693862153^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148187293 5000000000 32801693862153 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4453786387/10000000000 : ℝ), (4296374721/10000000000 : ℝ), (2148187293/5000000000 : ℝ)] ![(6879322179541/20000000000000 : ℝ), (32801695222097/100000000000000 : ℝ), (32801693862153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4453786387/10000000000 : ℝ)|^8459 ≤ (6879322179541/20000000000000 : ℝ)^6411
        have hw : |(4453786387/10000000000 : ℝ)|=(4453786387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4296374721/10000000000 : ℝ)|^8459 ≤ (32801695222097/100000000000000 : ℝ)^6411
        have hw : |(4296374721/10000000000 : ℝ)|=(4296374721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2148187293/5000000000 : ℝ)|^8459 ≤ (32801693862153/100000000000000 : ℝ)^6411
        have hw : |(2148187293/5000000000 : ℝ)|=(2148187293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_box_4 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1116646781/5000000000 : ℝ)*x 0 + (1320631219/2500000000 : ℝ)*x 1 + (2641262411/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1116646781/5000000000 : ℝ)^8459 ≤ (13834578751031/100000000000000 : ℝ)^6411 := by
    have hnat : (1116646781 : ℕ)^8459*100000000000000^6411 ≤ 13834578751031^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1116646781 5000000000 13834578751031 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1320631219/2500000000 : ℝ)^8459 ≤ (5385338863497/12500000000000 : ℝ)^6411 := by
    have hnat : (1320631219 : ℕ)^8459*12500000000000^6411 ≤ 5385338863497^6411*2500000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320631219 2500000000 5385338863497 12500000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2641262411/5000000000 : ℝ)^8459 ≤ (43082710326879/100000000000000 : ℝ)^6411 := by
    have hnat : (2641262411 : ℕ)^8459*100000000000000^6411 ≤ 43082710326879^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641262411 5000000000 43082710326879 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1116646781/5000000000 : ℝ), (1320631219/2500000000 : ℝ), (2641262411/5000000000 : ℝ)] ![(13834578751031/100000000000000 : ℝ), (5385338863497/12500000000000 : ℝ), (43082710326879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1116646781/5000000000 : ℝ)|^8459 ≤ (13834578751031/100000000000000 : ℝ)^6411
        have hw : |(-1116646781/5000000000 : ℝ)|=(1116646781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1320631219/2500000000 : ℝ)|^8459 ≤ (5385338863497/12500000000000 : ℝ)^6411
        have hw : |(1320631219/2500000000 : ℝ)|=(1320631219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2641262411/5000000000 : ℝ)|^8459 ≤ (43082710326879/100000000000000 : ℝ)^6411
        have hw : |(2641262411/5000000000 : ℝ)|=(2641262411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_box_5 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5361741571/10000000000 : ℝ)*x 0 + (-425589677/2000000000 : ℝ)*x 1 + (2641262467/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5361741571/10000000000 : ℝ)^8459 ≤ (43937200795477/100000000000000 : ℝ)^6411 := by
    have hnat : (5361741571 : ℕ)^8459*100000000000000^6411 ≤ 43937200795477^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5361741571 10000000000 43937200795477 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (425589677/2000000000 : ℝ)^8459 ≤ (12980087661201/100000000000000 : ℝ)^6411 := by
    have hnat : (425589677 : ℕ)^8459*100000000000000^6411 ≤ 12980087661201^6411*2000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425589677 2000000000 12980087661201 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2641262467/5000000000 : ℝ)^8459 ≤ (43082711532117/100000000000000 : ℝ)^6411 := by
    have hnat : (2641262467 : ℕ)^8459*100000000000000^6411 ≤ 43082711532117^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641262467 5000000000 43082711532117 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5361741571/10000000000 : ℝ), (-425589677/2000000000 : ℝ), (2641262467/5000000000 : ℝ)] ![(43937200795477/100000000000000 : ℝ), (12980087661201/100000000000000 : ℝ), (43082711532117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5361741571/10000000000 : ℝ)|^8459 ≤ (43937200795477/100000000000000 : ℝ)^6411
        have hw : |(5361741571/10000000000 : ℝ)|=(5361741571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-425589677/2000000000 : ℝ)|^8459 ≤ (12980087661201/100000000000000 : ℝ)^6411
        have hw : |(-425589677/2000000000 : ℝ)|=(425589677/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2641262467/5000000000 : ℝ)|^8459 ≤ (43082711532117/100000000000000 : ℝ)^6411
        have hw : |(2641262467/5000000000 : ℝ)|=(2641262467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_box_6 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5361741583/10000000000 : ℝ)*x 0 + (42260199/80000000 : ℝ)*x 1 + (-2127948447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5361741583/10000000000 : ℝ)^8459 ≤ (21968600462613/50000000000000 : ℝ)^6411 := by
    have hnat : (5361741583 : ℕ)^8459*50000000000000^6411 ≤ 21968600462613^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5361741583 10000000000 21968600462613 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42260199/80000000 : ℝ)^8459 ≤ (8616542179443/20000000000000 : ℝ)^6411 := by
    have hnat : (42260199 : ℕ)^8459*20000000000000^6411 ≤ 8616542179443^6411*80000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42260199 80000000 8616542179443 20000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2127948447/10000000000 : ℝ)^8459 ≤ (6490044080101/50000000000000 : ℝ)^6411 := by
    have hnat : (2127948447 : ℕ)^8459*50000000000000^6411 ≤ 6490044080101^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127948447 10000000000 6490044080101 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5361741583/10000000000 : ℝ), (42260199/80000000 : ℝ), (-2127948447/10000000000 : ℝ)] ![(21968600462613/50000000000000 : ℝ), (8616542179443/20000000000000 : ℝ), (6490044080101/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5361741583/10000000000 : ℝ)|^8459 ≤ (21968600462613/50000000000000 : ℝ)^6411
        have hw : |(5361741583/10000000000 : ℝ)|=(5361741583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42260199/80000000 : ℝ)|^8459 ≤ (8616542179443/20000000000000 : ℝ)^6411
        have hw : |(42260199/80000000 : ℝ)|=(42260199/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2127948447/10000000000 : ℝ)|^8459 ≤ (6490044080101/50000000000000 : ℝ)^6411
        have hw : |(-2127948447/10000000000 : ℝ)|=(2127948447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_box_7 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4240790283/10000000000 : ℝ)*x 0 + (2201426401/5000000000 : ℝ)*x 1 + (17611411/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4240790283/10000000000 : ℝ)^8459 ≤ (4030364608747/12500000000000 : ℝ)^6411 := by
    have hnat : (4240790283 : ℕ)^8459*12500000000000^6411 ≤ 4030364608747^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4240790283 10000000000 4030364608747 12500000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2201426401/5000000000 : ℝ)^8459 ≤ (16939270908313/50000000000000 : ℝ)^6411 := by
    have hnat : (2201426401 : ℕ)^8459*50000000000000^6411 ≤ 16939270908313^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2201426401 5000000000 16939270908313 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17611411/40000000 : ℝ)^8459 ≤ (16939270644341/50000000000000 : ℝ)^6411 := by
    have hnat : (17611411 : ℕ)^8459*50000000000000^6411 ≤ 16939270644341^6411*40000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17611411 40000000 16939270644341 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4240790283/10000000000 : ℝ), (2201426401/5000000000 : ℝ), (17611411/40000000 : ℝ)] ![(4030364608747/12500000000000 : ℝ), (16939270908313/50000000000000 : ℝ), (16939270644341/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4240790283/10000000000 : ℝ)|^8459 ≤ (4030364608747/12500000000000 : ℝ)^6411
        have hw : |(4240790283/10000000000 : ℝ)|=(4240790283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2201426401/5000000000 : ℝ)|^8459 ≤ (16939270908313/50000000000000 : ℝ)^6411
        have hw : |(2201426401/5000000000 : ℝ)|=(2201426401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(17611411/40000000 : ℝ)|^8459 ≤ (16939270644341/50000000000000 : ℝ)^6411
        have hw : |(17611411/40000000 : ℝ)|=(17611411/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_box_8 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2181452661/10000000000 : ℝ)*x 0 + (1043952161/2000000000 : ℝ)*x 1 + (5384088109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2181452661/10000000000 : ℝ)^8459 ≤ (13412431361841/100000000000000 : ℝ)^6411 := by
    have hnat : (2181452661 : ℕ)^8459*100000000000000^6411 ≤ 13412431361841^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181452661 10000000000 13412431361841 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043952161/2000000000 : ℝ)^8459 ≤ (5301073591547/12500000000000 : ℝ)^6411 := by
    have hnat : (1043952161 : ℕ)^8459*12500000000000^6411 ≤ 5301073591547^6411*2000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043952161 2000000000 5301073591547 12500000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5384088109/10000000000 : ℝ)^8459 ≤ (2761186243117/6250000000000 : ℝ)^6411 := by
    have hnat : (5384088109 : ℕ)^8459*6250000000000^6411 ≤ 2761186243117^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384088109 10000000000 2761186243117 6250000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2181452661/10000000000 : ℝ), (1043952161/2000000000 : ℝ), (5384088109/10000000000 : ℝ)] ![(13412431361841/100000000000000 : ℝ), (5301073591547/12500000000000 : ℝ), (2761186243117/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2181452661/10000000000 : ℝ)|^8459 ≤ (13412431361841/100000000000000 : ℝ)^6411
        have hw : |(-2181452661/10000000000 : ℝ)|=(2181452661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043952161/2000000000 : ℝ)|^8459 ≤ (5301073591547/12500000000000 : ℝ)^6411
        have hw : |(1043952161/2000000000 : ℝ)|=(1043952161/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5384088109/10000000000 : ℝ)|^8459 ≤ (2761186243117/6250000000000 : ℝ)^6411
        have hw : |(5384088109/10000000000 : ℝ)|=(5384088109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_box_9 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (211607251/400000000 : ℝ)*x 0 + (-417509039/2000000000 : ℝ)*x 1 + (2692044161/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211607251/400000000 : ℝ)^8459 ≤ (43165120881337/100000000000000 : ℝ)^6411 := by
    have hnat : (211607251 : ℕ)^8459*100000000000000^6411 ≤ 43165120881337^6411*400000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211607251 400000000 43165120881337 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (417509039/2000000000 : ℝ)^8459 ≤ (1265589691073/10000000000000 : ℝ)^6411 := by
    have hnat : (417509039 : ℕ)^8459*10000000000000^6411 ≤ 1265589691073^6411*2000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417509039 2000000000 1265589691073 10000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2692044161/5000000000 : ℝ)^8459 ≤ (22089491097981/50000000000000 : ℝ)^6411 := by
    have hnat : (2692044161 : ℕ)^8459*50000000000000^6411 ≤ 22089491097981^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692044161 5000000000 22089491097981 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211607251/400000000 : ℝ), (-417509039/2000000000 : ℝ), (2692044161/5000000000 : ℝ)] ![(43165120881337/100000000000000 : ℝ), (1265589691073/10000000000000 : ℝ), (22089491097981/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211607251/400000000 : ℝ)|^8459 ≤ (43165120881337/100000000000000 : ℝ)^6411
        have hw : |(211607251/400000000 : ℝ)|=(211607251/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-417509039/2000000000 : ℝ)|^8459 ≤ (1265589691073/10000000000000 : ℝ)^6411
        have hw : |(-417509039/2000000000 : ℝ)|=(417509039/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2692044161/5000000000 : ℝ)|^8459 ≤ (22089491097981/50000000000000 : ℝ)^6411
        have hw : |(2692044161/5000000000 : ℝ)|=(2692044161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_box_10 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5290180729/10000000000 : ℝ)*x 0 + (2692044573/5000000000 : ℝ)*x 1 + (-2087544813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290180729/10000000000 : ℝ)^8459 ≤ (10791278750771/25000000000000 : ℝ)^6411 := by
    have hnat : (5290180729 : ℕ)^8459*25000000000000^6411 ≤ 10791278750771^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290180729 10000000000 10791278750771 25000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2692044573/5000000000 : ℝ)^8459 ≤ (44178991117177/100000000000000 : ℝ)^6411 := by
    have hnat : (2692044573 : ℕ)^8459*100000000000000^6411 ≤ 44178991117177^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692044573 5000000000 44178991117177 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2087544813/10000000000 : ℝ)^8459 ≤ (1265589385501/10000000000000 : ℝ)^6411 := by
    have hnat : (2087544813 : ℕ)^8459*10000000000000^6411 ≤ 1265589385501^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087544813 10000000000 1265589385501 10000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290180729/10000000000 : ℝ), (2692044573/5000000000 : ℝ), (-2087544813/10000000000 : ℝ)] ![(10791278750771/25000000000000 : ℝ), (44178991117177/100000000000000 : ℝ), (1265589385501/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290180729/10000000000 : ℝ)|^8459 ≤ (10791278750771/25000000000000 : ℝ)^6411
        have hw : |(5290180729/10000000000 : ℝ)|=(5290180729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2692044573/5000000000 : ℝ)|^8459 ≤ (44178991117177/100000000000000 : ℝ)^6411
        have hw : |(2692044573/5000000000 : ℝ)|=(2692044573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2087544813/10000000000 : ℝ)|^8459 ≤ (1265589385501/10000000000000 : ℝ)^6411
        have hw : |(-2087544813/10000000000 : ℝ)|=(2087544813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_box_11 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (179031239/400000000 : ℝ)*x 0 + (2142618561/5000000000 : ℝ)*x 1 + (1071309139/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (179031239/400000000 : ℝ)^8459 ≤ (2163807193367/6250000000000 : ℝ)^6411 := by
    have hnat : (179031239 : ℕ)^8459*6250000000000^6411 ≤ 2163807193367^6411*400000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179031239 400000000 2163807193367 6250000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2142618561/5000000000 : ℝ)^8459 ≤ (6537909059049/20000000000000 : ℝ)^6411 := by
    have hnat : (2142618561 : ℕ)^8459*20000000000000^6411 ≤ 6537909059049^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142618561 5000000000 6537909059049 20000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1071309139/2500000000 : ℝ)^8459 ≤ (16344769799139/50000000000000 : ℝ)^6411 := by
    have hnat : (1071309139 : ℕ)^8459*50000000000000^6411 ≤ 16344769799139^6411*2500000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071309139 2500000000 16344769799139 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(179031239/400000000 : ℝ), (2142618561/5000000000 : ℝ), (1071309139/2500000000 : ℝ)] ![(2163807193367/6250000000000 : ℝ), (6537909059049/20000000000000 : ℝ), (16344769799139/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(179031239/400000000 : ℝ)|^8459 ≤ (2163807193367/6250000000000 : ℝ)^6411
        have hw : |(179031239/400000000 : ℝ)|=(179031239/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2142618561/5000000000 : ℝ)|^8459 ≤ (6537909059049/20000000000000 : ℝ)^6411
        have hw : |(2142618561/5000000000 : ℝ)|=(2142618561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1071309139/2500000000 : ℝ)|^8459 ≤ (16344769799139/50000000000000 : ℝ)^6411
        have hw : |(1071309139/2500000000 : ℝ)|=(1071309139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_box_12 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2038103343/10000000000 : ℝ)*x 0 + (217441887/400000000 : ℝ)*x 1 + (2637218877/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2038103343/10000000000 : ℝ)^8459 ≤ (6130951263367/50000000000000 : ℝ)^6411 := by
    have hnat : (2038103343 : ℕ)^8459*50000000000000^6411 ≤ 6130951263367^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2038103343 10000000000 6130951263367 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217441887/400000000 : ℝ)^8459 ≤ (11185597802979/25000000000000 : ℝ)^6411 := by
    have hnat : (217441887 : ℕ)^8459*25000000000000^6411 ≤ 11185597802979^6411*400000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217441887 400000000 11185597802979 25000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2637218877/5000000000 : ℝ)^8459 ≤ (21497853128599/50000000000000 : ℝ)^6411 := by
    have hnat : (2637218877 : ℕ)^8459*50000000000000^6411 ≤ 21497853128599^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637218877 5000000000 21497853128599 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2038103343/10000000000 : ℝ), (217441887/400000000 : ℝ), (2637218877/5000000000 : ℝ)] ![(6130951263367/50000000000000 : ℝ), (11185597802979/25000000000000 : ℝ), (21497853128599/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2038103343/10000000000 : ℝ)|^8459 ≤ (6130951263367/50000000000000 : ℝ)^6411
        have hw : |(-2038103343/10000000000 : ℝ)|=(2038103343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(217441887/400000000 : ℝ)|^8459 ≤ (11185597802979/25000000000000 : ℝ)^6411
        have hw : |(217441887/400000000 : ℝ)|=(217441887/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2637218877/5000000000 : ℝ)|^8459 ≤ (21497853128599/50000000000000 : ℝ)^6411
        have hw : |(2637218877/5000000000 : ℝ)|=(2637218877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_box_13 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5367438073/10000000000 : ℝ)*x 0 + (-2131104781/10000000000 : ℝ)*x 1 + (5274437041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5367438073/10000000000 : ℝ)^8459 ≤ (1759952150809/4000000000000 : ℝ)^6411 := by
    have hnat : (5367438073 : ℕ)^8459*4000000000000^6411 ≤ 1759952150809^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5367438073 10000000000 1759952150809 4000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2131104781/10000000000 : ℝ)^8459 ≤ (1625687203629/12500000000000 : ℝ)^6411 := by
    have hnat : (2131104781 : ℕ)^8459*12500000000000^6411 ≤ 1625687203629^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2131104781 10000000000 1625687203629 12500000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5274437041/10000000000 : ℝ)^8459 ≤ (42995698588323/100000000000000 : ℝ)^6411 := by
    have hnat : (5274437041 : ℕ)^8459*100000000000000^6411 ≤ 42995698588323^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274437041 10000000000 42995698588323 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5367438073/10000000000 : ℝ), (-2131104781/10000000000 : ℝ), (5274437041/10000000000 : ℝ)] ![(1759952150809/4000000000000 : ℝ), (1625687203629/12500000000000 : ℝ), (42995698588323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5367438073/10000000000 : ℝ)|^8459 ≤ (1759952150809/4000000000000 : ℝ)^6411
        have hw : |(5367438073/10000000000 : ℝ)|=(5367438073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2131104781/10000000000 : ℝ)|^8459 ≤ (1625687203629/12500000000000 : ℝ)^6411
        have hw : |(-2131104781/10000000000 : ℝ)|=(2131104781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5274437041/10000000000 : ℝ)|^8459 ≤ (42995698588323/100000000000000 : ℝ)^6411
        have hw : |(5274437041/10000000000 : ℝ)|=(5274437041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_box_14 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5367437847/10000000000 : ℝ)*x 0 + (5274437297/10000000000 : ℝ)*x 1 + (-1065552371/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5367437847/10000000000 : ℝ)^8459 ≤ (43998801325807/100000000000000 : ℝ)^6411 := by
    have hnat : (5367437847 : ℕ)^8459*100000000000000^6411 ≤ 43998801325807^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5367437847 10000000000 43998801325807 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5274437297/10000000000 : ℝ)^8459 ≤ (10748925335451/25000000000000 : ℝ)^6411 := by
    have hnat : (5274437297 : ℕ)^8459*25000000000000^6411 ≤ 10748925335451^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274437297 10000000000 10748925335451 25000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1065552371/5000000000 : ℝ)^8459 ≤ (3251374328749/25000000000000 : ℝ)^6411 := by
    have hnat : (1065552371 : ℕ)^8459*25000000000000^6411 ≤ 3251374328749^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065552371 5000000000 3251374328749 25000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5367437847/10000000000 : ℝ), (5274437297/10000000000 : ℝ), (-1065552371/5000000000 : ℝ)] ![(43998801325807/100000000000000 : ℝ), (10748925335451/25000000000000 : ℝ), (3251374328749/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5367437847/10000000000 : ℝ)|^8459 ≤ (43998801325807/100000000000000 : ℝ)^6411
        have hw : |(5367437847/10000000000 : ℝ)|=(5367437847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5274437297/10000000000 : ℝ)|^8459 ≤ (10748925335451/25000000000000 : ℝ)^6411
        have hw : |(5274437297/10000000000 : ℝ)|=(5274437297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1065552371/5000000000 : ℝ)|^8459 ≤ (3251374328749/25000000000000 : ℝ)^6411
        have hw : |(-1065552371/5000000000 : ℝ)|=(1065552371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_box_15 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2110912047/5000000000 : ℝ)*x 0 + (4412212889/10000000000 : ℝ)*x 1 + (275763327/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2110912047/5000000000 : ℝ)^8459 ≤ (32052787071697/100000000000000 : ℝ)^6411 := by
    have hnat : (2110912047 : ℕ)^8459*100000000000000^6411 ≤ 32052787071697^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110912047 5000000000 32052787071697 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4412212889/10000000000 : ℝ)^8459 ≤ (8493401178719/25000000000000 : ℝ)^6411 := by
    have hnat : (4412212889 : ℕ)^8459*25000000000000^6411 ≤ 8493401178719^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4412212889 10000000000 8493401178719 25000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (275763327/625000000 : ℝ)^8459 ≤ (16986804099817/50000000000000 : ℝ)^6411 := by
    have hnat : (275763327 : ℕ)^8459*50000000000000^6411 ≤ 16986804099817^6411*625000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275763327 625000000 16986804099817 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2110912047/5000000000 : ℝ), (4412212889/10000000000 : ℝ), (275763327/625000000 : ℝ)] ![(32052787071697/100000000000000 : ℝ), (8493401178719/25000000000000 : ℝ), (16986804099817/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2110912047/5000000000 : ℝ)|^8459 ≤ (32052787071697/100000000000000 : ℝ)^6411
        have hw : |(2110912047/5000000000 : ℝ)|=(2110912047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4412212889/10000000000 : ℝ)|^8459 ≤ (8493401178719/25000000000000 : ℝ)^6411
        have hw : |(4412212889/10000000000 : ℝ)|=(4412212889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(275763327/625000000 : ℝ)|^8459 ≤ (16986804099817/50000000000000 : ℝ)^6411
        have hw : |(275763327/625000000 : ℝ)|=(275763327/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1266_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30379753/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3529/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2877/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62251/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59397/100000 : ℝ) ∧ (80179/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (41699/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3529/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2877/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3529/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2877/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3529/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2877/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3529/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2877/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3529/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2877/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3529/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2877/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2877/25000 : ℝ) ^ (4229/1024 : ℝ) ≤ (3311154469023401/25000000000000000000 : ℝ) := by
    have hpowers : (2877/25000 : ℝ)^4229 ≤ (3311154469023401/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2877 : ℕ)^4229*25000000000000000000^1024 ≤ 3311154469023401^1024*25000^4229 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2877 25000 3311154469023401 25000000000000000000 4229 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2877/25000 : ℝ)) (X := (3311154469023401/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3529/25000 : ℝ) ^ (4229/1024 : ℝ) ≤ (15394966943576819/50000000000000000000 : ℝ) := by
    have hpowers : (3529/25000 : ℝ)^4229 ≤ (15394966943576819/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3529 : ℕ)^4229*50000000000000000000^1024 ≤ 15394966943576819^1024*25000^4229 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3529 25000 15394966943576819 50000000000000000000 4229 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3529/25000 : ℝ)) (X := (15394966943576819/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503311154469023401/12500000000000000000 : ℝ) ≤ (10000641339681643/10000000000000000 : ℝ) ^ (4229/1024 : ℝ) := by
    have hpowers : (12503311154469023401/12500000000000000000 : ℝ)^1024 ≤ (10000641339681643/10000000000000000 : ℝ)^4229 := by
      have hnat : (12503311154469023401 : ℕ)^1024*10000000000000000^4229 ≤ 10000641339681643^4229*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503311154469023401 12500000000000000000 10000641339681643 10000000000000000 1024 4229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000641339681643/10000000000000000 : ℝ)) (X := (12503311154469023401/12500000000000000000 : ℝ)) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022017275881623621/50000000000000000000 : ℝ) ≤ (1000106606429343/1000000000000000 : ℝ) ^ (4229/1024 : ℝ) := by
    have hpowers : (50022017275881623621/50000000000000000000 : ℝ)^1024 ≤ (1000106606429343/1000000000000000 : ℝ)^4229 := by
      have hnat : (50022017275881623621 : ℕ)^1024*1000000000000000^4229 ≤ 1000106606429343^4229*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022017275881623621 50000000000000000000 1000106606429343 1000000000000000 1024 4229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000106606429343/1000000000000000 : ℝ)) (X := (50022017275881623621/50000000000000000000 : ℝ)) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015394966943576819/25000000000000000000 : ℝ) ≤ (10001490788905217/10000000000000000 : ℝ) ^ (4229/1024 : ℝ) := by
    have hpowers : (25015394966943576819/25000000000000000000 : ℝ)^1024 ≤ (10001490788905217/10000000000000000 : ℝ)^4229 := by
      have hnat : (25015394966943576819 : ℕ)^1024*10000000000000000^4229 ≤ 10001490788905217^4229*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015394966943576819 25000000000000000000 10001490788905217 10000000000000000 1024 4229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001490788905217/10000000000000000 : ℝ)) (X := (25015394966943576819/25000000000000000000 : ℝ)) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3311154469023401/25000000000000000000 : ℝ) ≤ ((3258987144028104419/3260000000000000000 : ℝ)+2*(424724611787/260800000000000 : ℝ)*(2877/25000 : ℝ))^(4229/1024 : ℝ) := by
    rw [show (3258987144028104419/3260000000000000000 : ℝ)+2*(424724611787/260800000000000 : ℝ)*(2877/25000 : ℝ)=(10000641339681643/10000000000000000 : ℝ) by norm_num, show 1+2*(3311154469023401/25000000000000000000 : ℝ)=(12503311154469023401/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15394966943576819/50000000000000000000 : ℝ)+(3311154469023401/25000000000000000000 : ℝ) ≤ ((3258987144028104419/3260000000000000000 : ℝ)+(424724611787/260800000000000 : ℝ)*((3529/25000 : ℝ)+(2877/25000 : ℝ)))^(4229/1024 : ℝ) := by
    rw [show (3258987144028104419/3260000000000000000 : ℝ)+(424724611787/260800000000000 : ℝ)*((3529/25000 : ℝ)+(2877/25000 : ℝ))=(1000106606429343/1000000000000000 : ℝ) by norm_num, show 1+(15394966943576819/50000000000000000000 : ℝ)+(3311154469023401/25000000000000000000 : ℝ)=(50022017275881623621/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15394966943576819/50000000000000000000 : ℝ) ≤ ((3258987144028104419/3260000000000000000 : ℝ)+2*(424724611787/260800000000000 : ℝ)*(3529/25000 : ℝ))^(4229/1024 : ℝ) := by
    rw [show (3258987144028104419/3260000000000000000 : ℝ)+2*(424724611787/260800000000000 : ℝ)*(3529/25000 : ℝ)=(10001490788905217/10000000000000000 : ℝ) by norm_num, show 1+2*(15394966943576819/50000000000000000000 : ℝ)=(25015394966943576819/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3258987144028104419/3260000000000000000 : ℝ)*(X 1 0+X 2 0)+(424724611787/260800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4229/1024 : ℝ)) (lo := (2877/25000 : ℝ)) (hi := (3529/25000 : ℝ)) (c := (3258987144028104419/3260000000000000000 : ℝ)) (alpha := (424724611787/260800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3258987144028104419/3260000000000000000 : ℝ)*(X 0 1+X 2 1)+(424724611787/260800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4229/1024 : ℝ)) (lo := (2877/25000 : ℝ)) (hi := (3529/25000 : ℝ)) (c := (3258987144028104419/3260000000000000000 : ℝ)) (alpha := (424724611787/260800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3258987144028104419/3260000000000000000 : ℝ)*(X 0 2+X 1 2)+(424724611787/260800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4229/1024 : ℝ)) (lo := (2877/25000 : ℝ)) (hi := (3529/25000 : ℝ)) (c := (3258987144028104419/3260000000000000000 : ℝ)) (alpha := (424724611787/260800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1986016467/10000000000 : ℝ)*X 0 0+(5374475711/10000000000 : ℝ)*X 0 1+(2687237891/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((529695669/1000000000 : ℝ)*X 1 0+(-2091429859/10000000000 : ℝ)*X 1 1+(1074895149/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2648478397/5000000000 : ℝ)*X 2 0+(671809471/1250000000 : ℝ)*X 2 1+(-261428711/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4453786387/10000000000 : ℝ)*X 0 0+(4296374721/10000000000 : ℝ)*X 0 1+(2148187293/5000000000 : ℝ)*X 0 2+(4453786387/10000000000 : ℝ)*X 1 0+(4296374721/10000000000 : ℝ)*X 1 1+(2148187293/5000000000 : ℝ)*X 1 2+(4453786387/10000000000 : ℝ)*X 2 0+(4296374721/10000000000 : ℝ)*X 2 1+(2148187293/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1116646781/5000000000 : ℝ)*X 0 0+(1320631219/2500000000 : ℝ)*X 0 1+(2641262411/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5361741571/10000000000 : ℝ)*X 1 0+(-425589677/2000000000 : ℝ)*X 1 1+(2641262467/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5361741583/10000000000 : ℝ)*X 2 0+(42260199/80000000 : ℝ)*X 2 1+(-2127948447/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4240790283/10000000000 : ℝ)*X 0 0+(2201426401/5000000000 : ℝ)*X 0 1+(17611411/40000000 : ℝ)*X 0 2+(4240790283/10000000000 : ℝ)*X 1 0+(2201426401/5000000000 : ℝ)*X 1 1+(17611411/40000000 : ℝ)*X 1 2+(4240790283/10000000000 : ℝ)*X 2 0+(2201426401/5000000000 : ℝ)*X 2 1+(17611411/40000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2181452661/10000000000 : ℝ)*X 0 0+(1043952161/2000000000 : ℝ)*X 0 1+(5384088109/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((211607251/400000000 : ℝ)*X 1 0+(-417509039/2000000000 : ℝ)*X 1 1+(2692044161/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5290180729/10000000000 : ℝ)*X 2 0+(2692044573/5000000000 : ℝ)*X 2 1+(-2087544813/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((179031239/400000000 : ℝ)*X 0 0+(2142618561/5000000000 : ℝ)*X 0 1+(1071309139/2500000000 : ℝ)*X 0 2+(179031239/400000000 : ℝ)*X 1 0+(2142618561/5000000000 : ℝ)*X 1 1+(1071309139/2500000000 : ℝ)*X 1 2+(179031239/400000000 : ℝ)*X 2 0+(2142618561/5000000000 : ℝ)*X 2 1+(1071309139/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2038103343/10000000000 : ℝ)*X 0 0+(217441887/400000000 : ℝ)*X 0 1+(2637218877/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5367438073/10000000000 : ℝ)*X 1 0+(-2131104781/10000000000 : ℝ)*X 1 1+(5274437041/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5367437847/10000000000 : ℝ)*X 2 0+(5274437297/10000000000 : ℝ)*X 2 1+(-1065552371/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2110912047/5000000000 : ℝ)*X 0 0+(4412212889/10000000000 : ℝ)*X 0 1+(275763327/625000000 : ℝ)*X 0 2+(2110912047/5000000000 : ℝ)*X 1 0+(4412212889/10000000000 : ℝ)*X 1 1+(275763327/625000000 : ℝ)*X 1 2+(2110912047/5000000000 : ℝ)*X 2 0+(4412212889/10000000000 : ℝ)*X 2 1+(275763327/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62251/100000 : ℝ) ≤ (-101465763975456233017236470834739/163000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (119721/12500000000000 : ℝ)*(upper1) + (15521/160000000000 : ℝ)*(upper2) + (9075849/25000000000000 : ℝ)*(upper3) + (2025859/100000000000000 : ℝ)*(lower4) + (4022971501410809/100000000000000 : ℝ)*(major0) + (4022971501410809/100000000000000 : ℝ)*(major1) + (4022971501410809/100000000000000 : ℝ)*(major2) + (58925337/100000000000000 : ℝ)*(sp2) + (1117208613/100000000000000 : ℝ)*(sp3) + (2709118473396689/50000000000000 : ℝ)*(sp4) + (2709102808855639/50000000000000 : ℝ)*(sp5) + (5418236887868041/100000000000000 : ℝ)*(sp6) + (1324227291902183/50000000000000 : ℝ)*(sp7) + (313290821/1000000000000 : ℝ)*(sp13) + (132422785050649/5000000000000 : ℝ)*(f.failure) + (2709118473396689/50000000000000 : ℝ)*(f.sum) + (80814595981763/13040000000000000000000000000 : ℝ)*base65 + (6701968854680302471/326000000000000000000000000000000 : ℝ)*base67 + (3352981351554302471/326000000000000000000000000000000 : ℝ)*base69 + (13641406578916302471/326000000000000000000000000000000 : ℝ)*base71 + (58920370755683/13040000000000000000000000000 : ℝ)*base73 + (5234704521818302471/326000000000000000000000000000000 : ℝ)*base75 + (928577752498302471/326000000000000000000000000000000 : ℝ)*base77 + (6568086339142302471/326000000000000000000000000000000 : ℝ)*base79 + (328665321490717/13040000000000000000000000000 : ℝ)*base82 + (109697/100000000000000000000 : ℝ)*base89 + (109697/100000000000000000000 : ℝ)*base91 + (109697/100000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (59397/100000 : ℝ) ≤ (484104502984759421775157595037/815000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4465547/20000000000000 : ℝ)*(lower1) + (19750303/50000000000000 : ℝ)*(lower2) + (39288073/50000000000000 : ℝ)*(upper4) + (20445845615459/500000000000 : ℝ)*(major0) + (20445845615459/500000000000 : ℝ)*(major1) + (20445845615459/500000000000 : ℝ)*(major2) + (5466501876582381/100000000000000 : ℝ)*(sp0) + (5466457607729791/100000000000000 : ℝ)*(sp1) + (2733248970476707/50000000000000 : ℝ)*(sp2) + (1346017133040983/50000000000000 : ℝ)*(sp3) + (2368473567/50000000000000 : ℝ)*(sp6) + (1527027873/100000000000000 : ℝ)*(sp7) + (801318167/100000000000000 : ℝ)*(sp8) + (22535085379/50000000000000 : ℝ)*(sp9) + (1346017896554919/50000000000000 : ℝ)*(f.failure) + (5466502677900549/100000000000000 : ℝ)*(f.sum) + (1983324359197/326000000000000000000000000 : ℝ)*base66 + (3357241311485821/1630000000000000000000000000000 : ℝ)*base67 + (8472562710295821/1630000000000000000000000000000 : ℝ)*base69 + (23195522556804179/1630000000000000000000000000000 : ℝ)*base72 + (152899482913/326000000000000000000000000 : ℝ)*base74 + (9220002078084179/1630000000000000000000000000000 : ℝ)*base76 + (1594561298455821/1630000000000000000000000000000 : ℝ)*base77 + (5869498573605821/1630000000000000000000000000000 : ℝ)*base79 + (1484989841131/326000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (9844993/1000000000000000000000 : ℝ)*base90 + (9844993/1000000000000000000000 : ℝ)*base92 + (9844993/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (80179/100000 : ℝ) ≤ (65348303564514509499849892330917/81500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (69129861/100000000000000 : ℝ)*(lower3) + (68880123/50000000000000 : ℝ)*(upper4) + (27587921/10000000000000 : ℝ)*(lower5) + (2277824259359619/50000000000000 : ℝ)*(major0) + (2277824259359619/50000000000000 : ℝ)*(major1) + (2277824259359619/50000000000000 : ℝ)*(major2) + (21595742453/100000000000000 : ℝ)*(sp0) + (228355166701/100000000000000 : ℝ)*(sp1) + (46099402911/5000000000000 : ℝ)*(sp2) + (61376210397/25000000000000 : ℝ)*(sp3) + (3042706726462827/50000000000000 : ℝ)*(sp8) + (6085206693501407/100000000000000 : ℝ)*(sp9) + (190141033144059/3125000000000 : ℝ)*(sp10) + (2998889161407501/100000000000000 : ℝ)*(sp11) + (2999134666249089/100000000000000 : ℝ)*(f.failure) + (6085435048668107/100000000000000 : ℝ)*(f.sum) + (32299292823567/6520000000000000000000000000 : ℝ)*base66 + (1558899495219468861/163000000000000000000000000000000 : ℝ)*base67 + (581337796840468861/163000000000000000000000000000000 : ℝ)*base69 + (66942378529531139/163000000000000000000000000000000 : ℝ)*base72 + (32749981989233/6520000000000000000000000000 : ℝ)*base73 + (1273237789819468861/163000000000000000000000000000000 : ℝ)*base75 + (1015987010499468861/163000000000000000000000000000000 : ℝ)*base77 + (217154707745531139/163000000000000000000000000000000 : ℝ)*base80 + (17459939957247/6520000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (295017/2000000000000000000000 : ℝ)*base89 + (295017/2000000000000000000000 : ℝ)*base91 + (295017/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-41699/50000 : ℝ) ≤ (-67967302245402030580114043877567/81500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10466377/10000000000000 : ℝ)*(upper3) + (24712059/25000000000000 : ℝ)*(lower4) + (104871501/50000000000000 : ℝ)*(upper5) + (4591307637644919/100000000000000 : ℝ)*(major0) + (4591307637644919/100000000000000 : ℝ)*(major1) + (4591307637644919/100000000000000 : ℝ)*(major2) + (228701223/500000000000 : ℝ)*(sp4) + (180159593563/25000000000000 : ℝ)*(sp5) + (324349142631/50000000000000 : ℝ)*(sp6) + (190398045603/50000000000000 : ℝ)*(sp7) + (1237551554911917/20000000000000 : ℝ)*(sp12) + (6187082876429933/100000000000000 : ℝ)*(sp13) + (6187154816518923/100000000000000 : ℝ)*(sp14) + (302222945202037/10000000000000 : ℝ)*(sp15) + (377826281013947/12500000000000 : ℝ)*(f.failure) + (1237560702960837/20000000000000 : ℝ)*(f.sum) + (25793485632333/13040000000000000000000000000 : ℝ)*base65 + (6082294878412040439/326000000000000000000000000000000 : ℝ)*base68 + (4031358955650040439/326000000000000000000000000000000 : ℝ)*base70 + (3128341243975959561/326000000000000000000000000000000 : ℝ)*base71 + (153995869394707/13040000000000000000000000000 : ℝ)*base74 + (175403027556040439/326000000000000000000000000000000 : ℝ)*base76 + (2302120961500040439/326000000000000000000000000000000 : ℝ)*base78 + (3736813356768040439/326000000000000000000000000000000 : ℝ)*base80 + (24497140874147/13040000000000000000000000000 : ℝ)*base82 + (1915091/250000000000000000000 : ℝ)*base89 + (1915091/250000000000000000000 : ℝ)*base91 + (1915091/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1266_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30379753/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3529/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2877/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62251/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59397/100000 : ℝ) else (80179/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41699/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1266_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1266_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30379753/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3529/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2877/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62251/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59397/100000 : ℝ) else (80179/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41699/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1266_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30379753/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3529/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2877/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62251/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59397/100000 : ℝ) else (80179/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41699/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1266_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

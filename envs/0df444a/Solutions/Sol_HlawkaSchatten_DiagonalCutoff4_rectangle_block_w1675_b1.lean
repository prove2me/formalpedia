-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1675_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:27:50.751414+00:00
-- url     : https://prove2.me/submissions/08aa7561-dd04-42dc-9b7b-eac44ded0b99

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
theorem support_rectangle_w1675_s3_0 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-96832979/625000000 : ℝ)*x 0 + (5493651017/10000000000 : ℝ)*x 1 + (5132263711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (96832979/625000000 : ℝ)^5023 ≤ (1922197932903/20000000000000 : ℝ)^3999 := by
    have hnat : (96832979 : ℕ)^5023*20000000000000^3999 ≤ 1922197932903^3999*625000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96832979 625000000 1922197932903 20000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5493651017/10000000000 : ℝ)^5023 ≤ (47124727046421/100000000000000 : ℝ)^3999 := by
    have hnat : (5493651017 : ℕ)^5023*100000000000000^3999 ≤ 47124727046421^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5493651017 10000000000 47124727046421 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5132263711/10000000000 : ℝ)^5023 ≤ (8652856653921/20000000000000 : ℝ)^3999 := by
    have hnat : (5132263711 : ℕ)^5023*20000000000000^3999 ≤ 8652856653921^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5132263711 10000000000 8652856653921 20000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-96832979/625000000 : ℝ), (5493651017/10000000000 : ℝ), (5132263711/10000000000 : ℝ)] ![(1922197932903/20000000000000 : ℝ), (47124727046421/100000000000000 : ℝ), (8652856653921/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-96832979/625000000 : ℝ)|^5023 ≤ (1922197932903/20000000000000 : ℝ)^3999
        have hw : |(-96832979/625000000 : ℝ)|=(96832979/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5493651017/10000000000 : ℝ)|^5023 ≤ (47124727046421/100000000000000 : ℝ)^3999
        have hw : |(5493651017/10000000000 : ℝ)|=(5493651017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5132263711/10000000000 : ℝ)|^5023 ≤ (8652856653921/20000000000000 : ℝ)^3999
        have hw : |(5132263711/10000000000 : ℝ)|=(5132263711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_s3_1 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5355199371/10000000000 : ℝ)*x 0 + (-1737322157/10000000000 : ℝ)*x 1 + (5132263211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355199371/10000000000 : ℝ)^5023 ≤ (1825512611037/4000000000000 : ℝ)^3999 := by
    have hnat : (5355199371 : ℕ)^5023*4000000000000^3999 ≤ 1825512611037^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355199371 10000000000 1825512611037 4000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1737322157/10000000000 : ℝ)^5023 ≤ (11097906726659/100000000000000 : ℝ)^3999 := by
    have hnat : (1737322157 : ℕ)^5023*100000000000000^3999 ≤ 11097906726659^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1737322157 10000000000 11097906726659 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5132263211/10000000000 : ℝ)^5023 ≤ (43264277975381/100000000000000 : ℝ)^3999 := by
    have hnat : (5132263211 : ℕ)^5023*100000000000000^3999 ≤ 43264277975381^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5132263211 10000000000 43264277975381 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355199371/10000000000 : ℝ), (-1737322157/10000000000 : ℝ), (5132263211/10000000000 : ℝ)] ![(1825512611037/4000000000000 : ℝ), (11097906726659/100000000000000 : ℝ), (43264277975381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355199371/10000000000 : ℝ)|^5023 ≤ (1825512611037/4000000000000 : ℝ)^3999
        have hw : |(5355199371/10000000000 : ℝ)|=(5355199371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1737322157/10000000000 : ℝ)|^5023 ≤ (11097906726659/100000000000000 : ℝ)^3999
        have hw : |(-1737322157/10000000000 : ℝ)|=(1737322157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5132263211/10000000000 : ℝ)|^5023 ≤ (43264277975381/100000000000000 : ℝ)^3999
        have hw : |(5132263211/10000000000 : ℝ)|=(5132263211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_s3_2 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071039751/2000000000 : ℝ)*x 0 + (2566131777/5000000000 : ℝ)*x 1 + (-1737322527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071039751/2000000000 : ℝ)^5023 ≤ (9127561736407/20000000000000 : ℝ)^3999 := by
    have hnat : (1071039751 : ℕ)^5023*20000000000000^3999 ≤ 9127561736407^3999*2000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071039751 2000000000 9127561736407 20000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2566131777/5000000000 : ℝ)^5023 ≤ (43264281607219/100000000000000 : ℝ)^3999 := by
    have hnat : (2566131777 : ℕ)^5023*100000000000000^3999 ≤ 43264281607219^3999*5000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2566131777 5000000000 43264281607219 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1737322527/10000000000 : ℝ)^5023 ≤ (11097909695413/100000000000000 : ℝ)^3999 := by
    have hnat : (1737322527 : ℕ)^5023*100000000000000^3999 ≤ 11097909695413^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1737322527 10000000000 11097909695413 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071039751/2000000000 : ℝ), (2566131777/5000000000 : ℝ), (-1737322527/10000000000 : ℝ)] ![(9127561736407/20000000000000 : ℝ), (43264281607219/100000000000000 : ℝ), (11097909695413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071039751/2000000000 : ℝ)|^5023 ≤ (9127561736407/20000000000000 : ℝ)^3999
        have hw : |(1071039751/2000000000 : ℝ)|=(1071039751/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2566131777/5000000000 : ℝ)|^5023 ≤ (43264281607219/100000000000000 : ℝ)^3999
        have hw : |(2566131777/5000000000 : ℝ)|=(2566131777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1737322527/10000000000 : ℝ)|^5023 ≤ (11097909695413/100000000000000 : ℝ)^3999
        have hw : |(-1737322527/10000000000 : ℝ)|=(1737322527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_s3_3 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (415233143/1000000000 : ℝ)*x 0 + (3689566873/10000000000 : ℝ)*x 1 + (4654073931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (415233143/1000000000 : ℝ)^5023 ≤ (33155099070847/100000000000000 : ℝ)^3999 := by
    have hnat : (415233143 : ℕ)^5023*100000000000000^3999 ≤ 33155099070847^3999*1000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415233143 1000000000 33155099070847 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3689566873/10000000000 : ℝ)^5023 ≤ (14291024672807/50000000000000 : ℝ)^3999 := by
    have hnat : (3689566873 : ℕ)^5023*50000000000000^3999 ≤ 14291024672807^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3689566873 10000000000 14291024672807 50000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4654073931/10000000000 : ℝ)^5023 ≤ (38262851567633/100000000000000 : ℝ)^3999 := by
    have hnat : (4654073931 : ℕ)^5023*100000000000000^3999 ≤ 38262851567633^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4654073931 10000000000 38262851567633 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(415233143/1000000000 : ℝ), (3689566873/10000000000 : ℝ), (4654073931/10000000000 : ℝ)] ![(33155099070847/100000000000000 : ℝ), (14291024672807/50000000000000 : ℝ), (38262851567633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(415233143/1000000000 : ℝ)|^5023 ≤ (33155099070847/100000000000000 : ℝ)^3999
        have hw : |(415233143/1000000000 : ℝ)|=(415233143/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3689566873/10000000000 : ℝ)|^5023 ≤ (14291024672807/50000000000000 : ℝ)^3999
        have hw : |(3689566873/10000000000 : ℝ)|=(3689566873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4654073931/10000000000 : ℝ)|^5023 ≤ (38262851567633/100000000000000 : ℝ)^3999
        have hw : |(4654073931/10000000000 : ℝ)|=(4654073931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_s3_4 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-774749747/5000000000 : ℝ)*x 0 + (1027229379/2000000000 : ℝ)*x 1 + (2744854957/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (774749747/5000000000 : ℝ)^5023 ≤ (4806164272429/50000000000000 : ℝ)^3999 := by
    have hnat : (774749747 : ℕ)^5023*50000000000000^3999 ≤ 4806164272429^3999*5000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      774749747 5000000000 4806164272429 50000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1027229379/2000000000 : ℝ)^5023 ≤ (21652702072637/50000000000000 : ℝ)^3999 := by
    have hnat : (1027229379 : ℕ)^5023*50000000000000^3999 ≤ 21652702072637^3999*2000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027229379 2000000000 21652702072637 50000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2744854957/5000000000 : ℝ)^5023 ≤ (23541133647809/50000000000000 : ℝ)^3999 := by
    have hnat : (2744854957 : ℕ)^5023*50000000000000^3999 ≤ 23541133647809^3999*5000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2744854957 5000000000 23541133647809 50000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-774749747/5000000000 : ℝ), (1027229379/2000000000 : ℝ), (2744854957/5000000000 : ℝ)] ![(4806164272429/50000000000000 : ℝ), (21652702072637/50000000000000 : ℝ), (23541133647809/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-774749747/5000000000 : ℝ)|^5023 ≤ (4806164272429/50000000000000 : ℝ)^3999
        have hw : |(-774749747/5000000000 : ℝ)|=(774749747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1027229379/2000000000 : ℝ)|^5023 ≤ (21652702072637/50000000000000 : ℝ)^3999
        have hw : |(1027229379/2000000000 : ℝ)|=(1027229379/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2744854957/5000000000 : ℝ)|^5023 ≤ (23541133647809/50000000000000 : ℝ)^3999
        have hw : |(2744854957/5000000000 : ℝ)|=(2744854957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_s3_5 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5258775863/10000000000 : ℝ)*x 0 + (-344968933/2500000000 : ℝ)*x 1 + (548971053/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5258775863/10000000000 : ℝ)^5023 ≤ (11152013203427/25000000000000 : ℝ)^3999 := by
    have hnat : (5258775863 : ℕ)^5023*25000000000000^3999 ≤ 11152013203427^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258775863 10000000000 11152013203427 25000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (344968933/2500000000 : ℝ)^5023 ≤ (4154836623341/50000000000000 : ℝ)^3999 := by
    have hnat : (344968933 : ℕ)^5023*50000000000000^3999 ≤ 4154836623341^3999*2500000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344968933 2500000000 4154836623341 50000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (548971053/1000000000 : ℝ)^5023 ≤ (5885284241441/12500000000000 : ℝ)^3999 := by
    have hnat : (548971053 : ℕ)^5023*12500000000000^3999 ≤ 5885284241441^3999*1000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548971053 1000000000 5885284241441 12500000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5258775863/10000000000 : ℝ), (-344968933/2500000000 : ℝ), (548971053/1000000000 : ℝ)] ![(11152013203427/25000000000000 : ℝ), (4154836623341/50000000000000 : ℝ), (5885284241441/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5258775863/10000000000 : ℝ)|^5023 ≤ (11152013203427/25000000000000 : ℝ)^3999
        have hw : |(5258775863/10000000000 : ℝ)|=(5258775863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-344968933/2500000000 : ℝ)|^5023 ≤ (4154836623341/50000000000000 : ℝ)^3999
        have hw : |(-344968933/2500000000 : ℝ)|=(344968933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(548971053/1000000000 : ℝ)|^5023 ≤ (5885284241441/12500000000000 : ℝ)^3999
        have hw : |(548971053/1000000000 : ℝ)|=(548971053/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_s3_6 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (525877547/1000000000 : ℝ)*x 0 + (548971041/1000000000 : ℝ)*x 1 + (-275975291/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525877547/1000000000 : ℝ)^5023 ≤ (44608048626419/100000000000000 : ℝ)^3999 := by
    have hnat : (525877547 : ℕ)^5023*100000000000000^3999 ≤ 44608048626419^3999*1000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525877547 1000000000 44608048626419 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (548971041/1000000000 : ℝ)^5023 ≤ (23541136319409/50000000000000 : ℝ)^3999 := by
    have hnat : (548971041 : ℕ)^5023*50000000000000^3999 ≤ 23541136319409^3999*1000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548971041 1000000000 23541136319409 50000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (275975291/2000000000 : ℝ)^5023 ≤ (8309678715507/100000000000000 : ℝ)^3999 := by
    have hnat : (275975291 : ℕ)^5023*100000000000000^3999 ≤ 8309678715507^3999*2000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275975291 2000000000 8309678715507 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525877547/1000000000 : ℝ), (548971041/1000000000 : ℝ), (-275975291/2000000000 : ℝ)] ![(44608048626419/100000000000000 : ℝ), (23541136319409/50000000000000 : ℝ), (8309678715507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525877547/1000000000 : ℝ)|^5023 ≤ (44608048626419/100000000000000 : ℝ)^3999
        have hw : |(525877547/1000000000 : ℝ)|=(525877547/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(548971041/1000000000 : ℝ)|^5023 ≤ (23541136319409/50000000000000 : ℝ)^3999
        have hw : |(548971041/1000000000 : ℝ)|=(548971041/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-275975291/2000000000 : ℝ)|^5023 ≤ (8309678715507/100000000000000 : ℝ)^3999
        have hw : |(-275975291/2000000000 : ℝ)|=(275975291/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_s3_7 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4152789817/10000000000 : ℝ)*x 0 + (4643711833/10000000000 : ℝ)*x 1 + (1850042207/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4152789817/10000000000 : ℝ)^5023 ≤ (16579848215481/50000000000000 : ℝ)^3999 := by
    have hnat : (4152789817 : ℕ)^5023*50000000000000^3999 ≤ 16579848215481^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4152789817 10000000000 16579848215481 50000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4643711833/10000000000 : ℝ)^5023 ≤ (190779386109/500000000000 : ℝ)^3999 := by
    have hnat : (4643711833 : ℕ)^5023*500000000000^3999 ≤ 190779386109^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4643711833 10000000000 190779386109 500000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1850042207/5000000000 : ℝ)^5023 ≤ (5736885265859/20000000000000 : ℝ)^3999 := by
    have hnat : (1850042207 : ℕ)^5023*20000000000000^3999 ≤ 5736885265859^3999*5000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1850042207 5000000000 5736885265859 20000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4152789817/10000000000 : ℝ), (4643711833/10000000000 : ℝ), (1850042207/5000000000 : ℝ)] ![(16579848215481/50000000000000 : ℝ), (190779386109/500000000000 : ℝ), (5736885265859/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4152789817/10000000000 : ℝ)|^5023 ≤ (16579848215481/50000000000000 : ℝ)^3999
        have hw : |(4152789817/10000000000 : ℝ)|=(4152789817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4643711833/10000000000 : ℝ)|^5023 ≤ (190779386109/500000000000 : ℝ)^3999
        have hw : |(4643711833/10000000000 : ℝ)|=(4643711833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1850042207/5000000000 : ℝ)|^5023 ≤ (5736885265859/20000000000000 : ℝ)^3999
        have hw : |(1850042207/5000000000 : ℝ)|=(1850042207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1675_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183445147/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17379/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1927/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (9667/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8671/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17379/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1927/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17379/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1927/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17379/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1927/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17379/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1927/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17379/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1927/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17379/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1927/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1927/20000 : ℝ) ^ (5015/1024 : ℝ) ≤ (1055488454329299/100000000000000000000 : ℝ) := by
    have hpowers : (1927/20000 : ℝ)^5015 ≤ (1055488454329299/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1927 : ℕ)^5015*100000000000000000000^1024 ≤ 1055488454329299^1024*20000^5015 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1927 20000 1055488454329299 100000000000000000000 5015 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1927/20000 : ℝ)) (X := (1055488454329299/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5015 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17379/100000 : ℝ) ^ (5015/1024 : ℝ) ≤ (4742322350677467/25000000000000000000 : ℝ) := by
    have hpowers : (17379/100000 : ℝ)^5015 ≤ (4742322350677467/25000000000000000000 : ℝ)^1024 := by
      have hnat : (17379 : ℕ)^5015*25000000000000000000^1024 ≤ 4742322350677467^1024*100000^5015 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17379 100000 4742322350677467 25000000000000000000 5015 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17379/100000 : ℝ)) (X := (4742322350677467/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5015 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001055488454329299/50000000000000000000 : ℝ) ≤ (2500010775783637/2500000000000000 : ℝ) ^ (5015/1024 : ℝ) := by
    have hpowers : (50001055488454329299/50000000000000000000 : ℝ)^1024 ≤ (2500010775783637/2500000000000000 : ℝ)^5015 := by
      have hnat : (50001055488454329299 : ℕ)^1024*2500000000000000^5015 ≤ 2500010775783637^5015*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001055488454329299 50000000000000000000 2500010775783637 2500000000000000 1024 5015 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500010775783637/2500000000000000 : ℝ)) (X := (50001055488454329299/50000000000000000000 : ℝ)) (by norm_num) 5015 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100020024777857039167/100000000000000000000 : ℝ) ≤ (625025553014527/625000000000000 : ℝ) ^ (5015/1024 : ℝ) := by
    have hpowers : (100020024777857039167/100000000000000000000 : ℝ)^1024 ≤ (625025553014527/625000000000000 : ℝ)^5015 := by
      have hnat : (100020024777857039167 : ℕ)^1024*625000000000000^5015 ≤ 625025553014527^5015*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100020024777857039167 100000000000000000000 625025553014527 625000000000000 1024 5015 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625025553014527/625000000000000 : ℝ)) (X := (100020024777857039167/100000000000000000000 : ℝ)) (by norm_num) 5015 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12504742322350677467/12500000000000000000 : ℝ) ≤ (2500193648332579/2500000000000000 : ℝ) ^ (5015/1024 : ℝ) := by
    have hpowers : (12504742322350677467/12500000000000000000 : ℝ)^1024 ≤ (2500193648332579/2500000000000000 : ℝ)^5015 := by
      have hnat : (12504742322350677467 : ℕ)^1024*2500000000000000^5015 ≤ 2500193648332579^5015*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12504742322350677467 12500000000000000000 2500193648332579 2500000000000000 1024 5015 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500193648332579/2500000000000000 : ℝ)) (X := (12504742322350677467/12500000000000000000 : ℝ)) (by norm_num) 5015 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1055488454329299/100000000000000000000 : ℝ) ≤ ((9679160735329714379/9680000000000000000 : ℝ)+2*(91436274471/193600000000000 : ℝ)*(1927/20000 : ℝ))^(5015/1024 : ℝ) := by
    rw [show (9679160735329714379/9680000000000000000 : ℝ)+2*(91436274471/193600000000000 : ℝ)*(1927/20000 : ℝ)=(2500010775783637/2500000000000000 : ℝ) by norm_num, show 1+2*(1055488454329299/100000000000000000000 : ℝ)=(50001055488454329299/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4742322350677467/25000000000000000000 : ℝ)+(1055488454329299/100000000000000000000 : ℝ) ≤ ((9679160735329714379/9680000000000000000 : ℝ)+(91436274471/193600000000000 : ℝ)*((17379/100000 : ℝ)+(1927/20000 : ℝ)))^(5015/1024 : ℝ) := by
    rw [show (9679160735329714379/9680000000000000000 : ℝ)+(91436274471/193600000000000 : ℝ)*((17379/100000 : ℝ)+(1927/20000 : ℝ))=(625025553014527/625000000000000 : ℝ) by norm_num, show 1+(4742322350677467/25000000000000000000 : ℝ)+(1055488454329299/100000000000000000000 : ℝ)=(100020024777857039167/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4742322350677467/25000000000000000000 : ℝ) ≤ ((9679160735329714379/9680000000000000000 : ℝ)+2*(91436274471/193600000000000 : ℝ)*(17379/100000 : ℝ))^(5015/1024 : ℝ) := by
    rw [show (9679160735329714379/9680000000000000000 : ℝ)+2*(91436274471/193600000000000 : ℝ)*(17379/100000 : ℝ)=(2500193648332579/2500000000000000 : ℝ) by norm_num, show 1+2*(4742322350677467/25000000000000000000 : ℝ)=(12504742322350677467/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9679160735329714379/9680000000000000000 : ℝ)*(X 1 0+X 2 0)+(91436274471/193600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5015/1024 : ℝ)) (lo := (1927/20000 : ℝ)) (hi := (17379/100000 : ℝ)) (c := (9679160735329714379/9680000000000000000 : ℝ)) (alpha := (91436274471/193600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9679160735329714379/9680000000000000000 : ℝ)*(X 0 1+X 2 1)+(91436274471/193600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5015/1024 : ℝ)) (lo := (1927/20000 : ℝ)) (hi := (17379/100000 : ℝ)) (c := (9679160735329714379/9680000000000000000 : ℝ)) (alpha := (91436274471/193600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9679160735329714379/9680000000000000000 : ℝ)*(X 0 2+X 1 2)+(91436274471/193600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5015/1024 : ℝ)) (lo := (1927/20000 : ℝ)) (hi := (17379/100000 : ℝ)) (c := (9679160735329714379/9680000000000000000 : ℝ)) (alpha := (91436274471/193600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-96832979/625000000 : ℝ)*X 0 0+(5493651017/10000000000 : ℝ)*X 0 1+(5132263711/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5355199371/10000000000 : ℝ)*X 1 0+(-1737322157/10000000000 : ℝ)*X 1 1+(5132263211/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1071039751/2000000000 : ℝ)*X 2 0+(2566131777/5000000000 : ℝ)*X 2 1+(-1737322527/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((415233143/1000000000 : ℝ)*X 0 0+(3689566873/10000000000 : ℝ)*X 0 1+(4654073931/10000000000 : ℝ)*X 0 2+(415233143/1000000000 : ℝ)*X 1 0+(3689566873/10000000000 : ℝ)*X 1 1+(4654073931/10000000000 : ℝ)*X 1 2+(415233143/1000000000 : ℝ)*X 2 0+(3689566873/10000000000 : ℝ)*X 2 1+(4654073931/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-774749747/5000000000 : ℝ)*X 0 0+(1027229379/2000000000 : ℝ)*X 0 1+(2744854957/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5258775863/10000000000 : ℝ)*X 1 0+(-344968933/2500000000 : ℝ)*X 1 1+(548971053/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((525877547/1000000000 : ℝ)*X 2 0+(548971041/1000000000 : ℝ)*X 2 1+(-275975291/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4152789817/10000000000 : ℝ)*X 0 0+(4643711833/10000000000 : ℝ)*X 0 1+(1850042207/5000000000 : ℝ)*X 0 2+(4152789817/10000000000 : ℝ)*X 1 0+(4643711833/10000000000 : ℝ)*X 1 1+(1850042207/5000000000 : ℝ)*X 1 2+(4152789817/10000000000 : ℝ)*X 2 0+(4643711833/10000000000 : ℝ)*X 2 1+(1850042207/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (900125539881132401969168931/121000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1269324047/50000000000000 : ℝ)*(base19) + (1985002871/100000000000000 : ℝ)*(base23) + (2312267/25000000000000 : ℝ)*(upper2) + (425139239/100000000000000 : ℝ)*(upper3) + (135280283/100000000000000 : ℝ)*(upper4) + (475496723455037/25000000000000 : ℝ)*(major0) + (475496723455037/25000000000000 : ℝ)*(major1) + (475496723455037/25000000000000 : ℝ)*(major2) + (691784920494559/25000000000000 : ℝ)*(sp0) + (172947246897093/6250000000000 : ℝ)*(sp1) + (276715650399871/10000000000000 : ℝ)*(sp2) + (259201443662183/25000000000000 : ℝ)*(sp3) + (9403511673/50000000000000 : ℝ)*(sp4) + (9276021509/100000000000000 : ℝ)*(sp7) + (1036815050670241/100000000000000 : ℝ)*(f.failure) + (1383579244500791/50000000000000 : ℝ)*(f.sum) + (7008778036727/2420000000000000000000000000 : ℝ)*base65 + (1341878466749772977/242000000000000000000000000000000 : ℝ)*base68 + (975328513844227023/242000000000000000000000000000000 : ℝ)*base69 + (1829225071681772977/242000000000000000000000000000000 : ℝ)*base72 + (1606552911287/2420000000000000000000000000 : ℝ)*base73 + (436229003268227023/242000000000000000000000000000000 : ℝ)*base75 + (1038874227834227023/242000000000000000000000000000000 : ℝ)*base77 + (1302615578014227023/242000000000000000000000000000000 : ℝ)*base79 + (9879834424267/2420000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (8770427/10000000000000000000000 : ℝ)*base89 + (8770427/10000000000000000000000 : ℝ)*base91 + (8770427/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1117040203905176376843783393/121000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (784124933/50000000000000 : ℝ)*(base19) + (2054107/125000000000 : ℝ)*(base23) + (278669087/50000000000000 : ℝ)*(lower1) + (161731549/100000000000000 : ℝ)*(upper2) + (28299531/10000000000000 : ℝ)*(upper3) + (113664481/100000000000000 : ℝ)*(upper5) + (972015813698311/50000000000000 : ℝ)*(major0) + (972015813698311/50000000000000 : ℝ)*(major1) + (972015813698311/50000000000000 : ℝ)*(major2) + (576555317/50000000000000 : ℝ)*(sp1) + (1414164191900379/50000000000000 : ℝ)*(sp4) + (1414162831220129/50000000000000 : ℝ)*(sp5) + (1414163370257579/50000000000000 : ℝ)*(sp6) + (264933640816977/25000000000000 : ℝ)*(sp7) + (264933640816977/25000000000000 : ℝ)*(f.failure) + (1414164191900379/50000000000000 : ℝ)*(f.sum) + (4048400580079/4840000000000000000000000000 : ℝ)*base66 + (1794413299387236131/484000000000000000000000000000000 : ℝ)*base68 + (534788808812763869/484000000000000000000000000000000 : ℝ)*base69 + (1689711554492763869/484000000000000000000000000000000 : ℝ)*base71 + (20633834696319/4840000000000000000000000000 : ℝ)*base74 + (2114425561044763869/484000000000000000000000000000000 : ℝ)*base75 + (860391884764763869/484000000000000000000000000000000 : ℝ)*base77 + (2980223289532763869/484000000000000000000000000000000 : ℝ)*base79 + (25306660972001/4840000000000000000000000000 : ℝ)*base81 + (4139381/2500000000000000000000 : ℝ)*base90 + (4139381/2500000000000000000000 : ℝ)*base92 + (4139381/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1675_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183445147/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17379/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1927/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9667/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8671/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1675_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1675_s4_0 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-387338447/2500000000 : ℝ)*x 0 + (5493548571/10000000000 : ℝ)*x 1 + (2566174367/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (387338447/2500000000 : ℝ)^5023 ≤ (9611193217381/100000000000000 : ℝ)^3999 := by
    have hnat : (387338447 : ℕ)^5023*100000000000000^3999 ≤ 9611193217381^3999*2500000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387338447 2500000000 9611193217381 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5493548571/10000000000 : ℝ)^5023 ≤ (5890452904807/12500000000000 : ℝ)^3999 := by
    have hnat : (5493548571 : ℕ)^5023*12500000000000^3999 ≤ 5890452904807^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5493548571 10000000000 5890452904807 12500000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2566174367/5000000000 : ℝ)^5023 ≤ (43265183533161/100000000000000 : ℝ)^3999 := by
    have hnat : (2566174367 : ℕ)^5023*100000000000000^3999 ≤ 43265183533161^3999*5000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2566174367 5000000000 43265183533161 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-387338447/2500000000 : ℝ), (5493548571/10000000000 : ℝ), (2566174367/5000000000 : ℝ)] ![(9611193217381/100000000000000 : ℝ), (5890452904807/12500000000000 : ℝ), (43265183533161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-387338447/2500000000 : ℝ)|^5023 ≤ (9611193217381/100000000000000 : ℝ)^3999
        have hw : |(-387338447/2500000000 : ℝ)|=(387338447/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5493548571/10000000000 : ℝ)|^5023 ≤ (5890452904807/12500000000000 : ℝ)^3999
        have hw : |(5493548571/10000000000 : ℝ)|=(5493548571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2566174367/5000000000 : ℝ)|^5023 ≤ (43265183533161/100000000000000 : ℝ)^3999
        have hw : |(2566174367/5000000000 : ℝ)|=(2566174367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_s4_1 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338792577/2500000000 : ℝ)*x 0 + (-1737249031/10000000000 : ℝ)*x 1 + (1026469601/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338792577/2500000000 : ℝ)^5023 ≤ (45637504175133/100000000000000 : ℝ)^3999 := by
    have hnat : (1338792577 : ℕ)^5023*100000000000000^3999 ≤ 45637504175133^3999*2500000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338792577 2500000000 45637504175133 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1737249031/10000000000 : ℝ)^5023 ≤ (5548659995851/50000000000000 : ℝ)^3999 := by
    have hnat : (1737249031 : ℕ)^5023*50000000000000^3999 ≤ 5548659995851^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1737249031 10000000000 5548659995851 50000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1026469601/2000000000 : ℝ)^5023 ≤ (865303516283/2000000000000 : ℝ)^3999 := by
    have hnat : (1026469601 : ℕ)^5023*2000000000000^3999 ≤ 865303516283^3999*2000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026469601 2000000000 865303516283 2000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338792577/2500000000 : ℝ), (-1737249031/10000000000 : ℝ), (1026469601/2000000000 : ℝ)] ![(45637504175133/100000000000000 : ℝ), (5548659995851/50000000000000 : ℝ), (865303516283/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338792577/2500000000 : ℝ)|^5023 ≤ (45637504175133/100000000000000 : ℝ)^3999
        have hw : |(1338792577/2500000000 : ℝ)|=(1338792577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1737249031/10000000000 : ℝ)|^5023 ≤ (5548659995851/50000000000000 : ℝ)^3999
        have hw : |(-1737249031/10000000000 : ℝ)|=(1737249031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1026469601/2000000000 : ℝ)|^5023 ≤ (865303516283/2000000000000 : ℝ)^3999
        have hw : |(1026469601/2000000000 : ℝ)|=(1026469601/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_s4_2 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338792597/2500000000 : ℝ)*x 0 + (641543523/1250000000 : ℝ)*x 1 + (-173724869/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338792597/2500000000 : ℝ)^5023 ≤ (22818752515741/50000000000000 : ℝ)^3999 := by
    have hnat : (1338792597 : ℕ)^5023*50000000000000^3999 ≤ 22818752515741^3999*2500000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338792597 2500000000 22818752515741 50000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (641543523/1250000000 : ℝ)^5023 ≤ (4326517770949/10000000000000 : ℝ)^3999 := by
    have hnat : (641543523 : ℕ)^5023*10000000000000^3999 ≤ 4326517770949^3999*1250000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      641543523 1250000000 4326517770949 10000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (173724869/1000000000 : ℝ)^5023 ≤ (693582328479/6250000000000 : ℝ)^3999 := by
    have hnat : (173724869 : ℕ)^5023*6250000000000^3999 ≤ 693582328479^3999*1000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173724869 1000000000 693582328479 6250000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338792597/2500000000 : ℝ), (641543523/1250000000 : ℝ), (-173724869/1000000000 : ℝ)] ![(22818752515741/50000000000000 : ℝ), (4326517770949/10000000000000 : ℝ), (693582328479/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338792597/2500000000 : ℝ)|^5023 ≤ (22818752515741/50000000000000 : ℝ)^3999
        have hw : |(1338792597/2500000000 : ℝ)|=(1338792597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(641543523/1250000000 : ℝ)|^5023 ≤ (4326517770949/10000000000000 : ℝ)^3999
        have hw : |(641543523/1250000000 : ℝ)|=(641543523/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-173724869/1000000000 : ℝ)|^5023 ≤ (693582328479/6250000000000 : ℝ)^3999
        have hw : |(-173724869/1000000000 : ℝ)|=(173724869/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_s4_3 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4152349773/10000000000 : ℝ)*x 0 + (3689814703/10000000000 : ℝ)*x 1 + (4653822591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4152349773/10000000000 : ℝ)^5023 ≤ (33155283038177/100000000000000 : ℝ)^3999 := by
    have hnat : (4152349773 : ℕ)^5023*100000000000000^3999 ≤ 33155283038177^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4152349773 10000000000 33155283038177 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3689814703/10000000000 : ℝ)^5023 ≤ (28584460846157/100000000000000 : ℝ)^3999 := by
    have hnat : (3689814703 : ℕ)^5023*100000000000000^3999 ≤ 28584460846157^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3689814703 10000000000 28584460846157 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4653822591/10000000000 : ℝ)^5023 ≤ (19130128053527/50000000000000 : ℝ)^3999 := by
    have hnat : (4653822591 : ℕ)^5023*50000000000000^3999 ≤ 19130128053527^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4653822591 10000000000 19130128053527 50000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4152349773/10000000000 : ℝ), (3689814703/10000000000 : ℝ), (4653822591/10000000000 : ℝ)] ![(33155283038177/100000000000000 : ℝ), (28584460846157/100000000000000 : ℝ), (19130128053527/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4152349773/10000000000 : ℝ)|^5023 ≤ (33155283038177/100000000000000 : ℝ)^3999
        have hw : |(4152349773/10000000000 : ℝ)|=(4152349773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3689814703/10000000000 : ℝ)|^5023 ≤ (28584460846157/100000000000000 : ℝ)^3999
        have hw : |(3689814703/10000000000 : ℝ)|=(3689814703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4653822591/10000000000 : ℝ)|^5023 ≤ (19130128053527/50000000000000 : ℝ)^3999
        have hw : |(4653822591/10000000000 : ℝ)|=(4653822591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_s4_4 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1549525551/10000000000 : ℝ)*x 0 + (1027245449/2000000000 : ℝ)*x 1 + (2744806037/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1549525551/10000000000 : ℝ)^5023 ≤ (4806265790719/50000000000000 : ℝ)^3999 := by
    have hnat : (1549525551 : ℕ)^5023*50000000000000^3999 ≤ 4806265790719^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1549525551 10000000000 4806265790719 50000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1027245449/2000000000 : ℝ)^5023 ≤ (43306255093593/100000000000000 : ℝ)^3999 := by
    have hnat : (1027245449 : ℕ)^5023*100000000000000^3999 ≤ 43306255093593^3999*2000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027245449 2000000000 43306255093593 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2744806037/5000000000 : ℝ)^5023 ≤ (47081213308751/100000000000000 : ℝ)^3999 := by
    have hnat : (2744806037 : ℕ)^5023*100000000000000^3999 ≤ 47081213308751^3999*5000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2744806037 5000000000 47081213308751 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1549525551/10000000000 : ℝ), (1027245449/2000000000 : ℝ), (2744806037/5000000000 : ℝ)] ![(4806265790719/50000000000000 : ℝ), (43306255093593/100000000000000 : ℝ), (47081213308751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1549525551/10000000000 : ℝ)|^5023 ≤ (4806265790719/50000000000000 : ℝ)^3999
        have hw : |(-1549525551/10000000000 : ℝ)|=(1549525551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1027245449/2000000000 : ℝ)|^5023 ≤ (43306255093593/100000000000000 : ℝ)^3999
        have hw : |(1027245449/2000000000 : ℝ)|=(1027245449/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2744806037/5000000000 : ℝ)|^5023 ≤ (47081213308751/100000000000000 : ℝ)^3999
        have hw : |(2744806037/5000000000 : ℝ)|=(2744806037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_s4_5 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1051759563/2000000000 : ℝ)*x 0 + (-34499623/250000000 : ℝ)*x 1 + (5489612149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051759563/2000000000 : ℝ)^5023 ≤ (5576035838169/12500000000000 : ℝ)^3999 := by
    have hnat : (1051759563 : ℕ)^5023*12500000000000^3999 ≤ 5576035838169^3999*2000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051759563 2000000000 5576035838169 12500000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34499623/250000000 : ℝ)^5023 ≤ (8310499161113/100000000000000 : ℝ)^3999 := by
    have hnat : (34499623 : ℕ)^5023*100000000000000^3999 ≤ 8310499161113^3999*250000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34499623 250000000 8310499161113 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5489612149/10000000000 : ℝ)^5023 ≤ (47081214116691/100000000000000 : ℝ)^3999 := by
    have hnat : (5489612149 : ℕ)^5023*100000000000000^3999 ≤ 47081214116691^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5489612149 10000000000 47081214116691 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051759563/2000000000 : ℝ), (-34499623/250000000 : ℝ), (5489612149/10000000000 : ℝ)] ![(5576035838169/12500000000000 : ℝ), (8310499161113/100000000000000 : ℝ), (47081214116691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051759563/2000000000 : ℝ)|^5023 ≤ (5576035838169/12500000000000 : ℝ)^3999
        have hw : |(1051759563/2000000000 : ℝ)|=(1051759563/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-34499623/250000000 : ℝ)|^5023 ≤ (8310499161113/100000000000000 : ℝ)^3999
        have hw : |(-34499623/250000000 : ℝ)|=(34499623/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5489612149/10000000000 : ℝ)|^5023 ≤ (47081214116691/100000000000000 : ℝ)^3999
        have hw : |(5489612149/10000000000 : ℝ)|=(5489612149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_s4_6 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5258797733/10000000000 : ℝ)*x 0 + (5489612363/10000000000 : ℝ)*x 1 + (-137998473/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5258797733/10000000000 : ℝ)^5023 ≤ (44608285831667/100000000000000 : ℝ)^3999 := by
    have hnat : (5258797733 : ℕ)^5023*100000000000000^3999 ≤ 44608285831667^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258797733 10000000000 44608285831667 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5489612363/10000000000 : ℝ)^5023 ≤ (47081216422013/100000000000000 : ℝ)^3999 := by
    have hnat : (5489612363 : ℕ)^5023*100000000000000^3999 ≤ 47081216422013^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5489612363 10000000000 47081216422013 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (137998473/1000000000 : ℝ)^5023 ≤ (831049772391/10000000000000 : ℝ)^3999 := by
    have hnat : (137998473 : ℕ)^5023*10000000000000^3999 ≤ 831049772391^3999*1000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137998473 1000000000 831049772391 10000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5258797733/10000000000 : ℝ), (5489612363/10000000000 : ℝ), (-137998473/1000000000 : ℝ)] ![(44608285831667/100000000000000 : ℝ), (47081216422013/100000000000000 : ℝ), (831049772391/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5258797733/10000000000 : ℝ)|^5023 ≤ (44608285831667/100000000000000 : ℝ)^3999
        have hw : |(5258797733/10000000000 : ℝ)|=(5258797733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5489612363/10000000000 : ℝ)|^5023 ≤ (47081216422013/100000000000000 : ℝ)^3999
        have hw : |(5489612363/10000000000 : ℝ)|=(5489612363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-137998473/1000000000 : ℝ)|^5023 ≤ (831049772391/10000000000000 : ℝ)^3999
        have hw : |(-137998473/1000000000 : ℝ)|=(137998473/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_s4_7 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1038202159/2500000000 : ℝ)*x 0 + (1160867713/2500000000 : ℝ)*x 1 + (3700320441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1038202159/2500000000 : ℝ)^5023 ≤ (33159885177573/100000000000000 : ℝ)^3999 := by
    have hnat : (1038202159 : ℕ)^5023*100000000000000^3999 ≤ 33159885177573^3999*2500000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038202159 2500000000 33159885177573 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1160867713/2500000000 : ℝ)^5023 ≤ (7630678030517/20000000000000 : ℝ)^3999 := by
    have hnat : (1160867713 : ℕ)^5023*20000000000000^3999 ≤ 7630678030517^3999*2500000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1160867713 2500000000 7630678030517 20000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3700320441/10000000000 : ℝ)^5023 ≤ (14343362327419/50000000000000 : ℝ)^3999 := by
    have hnat : (3700320441 : ℕ)^5023*50000000000000^3999 ≤ 14343362327419^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3700320441 10000000000 14343362327419 50000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1038202159/2500000000 : ℝ), (1160867713/2500000000 : ℝ), (3700320441/10000000000 : ℝ)] ![(33159885177573/100000000000000 : ℝ), (7630678030517/20000000000000 : ℝ), (14343362327419/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1038202159/2500000000 : ℝ)|^5023 ≤ (33159885177573/100000000000000 : ℝ)^3999
        have hw : |(1038202159/2500000000 : ℝ)|=(1038202159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1160867713/2500000000 : ℝ)|^5023 ≤ (7630678030517/20000000000000 : ℝ)^3999
        have hw : |(1160867713/2500000000 : ℝ)|=(1160867713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3700320441/10000000000 : ℝ)|^5023 ≤ (14343362327419/50000000000000 : ℝ)^3999
        have hw : |(3700320441/10000000000 : ℝ)|=(3700320441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1675_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183445147/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8671/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9667/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9669/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (867/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8671/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9667/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8671/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9667/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8671/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9667/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8671/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9667/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8671/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9667/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8671/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9667/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9667/100000 : ℝ) ^ (5015/1024 : ℝ) ≤ (536384022907507/50000000000000000000 : ℝ) := by
    have hpowers : (9667/100000 : ℝ)^5015 ≤ (536384022907507/50000000000000000000 : ℝ)^1024 := by
      have hnat : (9667 : ℕ)^5015*50000000000000000000^1024 ≤ 536384022907507^1024*100000^5015 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9667 100000 536384022907507 50000000000000000000 5015 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9667/100000 : ℝ)) (X := (536384022907507/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5015 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8671/50000 : ℝ) ^ (5015/1024 : ℝ) ≤ (18772320744832659/100000000000000000000 : ℝ) := by
    have hpowers : (8671/50000 : ℝ)^5015 ≤ (18772320744832659/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8671 : ℕ)^5015*100000000000000000000^1024 ≤ 18772320744832659^1024*50000^5015 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8671 50000 18772320744832659 100000000000000000000 5015 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8671/50000 : ℝ)) (X := (18772320744832659/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5015 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000536384022907507/25000000000000000000 : ℝ) ≤ (5000021904388849/5000000000000000 : ℝ) ^ (5015/1024 : ℝ) := by
    have hpowers : (25000536384022907507/25000000000000000000 : ℝ)^1024 ≤ (5000021904388849/5000000000000000 : ℝ)^5015 := by
      have hnat : (25000536384022907507 : ℕ)^1024*5000000000000000^5015 ≤ 5000021904388849^5015*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000536384022907507 25000000000000000000 5000021904388849 5000000000000000 1024 5015 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000021904388849/5000000000000000 : ℝ)) (X := (25000536384022907507/25000000000000000000 : ℝ)) (by norm_num) 5015 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100019845088790647673/100000000000000000000 : ℝ) ≤ (2000081035957879/2000000000000000 : ℝ) ^ (5015/1024 : ℝ) := by
    have hpowers : (100019845088790647673/100000000000000000000 : ℝ)^1024 ≤ (2000081035957879/2000000000000000 : ℝ)^5015 := by
      have hnat : (100019845088790647673 : ℕ)^1024*2000000000000000^5015 ≤ 2000081035957879^5015*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100019845088790647673 100000000000000000000 2000081035957879 2000000000000000 1024 5015 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000081035957879/2000000000000000 : ℝ)) (X := (100019845088790647673/100000000000000000000 : ℝ)) (by norm_num) 5015 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50018772320744832659/50000000000000000000 : ℝ) ≤ (2500191637700273/2500000000000000 : ℝ) ^ (5015/1024 : ℝ) := by
    have hpowers : (50018772320744832659/50000000000000000000 : ℝ)^1024 ≤ (2500191637700273/2500000000000000 : ℝ)^5015 := by
      have hnat : (50018772320744832659 : ℕ)^1024*2500000000000000^5015 ≤ 2500191637700273^5015*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018772320744832659 50000000000000000000 2500191637700273 2500000000000000 1024 5015 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500191637700273/2500000000000000 : ℝ)) (X := (50018772320744832659/50000000000000000000 : ℝ)) (by norm_num) 5015 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(536384022907507/50000000000000000000 : ℝ) ≤ ((4796459342826792647/4796875000000000000 : ℝ)+2*(361371011697/767500000000000 : ℝ)*(9667/100000 : ℝ))^(5015/1024 : ℝ) := by
    rw [show (4796459342826792647/4796875000000000000 : ℝ)+2*(361371011697/767500000000000 : ℝ)*(9667/100000 : ℝ)=(5000021904388849/5000000000000000 : ℝ) by norm_num, show 1+2*(536384022907507/50000000000000000000 : ℝ)=(25000536384022907507/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18772320744832659/100000000000000000000 : ℝ)+(536384022907507/50000000000000000000 : ℝ) ≤ ((4796459342826792647/4796875000000000000 : ℝ)+(361371011697/767500000000000 : ℝ)*((8671/50000 : ℝ)+(9667/100000 : ℝ)))^(5015/1024 : ℝ) := by
    rw [show (4796459342826792647/4796875000000000000 : ℝ)+(361371011697/767500000000000 : ℝ)*((8671/50000 : ℝ)+(9667/100000 : ℝ))=(2000081035957879/2000000000000000 : ℝ) by norm_num, show 1+(18772320744832659/100000000000000000000 : ℝ)+(536384022907507/50000000000000000000 : ℝ)=(100019845088790647673/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18772320744832659/100000000000000000000 : ℝ) ≤ ((4796459342826792647/4796875000000000000 : ℝ)+2*(361371011697/767500000000000 : ℝ)*(8671/50000 : ℝ))^(5015/1024 : ℝ) := by
    rw [show (4796459342826792647/4796875000000000000 : ℝ)+2*(361371011697/767500000000000 : ℝ)*(8671/50000 : ℝ)=(2500191637700273/2500000000000000 : ℝ) by norm_num, show 1+2*(18772320744832659/100000000000000000000 : ℝ)=(50018772320744832659/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4796459342826792647/4796875000000000000 : ℝ)*(X 1 0+X 2 0)+(361371011697/767500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5015/1024 : ℝ)) (lo := (9667/100000 : ℝ)) (hi := (8671/50000 : ℝ)) (c := (4796459342826792647/4796875000000000000 : ℝ)) (alpha := (361371011697/767500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4796459342826792647/4796875000000000000 : ℝ)*(X 0 1+X 2 1)+(361371011697/767500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5015/1024 : ℝ)) (lo := (9667/100000 : ℝ)) (hi := (8671/50000 : ℝ)) (c := (4796459342826792647/4796875000000000000 : ℝ)) (alpha := (361371011697/767500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4796459342826792647/4796875000000000000 : ℝ)*(X 0 2+X 1 2)+(361371011697/767500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5015/1024 : ℝ)) (lo := (9667/100000 : ℝ)) (hi := (8671/50000 : ℝ)) (c := (4796459342826792647/4796875000000000000 : ℝ)) (alpha := (361371011697/767500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-387338447/2500000000 : ℝ)*X 0 0+(5493548571/10000000000 : ℝ)*X 0 1+(2566174367/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338792577/2500000000 : ℝ)*X 1 0+(-1737249031/10000000000 : ℝ)*X 1 1+(1026469601/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338792597/2500000000 : ℝ)*X 2 0+(641543523/1250000000 : ℝ)*X 2 1+(-173724869/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4152349773/10000000000 : ℝ)*X 0 0+(3689814703/10000000000 : ℝ)*X 0 1+(4653822591/10000000000 : ℝ)*X 0 2+(4152349773/10000000000 : ℝ)*X 1 0+(3689814703/10000000000 : ℝ)*X 1 1+(4653822591/10000000000 : ℝ)*X 1 2+(4152349773/10000000000 : ℝ)*X 2 0+(3689814703/10000000000 : ℝ)*X 2 1+(4653822591/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1549525551/10000000000 : ℝ)*X 0 0+(1027245449/2000000000 : ℝ)*X 0 1+(2744806037/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1051759563/2000000000 : ℝ)*X 1 0+(-34499623/250000000 : ℝ)*X 1 1+(5489612149/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5258797733/10000000000 : ℝ)*X 2 0+(5489612363/10000000000 : ℝ)*X 2 1+(-137998473/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1038202159/2500000000 : ℝ)*X 0 0+(1160867713/2500000000 : ℝ)*X 0 1+(3700320441/10000000000 : ℝ)*X 0 2+(1038202159/2500000000 : ℝ)*X 1 0+(1160867713/2500000000 : ℝ)*X 1 1+(3700320441/10000000000 : ℝ)*X 1 2+(1038202159/2500000000 : ℝ)*X 2 0+(1160867713/2500000000 : ℝ)*X 2 1+(3700320441/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2017642893869910369786093/234222412109375000000000000000 : ℝ) := by norm_num
    linear_combination (150929621/12500000000000 : ℝ)*(base19) + (283312861/25000000000000 : ℝ)*(base23) + (495009/800000000000 : ℝ)*(lower2) + (63951821/100000000000000 : ℝ)*(upper3) + (93039631/50000000000000 : ℝ)*(upper5) + (237869239517419/12500000000000 : ℝ)*(major0) + (237869239517419/12500000000000 : ℝ)*(major1) + (237869239517419/12500000000000 : ℝ)*(major2) + (1384278168732371/50000000000000 : ℝ)*(sp0) + (34607051772667/1250000000000 : ℝ)*(sp1) + (2768564215998883/100000000000000 : ℝ)*(sp2) + (51866961581251/5000000000000 : ℝ)*(sp3) + (4505892793/50000000000000 : ℝ)*(sp4) + (92633211/3125000000000 : ℝ)*(sp7) + (259335548971943/25000000000000 : ℝ)*(f.failure) + (346070668656291/12500000000000 : ℝ)*(f.sum) + (48394698372047/19187500000000000000000000000 : ℝ)*base65 + (125229488632738157/59960937500000000000000000000000 : ℝ)*base68 + (349920775624144407/59960937500000000000000000000000 : ℝ)*base70 + (49607569486644407/59960937500000000000000000000000 : ℝ)*base72 + (28083552299211/9593750000000000000000000000 : ℝ)*base73 + (271986235791331907/59960937500000000000000000000000 : ℝ)*base76 + (110310545890699343/59960937500000000000000000000000 : ℝ)*base77 + (425055766144605593/59960937500000000000000000000000 : ℝ)*base79 + (43358603304453/19187500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (17489379/2500000000000000000000 : ℝ)*base90 + (17489379/2500000000000000000000 : ℝ)*base92 + (17489379/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8914748260056468349349109/781250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (376806309/25000000000000 : ℝ)*(base19) + (888720841/50000000000000 : ℝ)*(base23) + (222202293/50000000000000 : ℝ)*(lower1) + (256635661/100000000000000 : ℝ)*(upper3) + (61914703/50000000000000 : ℝ)*(lower4) + (200993331/100000000000000 : ℝ)*(upper5) + (1945016581372931/100000000000000 : ℝ)*(major0) + (1945016581372931/100000000000000 : ℝ)*(major1) + (1945016581372931/100000000000000 : ℝ)*(major2) + (172148347/4000000000000 : ℝ)*(sp2) + (282976129895561/10000000000000 : ℝ)*(sp4) + (1414879895865187/50000000000000 : ℝ)*(sp5) + (1414877608902627/50000000000000 : ℝ)*(sp6) + (1060271483427649/100000000000000 : ℝ)*(sp7) + (1060271483427649/100000000000000 : ℝ)*(f.failure) + (282976129895561/10000000000000 : ℝ)*(f.sum) + (112592504298343/38375000000000000000000000000 : ℝ)*base66 + (2926290769750567893/479687500000000000000000000000000 : ℝ)*base68 + (403866979058380393/479687500000000000000000000000000 : ℝ)*base70 + (22493285066675567893/479687500000000000000000000000000 : ℝ)*base72 + (36527160885593/38375000000000000000000000000 : ℝ)*base74 + (10283836238280255393/479687500000000000000000000000000 : ℝ)*base76 + (3329324422150567893/479687500000000000000000000000000 : ℝ)*base78 + (2234800588913067893/479687500000000000000000000000000 : ℝ)*base80 + (28483133588641/19187500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (34669403/10000000000000000000000 : ℝ)*base89 + (34669403/10000000000000000000000 : ℝ)*base91 + (34669403/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1675_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183445147/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8671/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9667/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9669/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (867/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1675_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1675_box_0 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-600460947/5000000000 : ℝ)*x 0 + (5436554353/10000000000 : ℝ)*x 1 + (5436553547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (600460947/5000000000 : ℝ)^5023 ≤ (872411996561/12500000000000 : ℝ)^3999 := by
    have hnat : (600460947 : ℕ)^5023*12500000000000^3999 ≤ 872411996561^3999*5000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      600460947 5000000000 872411996561 12500000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436554353/10000000000 : ℝ)^5023 ≤ (46510356331933/100000000000000 : ℝ)^3999 := by
    have hnat : (5436554353 : ℕ)^5023*100000000000000^3999 ≤ 46510356331933^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436554353 10000000000 46510356331933 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5436553547/10000000000 : ℝ)^5023 ≤ (46510347670839/100000000000000 : ℝ)^3999 := by
    have hnat : (5436553547 : ℕ)^5023*100000000000000^3999 ≤ 46510347670839^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436553547 10000000000 46510347670839 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-600460947/5000000000 : ℝ), (5436554353/10000000000 : ℝ), (5436553547/10000000000 : ℝ)] ![(872411996561/12500000000000 : ℝ), (46510356331933/100000000000000 : ℝ), (46510347670839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-600460947/5000000000 : ℝ)|^5023 ≤ (872411996561/12500000000000 : ℝ)^3999
        have hw : |(-600460947/5000000000 : ℝ)|=(600460947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436554353/10000000000 : ℝ)|^5023 ≤ (46510356331933/100000000000000 : ℝ)^3999
        have hw : |(5436554353/10000000000 : ℝ)|=(5436554353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5436553547/10000000000 : ℝ)|^5023 ≤ (46510347670839/100000000000000 : ℝ)^3999
        have hw : |(5436553547/10000000000 : ℝ)|=(5436553547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_box_1 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2613013783/5000000000 : ℝ)*x 0 + (-150026059/1000000000 : ℝ)*x 1 + (5436554573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2613013783/5000000000 : ℝ)^5023 ≤ (691553263143/1562500000000 : ℝ)^3999 := by
    have hnat : (2613013783 : ℕ)^5023*1562500000000^3999 ≤ 691553263143^3999*5000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613013783 5000000000 691553263143 1562500000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (150026059/1000000000 : ℝ)^5023 ≤ (4615116222293/50000000000000 : ℝ)^3999 := by
    have hnat : (150026059 : ℕ)^5023*50000000000000^3999 ≤ 4615116222293^3999*1000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      150026059 1000000000 4615116222293 50000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5436554573/10000000000 : ℝ)^5023 ≤ (46510358696003/100000000000000 : ℝ)^3999 := by
    have hnat : (5436554573 : ℕ)^5023*100000000000000^3999 ≤ 46510358696003^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436554573 10000000000 46510358696003 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2613013783/5000000000 : ℝ), (-150026059/1000000000 : ℝ), (5436554573/10000000000 : ℝ)] ![(691553263143/1562500000000 : ℝ), (4615116222293/50000000000000 : ℝ), (46510358696003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2613013783/5000000000 : ℝ)|^5023 ≤ (691553263143/1562500000000 : ℝ)^3999
        have hw : |(2613013783/5000000000 : ℝ)|=(2613013783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-150026059/1000000000 : ℝ)|^5023 ≤ (4615116222293/50000000000000 : ℝ)^3999
        have hw : |(-150026059/1000000000 : ℝ)|=(150026059/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5436554573/10000000000 : ℝ)|^5023 ≤ (46510358696003/100000000000000 : ℝ)^3999
        have hw : |(5436554573/10000000000 : ℝ)|=(5436554573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_box_2 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5226027101/10000000000 : ℝ)*x 0 + (1359138523/2500000000 : ℝ)*x 1 + (-1500261899/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5226027101/10000000000 : ℝ)^5023 ≤ (8851880778929/20000000000000 : ℝ)^3999 := by
    have hnat : (5226027101 : ℕ)^5023*20000000000000^3999 ≤ 8851880778929^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226027101 10000000000 8851880778929 20000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1359138523/2500000000 : ℝ)^5023 ≤ (23255176763643/50000000000000 : ℝ)^3999 := by
    have hnat : (1359138523 : ℕ)^5023*50000000000000^3999 ≤ 23255176763643^3999*2500000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359138523 2500000000 23255176763643 50000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1500261899/10000000000 : ℝ)^5023 ≤ (28844508001/312500000000 : ℝ)^3999 := by
    have hnat : (1500261899 : ℕ)^5023*312500000000^3999 ≤ 28844508001^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1500261899 10000000000 28844508001 312500000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5226027101/10000000000 : ℝ), (1359138523/2500000000 : ℝ), (-1500261899/10000000000 : ℝ)] ![(8851880778929/20000000000000 : ℝ), (23255176763643/50000000000000 : ℝ), (28844508001/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5226027101/10000000000 : ℝ)|^5023 ≤ (8851880778929/20000000000000 : ℝ)^3999
        have hw : |(5226027101/10000000000 : ℝ)|=(5226027101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1359138523/2500000000 : ℝ)|^5023 ≤ (23255176763643/50000000000000 : ℝ)^3999
        have hw : |(1359138523/2500000000 : ℝ)|=(1359138523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1500261899/10000000000 : ℝ)|^5023 ≤ (28844508001/312500000000 : ℝ)^3999
        have hw : |(-1500261899/10000000000 : ℝ)|=(1500261899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_box_3 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4538954929/10000000000 : ℝ)*x 0 + (3982526357/10000000000 : ℝ)*x 1 + (995630997/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4538954929/10000000000 : ℝ)^5023 ≤ (7415571188803/20000000000000 : ℝ)^3999 := by
    have hnat : (4538954929 : ℕ)^5023*20000000000000^3999 ≤ 7415571188803^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4538954929 10000000000 7415571188803 20000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3982526357/10000000000 : ℝ)^5023 ≤ (7865270942453/25000000000000 : ℝ)^3999 := by
    have hnat : (3982526357 : ℕ)^5023*25000000000000^3999 ≤ 7865270942453^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3982526357 10000000000 7865270942453 25000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (995630997/2500000000 : ℝ)^5023 ≤ (31461060263103/100000000000000 : ℝ)^3999 := by
    have hnat : (995630997 : ℕ)^5023*100000000000000^3999 ≤ 31461060263103^3999*2500000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      995630997 2500000000 31461060263103 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4538954929/10000000000 : ℝ), (3982526357/10000000000 : ℝ), (995630997/2500000000 : ℝ)] ![(7415571188803/20000000000000 : ℝ), (7865270942453/25000000000000 : ℝ), (31461060263103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4538954929/10000000000 : ℝ)|^5023 ≤ (7415571188803/20000000000000 : ℝ)^3999
        have hw : |(4538954929/10000000000 : ℝ)|=(4538954929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3982526357/10000000000 : ℝ)|^5023 ≤ (7865270942453/25000000000000 : ℝ)^3999
        have hw : |(3982526357/10000000000 : ℝ)|=(3982526357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(995630997/2500000000 : ℝ)|^5023 ≤ (31461060263103/100000000000000 : ℝ)^3999
        have hw : |(995630997/2500000000 : ℝ)|=(995630997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_box_4 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-959492653/5000000000 : ℝ)*x 0 + (5174572389/10000000000 : ℝ)*x 1 + (2587285417/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (959492653/5000000000 : ℝ)^5023 ≤ (12574539707211/100000000000000 : ℝ)^3999 := by
    have hnat : (959492653 : ℕ)^5023*100000000000000^3999 ≤ 12574539707211^3999*5000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      959492653 5000000000 12574539707211 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5174572389/10000000000 : ℝ)^5023 ≤ (43712738385087/100000000000000 : ℝ)^3999 := by
    have hnat : (5174572389 : ℕ)^5023*100000000000000^3999 ≤ 43712738385087^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174572389 10000000000 43712738385087 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2587285417/5000000000 : ℝ)^5023 ≤ (218563609427/500000000000 : ℝ)^3999 := by
    have hnat : (2587285417 : ℕ)^5023*500000000000^3999 ≤ 218563609427^3999*5000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587285417 5000000000 218563609427 500000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-959492653/5000000000 : ℝ), (5174572389/10000000000 : ℝ), (2587285417/5000000000 : ℝ)] ![(12574539707211/100000000000000 : ℝ), (43712738385087/100000000000000 : ℝ), (218563609427/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-959492653/5000000000 : ℝ)|^5023 ≤ (12574539707211/100000000000000 : ℝ)^3999
        have hw : |(-959492653/5000000000 : ℝ)|=(959492653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5174572389/10000000000 : ℝ)|^5023 ≤ (43712738385087/100000000000000 : ℝ)^3999
        have hw : |(5174572389/10000000000 : ℝ)|=(5174572389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2587285417/5000000000 : ℝ)|^5023 ≤ (218563609427/500000000000 : ℝ)^3999
        have hw : |(2587285417/5000000000 : ℝ)|=(2587285417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_box_5 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2702627151/5000000000 : ℝ)*x 0 + (-1613419559/10000000000 : ℝ)*x 1 + (5174572619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2702627151/5000000000 : ℝ)^5023 ≤ (11543565333933/25000000000000 : ℝ)^3999 := by
    have hnat : (2702627151 : ℕ)^5023*25000000000000^3999 ≤ 11543565333933^3999*5000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702627151 5000000000 11543565333933 25000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1613419559/10000000000 : ℝ)^5023 ≤ (10112997825981/100000000000000 : ℝ)^3999 := by
    have hnat : (1613419559 : ℕ)^5023*100000000000000^3999 ≤ 10112997825981^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1613419559 10000000000 10112997825981 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5174572619/10000000000 : ℝ)^5023 ≤ (8742548165111/20000000000000 : ℝ)^3999 := by
    have hnat : (5174572619 : ℕ)^5023*20000000000000^3999 ≤ 8742548165111^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174572619 10000000000 8742548165111 20000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2702627151/5000000000 : ℝ), (-1613419559/10000000000 : ℝ), (5174572619/10000000000 : ℝ)] ![(11543565333933/25000000000000 : ℝ), (10112997825981/100000000000000 : ℝ), (8742548165111/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2702627151/5000000000 : ℝ)|^5023 ≤ (11543565333933/25000000000000 : ℝ)^3999
        have hw : |(2702627151/5000000000 : ℝ)|=(2702627151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1613419559/10000000000 : ℝ)|^5023 ≤ (10112997825981/100000000000000 : ℝ)^3999
        have hw : |(-1613419559/10000000000 : ℝ)|=(1613419559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5174572619/10000000000 : ℝ)|^5023 ≤ (8742548165111/20000000000000 : ℝ)^3999
        have hw : |(5174572619/10000000000 : ℝ)|=(5174572619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_box_6 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (540525489/1000000000 : ℝ)*x 0 + (2587285757/5000000000 : ℝ)*x 1 + (-806710123/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540525489/1000000000 : ℝ)^5023 ≤ (46174267644913/100000000000000 : ℝ)^3999 := by
    have hnat : (540525489 : ℕ)^5023*100000000000000^3999 ≤ 46174267644913^3999*1000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540525489 1000000000 46174267644913 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2587285757/5000000000 : ℝ)^5023 ≤ (43712729100697/100000000000000 : ℝ)^3999 := by
    have hnat : (2587285757 : ℕ)^5023*100000000000000^3999 ≤ 43712729100697^3999*5000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587285757 5000000000 43712729100697 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (806710123/5000000000 : ℝ)^5023 ≤ (316031351087/3125000000000 : ℝ)^3999 := by
    have hnat : (806710123 : ℕ)^5023*3125000000000^3999 ≤ 316031351087^3999*5000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806710123 5000000000 316031351087 3125000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540525489/1000000000 : ℝ), (2587285757/5000000000 : ℝ), (-806710123/5000000000 : ℝ)] ![(46174267644913/100000000000000 : ℝ), (43712729100697/100000000000000 : ℝ), (316031351087/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540525489/1000000000 : ℝ)|^5023 ≤ (46174267644913/100000000000000 : ℝ)^3999
        have hw : |(540525489/1000000000 : ℝ)|=(540525489/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2587285757/5000000000 : ℝ)|^5023 ≤ (43712729100697/100000000000000 : ℝ)^3999
        have hw : |(2587285757/5000000000 : ℝ)|=(2587285757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-806710123/5000000000 : ℝ)|^5023 ≤ (316031351087/3125000000000 : ℝ)^3999
        have hw : |(-806710123/5000000000 : ℝ)|=(806710123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_box_7 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (469002777/1250000000 : ℝ)*x 0 + (2187550487/5000000000 : ℝ)*x 1 + (4375100301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (469002777/1250000000 : ℝ)^5023 ≤ (14595537544791/50000000000000 : ℝ)^3999 := by
    have hnat : (469002777 : ℕ)^5023*50000000000000^3999 ≤ 14595537544791^3999*1250000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469002777 1250000000 14595537544791 50000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2187550487/5000000000 : ℝ)^5023 ≤ (35404465871513/100000000000000 : ℝ)^3999 := by
    have hnat : (2187550487 : ℕ)^5023*100000000000000^3999 ≤ 35404465871513^3999*5000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187550487 5000000000 35404465871513 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4375100301/10000000000 : ℝ)^5023 ≤ (4425557378859/12500000000000 : ℝ)^3999 := by
    have hnat : (4375100301 : ℕ)^5023*12500000000000^3999 ≤ 4425557378859^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4375100301 10000000000 4425557378859 12500000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(469002777/1250000000 : ℝ), (2187550487/5000000000 : ℝ), (4375100301/10000000000 : ℝ)] ![(14595537544791/50000000000000 : ℝ), (35404465871513/100000000000000 : ℝ), (4425557378859/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(469002777/1250000000 : ℝ)|^5023 ≤ (14595537544791/50000000000000 : ℝ)^3999
        have hw : |(469002777/1250000000 : ℝ)|=(469002777/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2187550487/5000000000 : ℝ)|^5023 ≤ (35404465871513/100000000000000 : ℝ)^3999
        have hw : |(2187550487/5000000000 : ℝ)|=(2187550487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4375100301/10000000000 : ℝ)|^5023 ≤ (4425557378859/12500000000000 : ℝ)^3999
        have hw : |(4375100301/10000000000 : ℝ)|=(4375100301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_box_8 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-882628277/5000000000 : ℝ)*x 0 + (4983179847/10000000000 : ℝ)*x 1 + (5480759409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (882628277/5000000000 : ℝ)^5023 ≤ (11322502399763/100000000000000 : ℝ)^3999 := by
    have hnat : (882628277 : ℕ)^5023*100000000000000^3999 ≤ 11322502399763^3999*5000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      882628277 5000000000 11322502399763 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4983179847/10000000000 : ℝ)^5023 ≤ (2084581509261/5000000000000 : ℝ)^3999 := by
    have hnat : (4983179847 : ℕ)^5023*5000000000000^3999 ≤ 2084581509261^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4983179847 10000000000 2084581509261 5000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5480759409/10000000000 : ℝ)^5023 ≤ (9397173479147/20000000000000 : ℝ)^3999 := by
    have hnat : (5480759409 : ℕ)^5023*20000000000000^3999 ≤ 9397173479147^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5480759409 10000000000 9397173479147 20000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-882628277/5000000000 : ℝ), (4983179847/10000000000 : ℝ), (5480759409/10000000000 : ℝ)] ![(11322502399763/100000000000000 : ℝ), (2084581509261/5000000000000 : ℝ), (9397173479147/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-882628277/5000000000 : ℝ)|^5023 ≤ (11322502399763/100000000000000 : ℝ)^3999
        have hw : |(-882628277/5000000000 : ℝ)|=(882628277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4983179847/10000000000 : ℝ)|^5023 ≤ (2084581509261/5000000000000 : ℝ)^3999
        have hw : |(4983179847/10000000000 : ℝ)|=(4983179847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5480759409/10000000000 : ℝ)|^5023 ≤ (9397173479147/20000000000000 : ℝ)^3999
        have hw : |(5480759409/10000000000 : ℝ)|=(5480759409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_box_9 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5195789601/10000000000 : ℝ)*x 0 + (-1480286413/10000000000 : ℝ)*x 1 + (1370190007/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5195789601/10000000000 : ℝ)^5023 ≤ (4393798658871/10000000000000 : ℝ)^3999 := by
    have hnat : (5195789601 : ℕ)^5023*10000000000000^3999 ≤ 4393798658871^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195789601 10000000000 4393798658871 10000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1480286413/10000000000 : ℝ)^5023 ≤ (1134517417051/12500000000000 : ℝ)^3999 := by
    have hnat : (1480286413 : ℕ)^5023*12500000000000^3999 ≤ 1134517417051^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1480286413 10000000000 1134517417051 12500000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1370190007/2500000000 : ℝ)^5023 ≤ (5873234257647/12500000000000 : ℝ)^3999 := by
    have hnat : (1370190007 : ℕ)^5023*12500000000000^3999 ≤ 5873234257647^3999*2500000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1370190007 2500000000 5873234257647 12500000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5195789601/10000000000 : ℝ), (-1480286413/10000000000 : ℝ), (1370190007/2500000000 : ℝ)] ![(4393798658871/10000000000000 : ℝ), (1134517417051/12500000000000 : ℝ), (5873234257647/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5195789601/10000000000 : ℝ)|^5023 ≤ (4393798658871/10000000000000 : ℝ)^3999
        have hw : |(5195789601/10000000000 : ℝ)|=(5195789601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1480286413/10000000000 : ℝ)|^5023 ≤ (1134517417051/12500000000000 : ℝ)^3999
        have hw : |(-1480286413/10000000000 : ℝ)|=(1480286413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1370190007/2500000000 : ℝ)|^5023 ≤ (5873234257647/12500000000000 : ℝ)^3999
        have hw : |(1370190007/2500000000 : ℝ)|=(1370190007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_box_10 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2597894857/5000000000 : ℝ)*x 0 + (5480759993/10000000000 : ℝ)*x 1 + (-296057261/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2597894857/5000000000 : ℝ)^5023 ≤ (2196899389449/5000000000000 : ℝ)^3999 := by
    have hnat : (2597894857 : ℕ)^5023*5000000000000^3999 ≤ 2196899389449^3999*5000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597894857 5000000000 2196899389449 5000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5480759993/10000000000 : ℝ)^5023 ≤ (23492936842147/50000000000000 : ℝ)^3999 := by
    have hnat : (5480759993 : ℕ)^5023*50000000000000^3999 ≤ 23492936842147^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5480759993 10000000000 23492936842147 50000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (296057261/2000000000 : ℝ)^5023 ≤ (4538069252331/50000000000000 : ℝ)^3999 := by
    have hnat : (296057261 : ℕ)^5023*50000000000000^3999 ≤ 4538069252331^3999*2000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      296057261 2000000000 4538069252331 50000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2597894857/5000000000 : ℝ), (5480759993/10000000000 : ℝ), (-296057261/2000000000 : ℝ)] ![(2196899389449/5000000000000 : ℝ), (23492936842147/50000000000000 : ℝ), (4538069252331/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2597894857/5000000000 : ℝ)|^5023 ≤ (2196899389449/5000000000000 : ℝ)^3999
        have hw : |(2597894857/5000000000 : ℝ)|=(2597894857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5480759993/10000000000 : ℝ)|^5023 ≤ (23492936842147/50000000000000 : ℝ)^3999
        have hw : |(5480759993/10000000000 : ℝ)|=(5480759993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-296057261/2000000000 : ℝ)|^5023 ≤ (4538069252331/50000000000000 : ℝ)^3999
        have hw : |(-296057261/2000000000 : ℝ)|=(296057261/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_box_11 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4666676711/10000000000 : ℝ)*x 0 + (1958055597/5000000000 : ℝ)*x 1 + (3916110449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4666676711/10000000000 : ℝ)^5023 ≤ (19196520034287/50000000000000 : ℝ)^3999 := by
    have hnat : (4666676711 : ℕ)^5023*50000000000000^3999 ≤ 19196520034287^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4666676711 10000000000 19196520034287 50000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1958055597/5000000000 : ℝ)^5023 ≤ (30803483634989/100000000000000 : ℝ)^3999 := by
    have hnat : (1958055597 : ℕ)^5023*100000000000000^3999 ≤ 30803483634989^3999*5000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1958055597 5000000000 30803483634989 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3916110449/10000000000 : ℝ)^5023 ≤ (6160695254879/20000000000000 : ℝ)^3999 := by
    have hnat : (3916110449 : ℕ)^5023*20000000000000^3999 ≤ 6160695254879^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3916110449 10000000000 6160695254879 20000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4666676711/10000000000 : ℝ), (1958055597/5000000000 : ℝ), (3916110449/10000000000 : ℝ)] ![(19196520034287/50000000000000 : ℝ), (30803483634989/100000000000000 : ℝ), (6160695254879/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4666676711/10000000000 : ℝ)|^5023 ≤ (19196520034287/50000000000000 : ℝ)^3999
        have hw : |(4666676711/10000000000 : ℝ)|=(4666676711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1958055597/5000000000 : ℝ)|^5023 ≤ (30803483634989/100000000000000 : ℝ)^3999
        have hw : |(1958055597/5000000000 : ℝ)|=(1958055597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3916110449/10000000000 : ℝ)|^5023 ≤ (6160695254879/20000000000000 : ℝ)^3999
        have hw : |(3916110449/10000000000 : ℝ)|=(3916110449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_box_12 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-84400991/625000000 : ℝ)*x 0 + (2809033423/5000000000 : ℝ)*x 1 + (64364699/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84400991/625000000 : ℝ)^5023 ≤ (4043724471553/50000000000000 : ℝ)^3999 := by
    have hnat : (84400991 : ℕ)^5023*50000000000000^3999 ≤ 4043724471553^3999*625000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84400991 625000000 4043724471553 50000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2809033423/5000000000 : ℝ)^5023 ≤ (48469118220799/100000000000000 : ℝ)^3999 := by
    have hnat : (2809033423 : ℕ)^5023*100000000000000^3999 ≤ 48469118220799^3999*5000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2809033423 5000000000 48469118220799 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (64364699/125000000 : ℝ)^5023 ≤ (10860858202853/25000000000000 : ℝ)^3999 := by
    have hnat : (64364699 : ℕ)^5023*25000000000000^3999 ≤ 10860858202853^3999*125000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64364699 125000000 10860858202853 25000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-84400991/625000000 : ℝ), (2809033423/5000000000 : ℝ), (64364699/125000000 : ℝ)] ![(4043724471553/50000000000000 : ℝ), (48469118220799/100000000000000 : ℝ), (10860858202853/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-84400991/625000000 : ℝ)|^5023 ≤ (4043724471553/50000000000000 : ℝ)^3999
        have hw : |(-84400991/625000000 : ℝ)|=(84400991/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2809033423/5000000000 : ℝ)|^5023 ≤ (48469118220799/100000000000000 : ℝ)^3999
        have hw : |(2809033423/5000000000 : ℝ)|=(2809033423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(64364699/125000000 : ℝ)|^5023 ≤ (10860858202853/25000000000000 : ℝ)^3999
        have hw : |(64364699/125000000 : ℝ)|=(64364699/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_box_13 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2711326993/5000000000 : ℝ)*x 0 + (-202986733/1250000000 : ℝ)*x 1 + (5149176001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2711326993/5000000000 : ℝ)^5023 ≤ (46361035056601/100000000000000 : ℝ)^3999 := by
    have hnat : (2711326993 : ℕ)^5023*100000000000000^3999 ≤ 46361035056601^3999*5000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711326993 5000000000 46361035056601 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (202986733/1250000000 : ℝ)^5023 ≤ (10195531244797/100000000000000 : ℝ)^3999 := by
    have hnat : (202986733 : ℕ)^5023*100000000000000^3999 ≤ 10195531244797^3999*1250000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202986733 1250000000 10195531244797 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5149176001/10000000000 : ℝ)^5023 ≤ (217217168349/500000000000 : ℝ)^3999 := by
    have hnat : (5149176001 : ℕ)^5023*500000000000^3999 ≤ 217217168349^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5149176001 10000000000 217217168349 500000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2711326993/5000000000 : ℝ), (-202986733/1250000000 : ℝ), (5149176001/10000000000 : ℝ)] ![(46361035056601/100000000000000 : ℝ), (10195531244797/100000000000000 : ℝ), (217217168349/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2711326993/5000000000 : ℝ)|^5023 ≤ (46361035056601/100000000000000 : ℝ)^3999
        have hw : |(2711326993/5000000000 : ℝ)|=(2711326993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-202986733/1250000000 : ℝ)|^5023 ≤ (10195531244797/100000000000000 : ℝ)^3999
        have hw : |(-202986733/1250000000 : ℝ)|=(202986733/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5149176001/10000000000 : ℝ)|^5023 ≤ (217217168349/500000000000 : ℝ)^3999
        have hw : |(5149176001/10000000000 : ℝ)|=(5149176001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_box_14 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2711327019/5000000000 : ℝ)*x 0 + (643646999/1250000000 : ℝ)*x 1 + (-1623893807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2711327019/5000000000 : ℝ)^5023 ≤ (9272207123003/20000000000000 : ℝ)^3999 := by
    have hnat : (2711327019 : ℕ)^5023*20000000000000^3999 ≤ 9272207123003^3999*5000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711327019 5000000000 9272207123003 20000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (643646999/1250000000 : ℝ)^5023 ≤ (43443433574423/100000000000000 : ℝ)^3999 := by
    have hnat : (643646999 : ℕ)^5023*100000000000000^3999 ≤ 43443433574423^3999*1250000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643646999 1250000000 43443433574423 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1623893807/10000000000 : ℝ)^5023 ≤ (1274441349411/12500000000000 : ℝ)^3999 := by
    have hnat : (1623893807 : ℕ)^5023*12500000000000^3999 ≤ 1274441349411^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1623893807 10000000000 1274441349411 12500000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2711327019/5000000000 : ℝ), (643646999/1250000000 : ℝ), (-1623893807/10000000000 : ℝ)] ![(9272207123003/20000000000000 : ℝ), (43443433574423/100000000000000 : ℝ), (1274441349411/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2711327019/5000000000 : ℝ)|^5023 ≤ (9272207123003/20000000000000 : ℝ)^3999
        have hw : |(2711327019/5000000000 : ℝ)|=(2711327019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(643646999/1250000000 : ℝ)|^5023 ≤ (43443433574423/100000000000000 : ℝ)^3999
        have hw : |(643646999/1250000000 : ℝ)|=(643646999/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1623893807/10000000000 : ℝ)|^5023 ≤ (1274441349411/12500000000000 : ℝ)^3999
        have hw : |(-1623893807/10000000000 : ℝ)|=(1623893807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_box_15 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (367276599/1000000000 : ℝ)*x 0 + (551631779/1250000000 : ℝ)*x 1 + (275815909/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (367276599/1000000000 : ℝ)^5023 ≤ (28418665805553/100000000000000 : ℝ)^3999 := by
    have hnat : (367276599 : ℕ)^5023*100000000000000^3999 ≤ 28418665805553^3999*1000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      367276599 1000000000 28418665805553 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (551631779/1250000000 : ℝ)^5023 ≤ (35790665502431/100000000000000 : ℝ)^3999 := by
    have hnat : (551631779 : ℕ)^5023*100000000000000^3999 ≤ 35790665502431^3999*1250000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551631779 1250000000 35790665502431 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (275815909/625000000 : ℝ)^5023 ≤ (7158133736149/20000000000000 : ℝ)^3999 := by
    have hnat : (275815909 : ℕ)^5023*20000000000000^3999 ≤ 7158133736149^3999*625000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275815909 625000000 7158133736149 20000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(367276599/1000000000 : ℝ), (551631779/1250000000 : ℝ), (275815909/625000000 : ℝ)] ![(28418665805553/100000000000000 : ℝ), (35790665502431/100000000000000 : ℝ), (7158133736149/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(367276599/1000000000 : ℝ)|^5023 ≤ (28418665805553/100000000000000 : ℝ)^3999
        have hw : |(367276599/1000000000 : ℝ)|=(367276599/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(551631779/1250000000 : ℝ)|^5023 ≤ (35790665502431/100000000000000 : ℝ)^3999
        have hw : |(551631779/1250000000 : ℝ)|=(551631779/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(275815909/625000000 : ℝ)|^5023 ≤ (7158133736149/20000000000000 : ℝ)^3999
        have hw : |(275815909/625000000 : ℝ)|=(275815909/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1675_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183445147/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (867/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9669/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(66461/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(57571/100000 : ℝ) ∧ (40129/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (17981/20000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (867/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9669/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (867/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9669/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (867/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9669/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (867/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9669/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (867/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9669/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (867/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9669/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9669/100000 : ℝ) ^ (5015/1024 : ℝ) ≤ (1073855447950563/100000000000000000000 : ℝ) := by
    have hpowers : (9669/100000 : ℝ)^5015 ≤ (1073855447950563/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9669 : ℕ)^5015*100000000000000000000^1024 ≤ 1073855447950563^1024*100000^5015 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9669 100000 1073855447950563 100000000000000000000 5015 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9669/100000 : ℝ)) (X := (1073855447950563/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5015 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (867/5000 : ℝ) ^ (5015/1024 : ℝ) ≤ (9380860173598753/50000000000000000000 : ℝ) := by
    have hpowers : (867/5000 : ℝ)^5015 ≤ (9380860173598753/50000000000000000000 : ℝ)^1024 := by
      have hnat : (867 : ℕ)^5015*50000000000000000000^1024 ≤ 9380860173598753^1024*5000^5015 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        867 5000 9380860173598753 50000000000000000000 5015 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (867/5000 : ℝ)) (X := (9380860173598753/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5015 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001073855447950563/50000000000000000000 : ℝ) ≤ (10000043853183711/10000000000000000 : ℝ) ^ (5015/1024 : ℝ) := by
    have hpowers : (50001073855447950563/50000000000000000000 : ℝ)^1024 ≤ (10000043853183711/10000000000000000 : ℝ)^5015 := by
      have hnat : (50001073855447950563 : ℕ)^1024*10000000000000000^5015 ≤ 10000043853183711^5015*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001073855447950563 50000000000000000000 10000043853183711 10000000000000000 1024 5015 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000043853183711/10000000000000000 : ℝ)) (X := (50001073855447950563/50000000000000000000 : ℝ)) (by norm_num) 5015 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100019835575795148069/100000000000000000000 : ℝ) ≤ (10000404985576641/10000000000000000 : ℝ) ^ (5015/1024 : ℝ) := by
    have hpowers : (100019835575795148069/100000000000000000000 : ℝ)^1024 ≤ (10000404985576641/10000000000000000 : ℝ)^5015 := by
      have hnat : (100019835575795148069 : ℕ)^1024*10000000000000000^5015 ≤ 10000404985576641^5015*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100019835575795148069 100000000000000000000 10000404985576641 10000000000000000 1024 5015 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000404985576641/10000000000000000 : ℝ)) (X := (100019835575795148069/100000000000000000000 : ℝ)) (by norm_num) 5015 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25009380860173598753/25000000000000000000 : ℝ) ≤ (10000766117969571/10000000000000000 : ℝ) ^ (5015/1024 : ℝ) := by
    have hpowers : (25009380860173598753/25000000000000000000 : ℝ)^1024 ≤ (10000766117969571/10000000000000000 : ℝ)^5015 := by
      have hnat : (25009380860173598753 : ℕ)^1024*10000000000000000^5015 ≤ 10000766117969571^5015*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009380860173598753 25000000000000000000 10000766117969571 10000000000000000 1024 5015 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000766117969571/10000000000000000 : ℝ)) (X := (25009380860173598753/25000000000000000000 : ℝ)) (by norm_num) 5015 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1073855447950563/100000000000000000000 : ℝ) ≤ ((25567784273185922247/25570000000000000000 : ℝ)+2*(12037746431/25570000000000 : ℝ)*(9669/100000 : ℝ))^(5015/1024 : ℝ) := by
    rw [show (25567784273185922247/25570000000000000000 : ℝ)+2*(12037746431/25570000000000 : ℝ)*(9669/100000 : ℝ)=(10000043853183711/10000000000000000 : ℝ) by norm_num, show 1+2*(1073855447950563/100000000000000000000 : ℝ)=(50001073855447950563/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9380860173598753/50000000000000000000 : ℝ)+(1073855447950563/100000000000000000000 : ℝ) ≤ ((25567784273185922247/25570000000000000000 : ℝ)+(12037746431/25570000000000 : ℝ)*((867/5000 : ℝ)+(9669/100000 : ℝ)))^(5015/1024 : ℝ) := by
    rw [show (25567784273185922247/25570000000000000000 : ℝ)+(12037746431/25570000000000 : ℝ)*((867/5000 : ℝ)+(9669/100000 : ℝ))=(10000404985576641/10000000000000000 : ℝ) by norm_num, show 1+(9380860173598753/50000000000000000000 : ℝ)+(1073855447950563/100000000000000000000 : ℝ)=(100019835575795148069/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9380860173598753/50000000000000000000 : ℝ) ≤ ((25567784273185922247/25570000000000000000 : ℝ)+2*(12037746431/25570000000000 : ℝ)*(867/5000 : ℝ))^(5015/1024 : ℝ) := by
    rw [show (25567784273185922247/25570000000000000000 : ℝ)+2*(12037746431/25570000000000 : ℝ)*(867/5000 : ℝ)=(10000766117969571/10000000000000000 : ℝ) by norm_num, show 1+2*(9380860173598753/50000000000000000000 : ℝ)=(25009380860173598753/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (25567784273185922247/25570000000000000000 : ℝ)*(X 1 0+X 2 0)+(12037746431/25570000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5015/1024 : ℝ)) (lo := (9669/100000 : ℝ)) (hi := (867/5000 : ℝ)) (c := (25567784273185922247/25570000000000000000 : ℝ)) (alpha := (12037746431/25570000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (25567784273185922247/25570000000000000000 : ℝ)*(X 0 1+X 2 1)+(12037746431/25570000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5015/1024 : ℝ)) (lo := (9669/100000 : ℝ)) (hi := (867/5000 : ℝ)) (c := (25567784273185922247/25570000000000000000 : ℝ)) (alpha := (12037746431/25570000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (25567784273185922247/25570000000000000000 : ℝ)*(X 0 2+X 1 2)+(12037746431/25570000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5015/1024 : ℝ)) (lo := (9669/100000 : ℝ)) (hi := (867/5000 : ℝ)) (c := (25567784273185922247/25570000000000000000 : ℝ)) (alpha := (12037746431/25570000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-600460947/5000000000 : ℝ)*X 0 0+(5436554353/10000000000 : ℝ)*X 0 1+(5436553547/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2613013783/5000000000 : ℝ)*X 1 0+(-150026059/1000000000 : ℝ)*X 1 1+(5436554573/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5226027101/10000000000 : ℝ)*X 2 0+(1359138523/2500000000 : ℝ)*X 2 1+(-1500261899/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4538954929/10000000000 : ℝ)*X 0 0+(3982526357/10000000000 : ℝ)*X 0 1+(995630997/2500000000 : ℝ)*X 0 2+(4538954929/10000000000 : ℝ)*X 1 0+(3982526357/10000000000 : ℝ)*X 1 1+(995630997/2500000000 : ℝ)*X 1 2+(4538954929/10000000000 : ℝ)*X 2 0+(3982526357/10000000000 : ℝ)*X 2 1+(995630997/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-959492653/5000000000 : ℝ)*X 0 0+(5174572389/10000000000 : ℝ)*X 0 1+(2587285417/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2702627151/5000000000 : ℝ)*X 1 0+(-1613419559/10000000000 : ℝ)*X 1 1+(5174572619/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((540525489/1000000000 : ℝ)*X 2 0+(2587285757/5000000000 : ℝ)*X 2 1+(-806710123/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((469002777/1250000000 : ℝ)*X 0 0+(2187550487/5000000000 : ℝ)*X 0 1+(4375100301/10000000000 : ℝ)*X 0 2+(469002777/1250000000 : ℝ)*X 1 0+(2187550487/5000000000 : ℝ)*X 1 1+(4375100301/10000000000 : ℝ)*X 1 2+(469002777/1250000000 : ℝ)*X 2 0+(2187550487/5000000000 : ℝ)*X 2 1+(4375100301/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-882628277/5000000000 : ℝ)*X 0 0+(4983179847/10000000000 : ℝ)*X 0 1+(5480759409/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5195789601/10000000000 : ℝ)*X 1 0+(-1480286413/10000000000 : ℝ)*X 1 1+(1370190007/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2597894857/5000000000 : ℝ)*X 2 0+(5480759993/10000000000 : ℝ)*X 2 1+(-296057261/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4666676711/10000000000 : ℝ)*X 0 0+(1958055597/5000000000 : ℝ)*X 0 1+(3916110449/10000000000 : ℝ)*X 0 2+(4666676711/10000000000 : ℝ)*X 1 0+(1958055597/5000000000 : ℝ)*X 1 1+(3916110449/10000000000 : ℝ)*X 1 2+(4666676711/10000000000 : ℝ)*X 2 0+(1958055597/5000000000 : ℝ)*X 2 1+(3916110449/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-84400991/625000000 : ℝ)*X 0 0+(2809033423/5000000000 : ℝ)*X 0 1+(64364699/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2711326993/5000000000 : ℝ)*X 1 0+(-202986733/1250000000 : ℝ)*X 1 1+(5149176001/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2711327019/5000000000 : ℝ)*X 2 0+(643646999/1250000000 : ℝ)*X 2 1+(-1623893807/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((367276599/1000000000 : ℝ)*X 0 0+(551631779/1250000000 : ℝ)*X 0 1+(275815909/625000000 : ℝ)*X 0 2+(367276599/1000000000 : ℝ)*X 1 0+(551631779/1250000000 : ℝ)*X 1 1+(275815909/625000000 : ℝ)*X 1 2+(367276599/1000000000 : ℝ)*X 2 0+(551631779/1250000000 : ℝ)*X 2 1+(275815909/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-66461/100000 : ℝ) ≤ (-212417387634844566595217334519039/319625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21271853/100000000000000 : ℝ)*(upper0) + (313553463/100000000000000 : ℝ)*(upper3) + (186932349/100000000000000 : ℝ)*(upper5) + (633268279936579/50000000000000 : ℝ)*(major0) + (633268279936579/50000000000000 : ℝ)*(major1) + (633268279936579/50000000000000 : ℝ)*(major2) + (3675430937/100000000000000 : ℝ)*(sp1) + (9793364647/100000000000000 : ℝ)*(sp2) + (3314936663/50000000000000 : ℝ)*(sp3) + (372961014480627/20000000000000 : ℝ)*(sp4) + (932402586286351/50000000000000 : ℝ)*(sp5) + (1864799054638993/100000000000000 : ℝ)*(sp6) + (345205206680199/50000000000000 : ℝ)*(sp7) + (471950063/12500000000000 : ℝ)*(sp8) + (172604260808431/25000000000000 : ℝ)*(f.failure) + (46620221200091/2500000000000 : ℝ)*(f.sum) + (1551630743669/639250000000000000000000000 : ℝ)*base66 + (4647608546129673013/1278500000000000000000000000000000 : ℝ)*base67 + (11302243012892173013/1278500000000000000000000000000000 : ℝ)*base69 + (5727383964046173013/1278500000000000000000000000000000 : ℝ)*base71 + (2343885532303/1278500000000000000000000000 : ℝ)*base74 + (5849741327321673013/1278500000000000000000000000000000 : ℝ)*base75 + (1573810896677326987/1278500000000000000000000000000000 : ℝ)*base78 + (6279551759474173013/1278500000000000000000000000000000 : ℝ)*base79 + (8077393854261/2557000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (13634357/2500000000000000000000 : ℝ)*base89 + (13634357/2500000000000000000000 : ℝ)*base91 + (13634357/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (57571/100000 : ℝ) ≤ (184017637805548923599953183856721/319625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (59238991/50000000000000 : ℝ)*(lower0) + (32103083/20000000000000 : ℝ)*(upper2) + (135645111/100000000000000 : ℝ)*(upper3) + (16740761/12500000000000 : ℝ)*(lower5) + (340318708899073/25000000000000 : ℝ)*(major0) + (340318708899073/25000000000000 : ℝ)*(major1) + (340318708899073/25000000000000 : ℝ)*(major2) + (196129770870849/10000000000000 : ℝ)*(sp0) + (245161900666081/12500000000000 : ℝ)*(sp1) + (61290300731751/3125000000000 : ℝ)*(sp2) + (742060429518631/100000000000000 : ℝ)*(sp3) + (1251689921/50000000000000 : ℝ)*(sp5) + (67447751/12500000000000 : ℝ)*(sp7) + (4042646229/50000000000000 : ℝ)*(sp10) + (742060969100639/100000000000000 : ℝ)*(f.failure) + (196129770870849/10000000000000 : ℝ)*(f.sum) + (1811039907243/511400000000000000000000000 : ℝ)*base66 + (3055188390973127031/639250000000000000000000000000000 : ℝ)*base67 + (1339550806920877031/639250000000000000000000000000000 : ℝ)*base69 + (1954864657685627031/639250000000000000000000000000000 : ℝ)*base71 + (33889369585273/2557000000000000000000000000 : ℝ)*base74 + (3561878199444877031/639250000000000000000000000000000 : ℝ)*base75 + (1737539351699627031/639250000000000000000000000000000 : ℝ)*base77 + (5624028088529127031/639250000000000000000000000000000 : ℝ)*base79 + (4262771931421/1278500000000000000000000000 : ℝ)*base82 + (20851067/10000000000000000000000 : ℝ)*base90 + (20851067/10000000000000000000000 : ℝ)*base92 + (20851067/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (40129/50000 : ℝ) ≤ (513067597256699153982238969268199/639250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12663053/50000000000000 : ℝ)*(upper2) + (57583489/100000000000000 : ℝ)*(upper3) + (16400027/20000000000000 : ℝ)*(upper4) + (1399762693926661/100000000000000 : ℝ)*(major0) + (1399762693926661/100000000000000 : ℝ)*(major1) + (1399762693926661/100000000000000 : ℝ)*(major2) + (34614831/2500000000000 : ℝ)*(sp0) + (16500118677/100000000000000 : ℝ)*(sp1) + (3466613961/12500000000000 : ℝ)*(sp2) + (4526058337/50000000000000 : ℝ)*(sp3) + (2009728830200391/100000000000000 : ℝ)*(sp8) + (1004856857337477/50000000000000 : ℝ)*(sp9) + (2009702481881943/100000000000000 : ℝ)*(sp10) + (381516249175543/50000000000000 : ℝ)*(sp11) + (9538019380847/1250000000000 : ℝ)*(f.failure) + (2009730214793631/100000000000000 : ℝ)*(f.sum) + (169088296829/39953125000000000000000000 : ℝ)*base65 + (8516538720114327267/2557000000000000000000000000000000 : ℝ)*base67 + (3879535253867672733/2557000000000000000000000000000000 : ℝ)*base70 + (1778790971761327267/2557000000000000000000000000000000 : ℝ)*base71 + (141305554119/79906250000000000000000000 : ℝ)*base74 + (3842483457394327267/2557000000000000000000000000000000 : ℝ)*base75 + (10555470363283327267/2557000000000000000000000000000000 : ℝ)*base77 + (4539279156628327267/2557000000000000000000000000000000 : ℝ)*base79 + (15056140925461/2557000000000000000000000000 : ℝ)*base82 + (649509/125000000000000000000 : ℝ)*base89 + (649509/125000000000000000000 : ℝ)*base91 + (649509/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-17981/20000 : ℝ) ≤ (-229879750461625544426025469604211/255700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2083189/10000000000000 : ℝ)*(lower1) + (9836963/100000000000000 : ℝ)*(lower2) + (4164909/25000000000000 : ℝ)*(upper5) + (289058647460557/20000000000000 : ℝ)*(major0) + (289058647460557/20000000000000 : ℝ)*(major1) + (289058647460557/20000000000000 : ℝ)*(major2) + (353587799/100000000000000 : ℝ)*(sp0) + (5401664971/100000000000000 : ℝ)*(sp5) + (61220037/1000000000000 : ℝ)*(sp6) + (1441789039/100000000000000 : ℝ)*(sp7) + (1066346121630291/50000000000000 : ℝ)*(sp12) + (2132687195183409/100000000000000 : ℝ)*(sp13) + (53317161871117/2500000000000 : ℝ)*(sp14) + (98482476645373/12500000000000 : ℝ)*(sp15) + (98482656869003/12500000000000 : ℝ)*(f.failure) + (106634629842419/5000000000000 : ℝ)*(f.sum) + (592942266971/319625000000000000000000000 : ℝ)*base65 + (3716826221268111579/511400000000000000000000000000000 : ℝ)*base67 + (398309259449111579/511400000000000000000000000000000 : ℝ)*base69 + (2645595410328311579/511400000000000000000000000000000 : ℝ)*base71 + (24331035127957/2557000000000000000000000000 : ℝ)*base73 + (3254356564148111579/511400000000000000000000000000000 : ℝ)*base75 + (2557359822834711579/511400000000000000000000000000000 : ℝ)*base77 + (2533691612040711579/511400000000000000000000000000000 : ℝ)*base79 + (3749672025579/511400000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (2578441/1250000000000000000000 : ℝ)*base89 + (2578441/1250000000000000000000 : ℝ)*base91 + (2578441/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1675_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183445147/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (867/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9669/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66461/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(57571/100000 : ℝ) else (40129/50000 : ℝ) ≤ X j i ∧ X j i ≤ (17981/20000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1675_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1675_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183445147/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17379/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1927/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66461/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(57571/100000 : ℝ) else (40129/50000 : ℝ) ≤ X j i ∧ X j i ≤ (17981/20000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1675_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1675_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1675_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183445147/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17379/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1927/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66461/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(57571/100000 : ℝ) else (40129/50000 : ℝ) ≤ X j i ∧ X j i ≤ (17981/20000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1675_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

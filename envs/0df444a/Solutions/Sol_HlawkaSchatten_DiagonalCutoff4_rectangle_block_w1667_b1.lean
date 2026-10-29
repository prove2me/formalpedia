-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1667_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:19:38.39369+00:00
-- url     : https://prove2.me/submissions/ea5deef5-ea85-465a-bfd1-7c47d79a5fe2

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
theorem support_rectangle_w1667_s3_0 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1570651623/10000000000 : ℝ)*x 0 + (2721298171/5000000000 : ℝ)*x 1 + (2592435733/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1570651623/10000000000 : ℝ)^4987 ≤ (304231990433/3125000000000 : ℝ)^3963 := by
    have hnat : (1570651623 : ℕ)^4987*3125000000000^3963 ≤ 304231990433^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1570651623 10000000000 304231990433 3125000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2721298171/5000000000 : ℝ)^4987 ≤ (23254716312249/50000000000000 : ℝ)^3963 := by
    have hnat : (2721298171 : ℕ)^4987*50000000000000^3963 ≤ 23254716312249^3963*5000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721298171 5000000000 23254716312249 50000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2592435733/5000000000 : ℝ)^4987 ≤ (43755143660091/100000000000000 : ℝ)^3963 := by
    have hnat : (2592435733 : ℕ)^4987*100000000000000^3963 ≤ 43755143660091^3963*5000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592435733 5000000000 43755143660091 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1570651623/10000000000 : ℝ), (2721298171/5000000000 : ℝ), (2592435733/5000000000 : ℝ)] ![(304231990433/3125000000000 : ℝ), (23254716312249/50000000000000 : ℝ), (43755143660091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1570651623/10000000000 : ℝ)|^4987 ≤ (304231990433/3125000000000 : ℝ)^3963
        have hw : |(-1570651623/10000000000 : ℝ)|=(1570651623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2721298171/5000000000 : ℝ)|^4987 ≤ (23254716312249/50000000000000 : ℝ)^3963
        have hw : |(2721298171/5000000000 : ℝ)|=(2721298171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2592435733/5000000000 : ℝ)|^4987 ≤ (43755143660091/100000000000000 : ℝ)^3963
        have hw : |(2592435733/5000000000 : ℝ)|=(2592435733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_s3_1 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672585761/5000000000 : ℝ)*x 0 + (-1703239269/10000000000 : ℝ)*x 1 + (1036974293/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672585761/5000000000 : ℝ)^4987 ≤ (22732103797277/50000000000000 : ℝ)^3963 := by
    have hnat : (2672585761 : ℕ)^4987*50000000000000^3963 ≤ 22732103797277^3963*5000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672585761 5000000000 22732103797277 50000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1703239269/10000000000 : ℝ)^4987 ≤ (86245189973/800000000000 : ℝ)^3963 := by
    have hnat : (1703239269 : ℕ)^4987*800000000000^3963 ≤ 86245189973^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1703239269 10000000000 86245189973 800000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036974293/2000000000 : ℝ)^4987 ≤ (43755143649471/100000000000000 : ℝ)^3963 := by
    have hnat : (1036974293 : ℕ)^4987*100000000000000^3963 ≤ 43755143649471^3963*2000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036974293 2000000000 43755143649471 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672585761/5000000000 : ℝ), (-1703239269/10000000000 : ℝ), (1036974293/2000000000 : ℝ)] ![(22732103797277/50000000000000 : ℝ), (86245189973/800000000000 : ℝ), (43755143649471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672585761/5000000000 : ℝ)|^4987 ≤ (22732103797277/50000000000000 : ℝ)^3963
        have hw : |(2672585761/5000000000 : ℝ)|=(2672585761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1703239269/10000000000 : ℝ)|^4987 ≤ (86245189973/800000000000 : ℝ)^3963
        have hw : |(-1703239269/10000000000 : ℝ)|=(1703239269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1036974293/2000000000 : ℝ)|^4987 ≤ (43755143649471/100000000000000 : ℝ)^3963
        have hw : |(1036974293/2000000000 : ℝ)|=(1036974293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_s3_2 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345171521/10000000000 : ℝ)*x 0 + (2592435733/5000000000 : ℝ)*x 1 + (-425809817/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345171521/10000000000 : ℝ)^4987 ≤ (909284151677/2000000000000 : ℝ)^3963 := by
    have hnat : (5345171521 : ℕ)^4987*2000000000000^3963 ≤ 909284151677^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345171521 10000000000 909284151677 2000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2592435733/5000000000 : ℝ)^4987 ≤ (43755143660091/100000000000000 : ℝ)^3963 := by
    have hnat : (2592435733 : ℕ)^4987*100000000000000^3963 ≤ 43755143660091^3963*5000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592435733 5000000000 43755143660091 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (425809817/2500000000 : ℝ)^4987 ≤ (539032436933/5000000000000 : ℝ)^3963 := by
    have hnat : (425809817 : ℕ)^4987*5000000000000^3963 ≤ 539032436933^3963*2500000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425809817 2500000000 539032436933 5000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345171521/10000000000 : ℝ), (2592435733/5000000000 : ℝ), (-425809817/2500000000 : ℝ)] ![(909284151677/2000000000000 : ℝ), (43755143660091/100000000000000 : ℝ), (539032436933/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345171521/10000000000 : ℝ)|^4987 ≤ (909284151677/2000000000000 : ℝ)^3963
        have hw : |(5345171521/10000000000 : ℝ)|=(5345171521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2592435733/5000000000 : ℝ)|^4987 ≤ (43755143660091/100000000000000 : ℝ)^3963
        have hw : |(2592435733/5000000000 : ℝ)|=(2592435733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-425809817/2500000000 : ℝ)|^4987 ≤ (539032436933/5000000000000 : ℝ)^3963
        have hw : |(-425809817/2500000000 : ℝ)|=(425809817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_s3_3 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2083941863/5000000000 : ℝ)*x 0 + (767435707/2000000000 : ℝ)*x 1 + (564784803/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2083941863/5000000000 : ℝ)^4987 ≤ (33243408319827/100000000000000 : ℝ)^3963 := by
    have hnat : (2083941863 : ℕ)^4987*100000000000000^3963 ≤ 33243408319827^3963*5000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083941863 5000000000 33243408319827 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (767435707/2000000000 : ℝ)^4987 ≤ (29958828273781/100000000000000 : ℝ)^3963 := by
    have hnat : (767435707 : ℕ)^4987*100000000000000^3963 ≤ 29958828273781^3963*2000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      767435707 2000000000 29958828273781 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (564784803/1250000000 : ℝ)^4987 ≤ (36797763398377/100000000000000 : ℝ)^3963 := by
    have hnat : (564784803 : ℕ)^4987*100000000000000^3963 ≤ 36797763398377^3963*1250000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564784803 1250000000 36797763398377 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2083941863/5000000000 : ℝ), (767435707/2000000000 : ℝ), (564784803/1250000000 : ℝ)] ![(33243408319827/100000000000000 : ℝ), (29958828273781/100000000000000 : ℝ), (36797763398377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2083941863/5000000000 : ℝ)|^4987 ≤ (33243408319827/100000000000000 : ℝ)^3963
        have hw : |(2083941863/5000000000 : ℝ)|=(2083941863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(767435707/2000000000 : ℝ)|^4987 ≤ (29958828273781/100000000000000 : ℝ)^3963
        have hw : |(767435707/2000000000 : ℝ)|=(767435707/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(564784803/1250000000 : ℝ)|^4987 ≤ (36797763398377/100000000000000 : ℝ)^3963
        have hw : |(564784803/1250000000 : ℝ)|=(564784803/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_s3_4 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-196339253/1250000000 : ℝ)*x 0 + (5186836323/10000000000 : ℝ)*x 1 + (544061051/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (196339253/1250000000 : ℝ)^4987 ≤ (2433977604829/25000000000000 : ℝ)^3963 := by
    have hnat : (196339253 : ℕ)^4987*25000000000000^3963 ≤ 2433977604829^3963*1250000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196339253 1250000000 2433977604829 25000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5186836323/10000000000 : ℝ)^4987 ≤ (8755202118643/20000000000000 : ℝ)^3963 := by
    have hnat : (5186836323 : ℕ)^4987*20000000000000^3963 ≤ 8755202118643^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5186836323 10000000000 8755202118643 20000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (544061051/1000000000 : ℝ)^4987 ≤ (46488078968501/100000000000000 : ℝ)^3963 := by
    have hnat : (544061051 : ℕ)^4987*100000000000000^3963 ≤ 46488078968501^3963*1000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544061051 1000000000 46488078968501 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-196339253/1250000000 : ℝ), (5186836323/10000000000 : ℝ), (544061051/1000000000 : ℝ)] ![(2433977604829/25000000000000 : ℝ), (8755202118643/20000000000000 : ℝ), (46488078968501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-196339253/1250000000 : ℝ)|^4987 ≤ (2433977604829/25000000000000 : ℝ)^3963
        have hw : |(-196339253/1250000000 : ℝ)|=(196339253/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5186836323/10000000000 : ℝ)|^4987 ≤ (8755202118643/20000000000000 : ℝ)^3963
        have hw : |(5186836323/10000000000 : ℝ)|=(5186836323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(544061051/1000000000 : ℝ)|^4987 ≤ (46488078968501/100000000000000 : ℝ)^3963
        have hw : |(544061051/1000000000 : ℝ)|=(544061051/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_s3_5 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055238693/2000000000 : ℝ)*x 0 + (-1447500413/10000000000 : ℝ)*x 1 + (5440610629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055238693/2000000000 : ℝ)^4987 ≤ (11181785035703/25000000000000 : ℝ)^3963 := by
    have hnat : (1055238693 : ℕ)^4987*25000000000000^3963 ≤ 11181785035703^3963*2000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055238693 2000000000 11181785035703 25000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1447500413/10000000000 : ℝ)^4987 ≤ (8784779603167/100000000000000 : ℝ)^3963 := by
    have hnat : (1447500413 : ℕ)^4987*100000000000000^3963 ≤ 8784779603167^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1447500413 10000000000 8784779603167 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5440610629/10000000000 : ℝ)^4987 ≤ (2905505015503/6250000000000 : ℝ)^3963 := by
    have hnat : (5440610629 : ℕ)^4987*6250000000000^3963 ≤ 2905505015503^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440610629 10000000000 2905505015503 6250000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055238693/2000000000 : ℝ), (-1447500413/10000000000 : ℝ), (5440610629/10000000000 : ℝ)] ![(11181785035703/25000000000000 : ℝ), (8784779603167/100000000000000 : ℝ), (2905505015503/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055238693/2000000000 : ℝ)|^4987 ≤ (11181785035703/25000000000000 : ℝ)^3963
        have hw : |(1055238693/2000000000 : ℝ)|=(1055238693/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1447500413/10000000000 : ℝ)|^4987 ≤ (8784779603167/100000000000000 : ℝ)^3963
        have hw : |(-1447500413/10000000000 : ℝ)|=(1447500413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5440610629/10000000000 : ℝ)|^4987 ≤ (2905505015503/6250000000000 : ℝ)^3963
        have hw : |(5440610629/10000000000 : ℝ)|=(5440610629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_s3_6 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (527619399/1000000000 : ℝ)*x 0 + (42504769/78125000 : ℝ)*x 1 + (-289499991/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527619399/1000000000 : ℝ)^4987 ≤ (44727145743289/100000000000000 : ℝ)^3963 := by
    have hnat : (527619399 : ℕ)^4987*100000000000000^3963 ≤ 44727145743289^3963*1000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527619399 1000000000 44727145743289 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42504769/78125000 : ℝ)^4987 ≤ (23244039064903/50000000000000 : ℝ)^3963 := by
    have hnat : (42504769 : ℕ)^4987*50000000000000^3963 ≤ 23244039064903^3963*78125000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42504769 78125000 23244039064903 50000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (289499991/2000000000 : ℝ)^4987 ≤ (1098097013173/12500000000000 : ℝ)^3963 := by
    have hnat : (289499991 : ℕ)^4987*12500000000000^3963 ≤ 1098097013173^3963*2000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      289499991 2000000000 1098097013173 12500000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527619399/1000000000 : ℝ), (42504769/78125000 : ℝ), (-289499991/2000000000 : ℝ)] ![(44727145743289/100000000000000 : ℝ), (23244039064903/50000000000000 : ℝ), (1098097013173/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527619399/1000000000 : ℝ)|^4987 ≤ (44727145743289/100000000000000 : ℝ)^3963
        have hw : |(527619399/1000000000 : ℝ)|=(527619399/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42504769/78125000 : ℝ)|^4987 ≤ (23244039064903/50000000000000 : ℝ)^3963
        have hw : |(42504769/78125000 : ℝ)|=(42504769/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-289499991/2000000000 : ℝ)|^4987 ≤ (1098097013173/12500000000000 : ℝ)^3963
        have hw : |(-289499991/2000000000 : ℝ)|=(289499991/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_s3_7 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2084023809/5000000000 : ℝ)*x 0 + (225654263/500000000 : ℝ)*x 1 + (3842426481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2084023809/5000000000 : ℝ)^4987 ≤ (33245053317191/100000000000000 : ℝ)^3963 := by
    have hnat : (2084023809 : ℕ)^4987*100000000000000^3963 ≤ 33245053317191^3963*5000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084023809 5000000000 33245053317191 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (225654263/500000000 : ℝ)^4987 ≤ (7348909748591/20000000000000 : ℝ)^3963 := by
    have hnat : (225654263 : ℕ)^4987*20000000000000^3963 ≤ 7348909748591^3963*500000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225654263 500000000 7348909748591 20000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3842426481/10000000000 : ℝ)^4987 ≤ (15005198961391/50000000000000 : ℝ)^3963 := by
    have hnat : (3842426481 : ℕ)^4987*50000000000000^3963 ≤ 15005198961391^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3842426481 10000000000 15005198961391 50000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2084023809/5000000000 : ℝ), (225654263/500000000 : ℝ), (3842426481/10000000000 : ℝ)] ![(33245053317191/100000000000000 : ℝ), (7348909748591/20000000000000 : ℝ), (15005198961391/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2084023809/5000000000 : ℝ)|^4987 ≤ (33245053317191/100000000000000 : ℝ)^3963
        have hw : |(2084023809/5000000000 : ℝ)|=(2084023809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(225654263/500000000 : ℝ)|^4987 ≤ (7348909748591/20000000000000 : ℝ)^3963
        have hw : |(225654263/500000000 : ℝ)|=(225654263/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3842426481/10000000000 : ℝ)|^4987 ≤ (15005198961391/50000000000000 : ℝ)^3963
        have hw : |(3842426481/10000000000 : ℝ)|=(3842426481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1667_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (182137009/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4073/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10703/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (336/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16237/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4073/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10703/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4073/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10703/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4073/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10703/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4073/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10703/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4073/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10703/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4073/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10703/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10703/100000 : ℝ) ^ (4983/1024 : ℝ) ≤ (1893952893683279/100000000000000000000 : ℝ) := by
    have hpowers : (10703/100000 : ℝ)^4983 ≤ (1893952893683279/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10703 : ℕ)^4983*100000000000000000000^1024 ≤ 1893952893683279^1024*100000^4983 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10703 100000 1893952893683279 100000000000000000000 4983 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10703/100000 : ℝ)) (X := (1893952893683279/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4983 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4073/25000 : ℝ) ^ (4983/1024 : ℝ) ≤ (7315958233908489/50000000000000000000 : ℝ) := by
    have hpowers : (4073/25000 : ℝ)^4983 ≤ (7315958233908489/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4073 : ℕ)^4983*50000000000000000000^1024 ≤ 7315958233908489^1024*25000^4983 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4073 25000 7315958233908489 50000000000000000000 4983 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4073/25000 : ℝ)) (X := (7315958233908489/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4983 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001893952893683279/50000000000000000000 : ℝ) ≤ (10000077839798539/10000000000000000 : ℝ) ^ (4983/1024 : ℝ) := by
    have hpowers : (50001893952893683279/50000000000000000000 : ℝ)^1024 ≤ (10000077839798539/10000000000000000 : ℝ)^4983 := by
      have hnat : (50001893952893683279 : ℕ)^1024*10000000000000000^4983 ≤ 10000077839798539^4983*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001893952893683279 50000000000000000000 10000077839798539 10000000000000000 1024 4983 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000077839798539/10000000000000000 : ℝ)) (X := (50001893952893683279/50000000000000000000 : ℝ)) (by norm_num) 4983 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100016525869361500257/100000000000000000000 : ℝ) ≤ (2000067916433431/2000000000000000 : ℝ) ^ (4983/1024 : ℝ) := by
    have hpowers : (100016525869361500257/100000000000000000000 : ℝ)^1024 ≤ (2000067916433431/2000000000000000 : ℝ)^4983 := by
      have hnat : (100016525869361500257 : ℕ)^1024*2000000000000000^4983 ≤ 2000067916433431^4983*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100016525869361500257 100000000000000000000 2000067916433431 2000000000000000 1024 4983 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000067916433431/2000000000000000 : ℝ)) (X := (100016525869361500257/100000000000000000000 : ℝ)) (by norm_num) 4983 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25007315958233908489/25000000000000000000 : ℝ) ≤ (10000601324535771/10000000000000000 : ℝ) ^ (4983/1024 : ℝ) := by
    have hpowers : (25007315958233908489/25000000000000000000 : ℝ)^1024 ≤ (10000601324535771/10000000000000000 : ℝ)^4983 := by
      have hnat : (25007315958233908489 : ℕ)^1024*10000000000000000^4983 ≤ 10000601324535771^4983*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007315958233908489 25000000000000000000 10000601324535771 10000000000000000 1024 4983 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000601324535771/10000000000000000 : ℝ)) (X := (25007315958233908489/25000000000000000000 : ℝ)) (by norm_num) 4983 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1893952893683279/100000000000000000000 : ℝ) ≤ ((447078657515931523/447120000000000000 : ℝ)+2*(32717796077/69862500000000 : ℝ)*(10703/100000 : ℝ))^(4983/1024 : ℝ) := by
    rw [show (447078657515931523/447120000000000000 : ℝ)+2*(32717796077/69862500000000 : ℝ)*(10703/100000 : ℝ)=(10000077839798539/10000000000000000 : ℝ) by norm_num, show 1+2*(1893952893683279/100000000000000000000 : ℝ)=(50001893952893683279/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7315958233908489/50000000000000000000 : ℝ)+(1893952893683279/100000000000000000000 : ℝ) ≤ ((447078657515931523/447120000000000000 : ℝ)+(32717796077/69862500000000 : ℝ)*((4073/25000 : ℝ)+(10703/100000 : ℝ)))^(4983/1024 : ℝ) := by
    rw [show (447078657515931523/447120000000000000 : ℝ)+(32717796077/69862500000000 : ℝ)*((4073/25000 : ℝ)+(10703/100000 : ℝ))=(2000067916433431/2000000000000000 : ℝ) by norm_num, show 1+(7315958233908489/50000000000000000000 : ℝ)+(1893952893683279/100000000000000000000 : ℝ)=(100016525869361500257/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7315958233908489/50000000000000000000 : ℝ) ≤ ((447078657515931523/447120000000000000 : ℝ)+2*(32717796077/69862500000000 : ℝ)*(4073/25000 : ℝ))^(4983/1024 : ℝ) := by
    rw [show (447078657515931523/447120000000000000 : ℝ)+2*(32717796077/69862500000000 : ℝ)*(4073/25000 : ℝ)=(10000601324535771/10000000000000000 : ℝ) by norm_num, show 1+2*(7315958233908489/50000000000000000000 : ℝ)=(25007315958233908489/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (447078657515931523/447120000000000000 : ℝ)*(X 1 0+X 2 0)+(32717796077/69862500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4983/1024 : ℝ)) (lo := (10703/100000 : ℝ)) (hi := (4073/25000 : ℝ)) (c := (447078657515931523/447120000000000000 : ℝ)) (alpha := (32717796077/69862500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (447078657515931523/447120000000000000 : ℝ)*(X 0 1+X 2 1)+(32717796077/69862500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4983/1024 : ℝ)) (lo := (10703/100000 : ℝ)) (hi := (4073/25000 : ℝ)) (c := (447078657515931523/447120000000000000 : ℝ)) (alpha := (32717796077/69862500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (447078657515931523/447120000000000000 : ℝ)*(X 0 2+X 1 2)+(32717796077/69862500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4983/1024 : ℝ)) (lo := (10703/100000 : ℝ)) (hi := (4073/25000 : ℝ)) (c := (447078657515931523/447120000000000000 : ℝ)) (alpha := (32717796077/69862500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1570651623/10000000000 : ℝ)*X 0 0+(2721298171/5000000000 : ℝ)*X 0 1+(2592435733/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672585761/5000000000 : ℝ)*X 1 0+(-1703239269/10000000000 : ℝ)*X 1 1+(1036974293/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345171521/10000000000 : ℝ)*X 2 0+(2592435733/5000000000 : ℝ)*X 2 1+(-425809817/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2083941863/5000000000 : ℝ)*X 0 0+(767435707/2000000000 : ℝ)*X 0 1+(564784803/1250000000 : ℝ)*X 0 2+(2083941863/5000000000 : ℝ)*X 1 0+(767435707/2000000000 : ℝ)*X 1 1+(564784803/1250000000 : ℝ)*X 1 2+(2083941863/5000000000 : ℝ)*X 2 0+(767435707/2000000000 : ℝ)*X 2 1+(564784803/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-196339253/1250000000 : ℝ)*X 0 0+(5186836323/10000000000 : ℝ)*X 0 1+(544061051/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1055238693/2000000000 : ℝ)*X 1 0+(-1447500413/10000000000 : ℝ)*X 1 1+(5440610629/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((527619399/1000000000 : ℝ)*X 2 0+(42504769/78125000 : ℝ)*X 2 1+(-289499991/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2084023809/5000000000 : ℝ)*X 0 0+(225654263/500000000 : ℝ)*X 0 1+(3842426481/10000000000 : ℝ)*X 0 2+(2084023809/5000000000 : ℝ)*X 1 0+(225654263/500000000 : ℝ)*X 1 1+(3842426481/10000000000 : ℝ)*X 1 2+(2084023809/5000000000 : ℝ)*X 2 0+(225654263/500000000 : ℝ)*X 2 1+(3842426481/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2454755665041882127983043/310500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24654989/2000000000000 : ℝ)*(base19) + (1154089421/100000000000000 : ℝ)*(base23) + (41657121/100000000000000 : ℝ)*(lower2) + (192367377/100000000000000 : ℝ)*(upper3) + (68683981/50000000000000 : ℝ)*(upper5) + (668545529821023/25000000000000 : ℝ)*(major0) + (668545529821023/25000000000000 : ℝ)*(major1) + (668545529821023/25000000000000 : ℝ)*(major2) + (121253835695577/3125000000000 : ℝ)*(sp0) + (970034295720223/25000000000000 : ℝ)*(sp1) + (1940068630770461/50000000000000 : ℝ)*(sp2) + (367054783530617/25000000000000 : ℝ)*(sp3) + (7836685939/50000000000000 : ℝ)*(sp4) + (6425288191/100000000000000 : ℝ)*(sp7) + (1468225559410659/100000000000000 : ℝ)*(f.failure) + (1940069207815171/50000000000000 : ℝ)*(f.sum) + (20634808582153/4657500000000000000000000000 : ℝ)*base66 + (804420663352619/1242000000000000000000000000000 : ℝ)*base68 + (523095224722619/1242000000000000000000000000000 : ℝ)*base70 + (2970464322511381/1242000000000000000000000000000 : ℝ)*base71 + (11948717954939/2328750000000000000000000000 : ℝ)*base74 + (6048406428514619/1242000000000000000000000000000 : ℝ)*base76 + (3257078602084619/1242000000000000000000000000000 : ℝ)*base78 + (13208359578892619/1242000000000000000000000000000 : ℝ)*base80 + (32008129359019/9315000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (32978931/10000000000000000000000 : ℝ)*base89 + (32978931/10000000000000000000000 : ℝ)*base91 + (32978931/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (29633452333333089334881371/3726000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (46746359/4000000000000 : ℝ)*(base19) + (1886061367/100000000000000 : ℝ)*(base23) + (54916357/50000000000000 : ℝ)*(upper2) + (50668701/25000000000000 : ℝ)*(upper3) + (271466149/100000000000000 : ℝ)*(upper5) + (1357896070898377/50000000000000 : ℝ)*(major0) + (1357896070898377/50000000000000 : ℝ)*(major1) + (1357896070898377/50000000000000 : ℝ)*(major2) + (14743710951/100000000000000 : ℝ)*(sp1) + (5926027093/25000000000000 : ℝ)*(sp2) + (3940513007326237/100000000000000 : ℝ)*(sp4) + (492562136869539/12500000000000 : ℝ)*(sp5) + (1970243708578249/50000000000000 : ℝ)*(sp6) + (1491071011162127/100000000000000 : ℝ)*(sp7) + (1491071011162127/100000000000000 : ℝ)*(f.failure) + (3940513007326237/100000000000000 : ℝ)*(f.sum) + (48718095351323/13972500000000000000000000000 : ℝ)*base66 + (6597222647849257/7452000000000000000000000000000 : ℝ)*base67 + (6431715440622743/7452000000000000000000000000000 : ℝ)*base70 + (89406501503634743/7452000000000000000000000000000 : ℝ)*base72 + (8384992288561/27945000000000000000000000000 : ℝ)*base74 + (76367264363658743/7452000000000000000000000000000 : ℝ)*base76 + (64289403826794743/7452000000000000000000000000000 : ℝ)*base78 + (61985003029325257/7452000000000000000000000000000 : ℝ)*base79 + (55896347513519/27945000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (25858143/10000000000000000000000 : ℝ)*base89 + (25858143/10000000000000000000000 : ℝ)*base91 + (25858143/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1667_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (182137009/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4073/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10703/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (336/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16237/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1667_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1667_s4_0 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-78534091/500000000 : ℝ)*x 0 + (5442443469/10000000000 : ℝ)*x 1 + (648125511/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (78534091/500000000 : ℝ)^4987 ≤ (97356592287/1000000000000 : ℝ)^3963 := by
    have hnat : (78534091 : ℕ)^4987*1000000000000^3963 ≤ 97356592287^3963*500000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78534091 500000000 97356592287 1000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5442443469/10000000000 : ℝ)^4987 ≤ (363342099291/781250000000 : ℝ)^3963 := by
    have hnat : (5442443469 : ℕ)^4987*781250000000^3963 ≤ 363342099291^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442443469 10000000000 363342099291 781250000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (648125511/1250000000 : ℝ)^4987 ≤ (21878276025841/50000000000000 : ℝ)^3963 := by
    have hnat : (648125511 : ℕ)^4987*50000000000000^3963 ≤ 21878276025841^3963*1250000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      648125511 1250000000 21878276025841 50000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-78534091/500000000 : ℝ), (5442443469/10000000000 : ℝ), (648125511/1250000000 : ℝ)] ![(97356592287/1000000000000 : ℝ), (363342099291/781250000000 : ℝ), (21878276025841/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-78534091/500000000 : ℝ)|^4987 ≤ (97356592287/1000000000000 : ℝ)^3963
        have hw : |(-78534091/500000000 : ℝ)|=(78534091/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5442443469/10000000000 : ℝ)|^4987 ≤ (363342099291/781250000000 : ℝ)^3963
        have hw : |(5442443469/10000000000 : ℝ)|=(5442443469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(648125511/1250000000 : ℝ)|^4987 ≤ (21878276025841/50000000000000 : ℝ)^3963
        have hw : |(648125511/1250000000 : ℝ)|=(648125511/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_s4_1 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345129347/10000000000 : ℝ)*x 0 + (-1703118641/10000000000 : ℝ)*x 1 + (5185004447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345129347/10000000000 : ℝ)^4987 ≤ (45463756177539/100000000000000 : ℝ)^3963 := by
    have hnat : (5345129347 : ℕ)^4987*100000000000000^3963 ≤ 45463756177539^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345129347 10000000000 45463756177539 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1703118641/10000000000 : ℝ)^4987 ≤ (10779687956161/100000000000000 : ℝ)^3963 := by
    have hnat : (1703118641 : ℕ)^4987*100000000000000^3963 ≤ 10779687956161^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1703118641 10000000000 10779687956161 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5185004447/10000000000 : ℝ)^4987 ≤ (683696185377/1562500000000 : ℝ)^3963 := by
    have hnat : (5185004447 : ℕ)^4987*1562500000000^3963 ≤ 683696185377^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185004447 10000000000 683696185377 1562500000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345129347/10000000000 : ℝ), (-1703118641/10000000000 : ℝ), (5185004447/10000000000 : ℝ)] ![(45463756177539/100000000000000 : ℝ), (10779687956161/100000000000000 : ℝ), (683696185377/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345129347/10000000000 : ℝ)|^4987 ≤ (45463756177539/100000000000000 : ℝ)^3963
        have hw : |(5345129347/10000000000 : ℝ)|=(5345129347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1703118641/10000000000 : ℝ)|^4987 ≤ (10779687956161/100000000000000 : ℝ)^3963
        have hw : |(-1703118641/10000000000 : ℝ)|=(1703118641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5185004447/10000000000 : ℝ)|^4987 ≤ (683696185377/1562500000000 : ℝ)^3963
        have hw : |(5185004447/10000000000 : ℝ)|=(5185004447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_s4_2 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336282401/2500000000 : ℝ)*x 0 + (1296251063/2500000000 : ℝ)*x 1 + (-340623711/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336282401/2500000000 : ℝ)^4987 ≤ (45463758928317/100000000000000 : ℝ)^3963 := by
    have hnat : (1336282401 : ℕ)^4987*100000000000000^3963 ≤ 45463758928317^3963*2500000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336282401 2500000000 45463758928317 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1296251063/2500000000 : ℝ)^4987 ≤ (43756553793301/100000000000000 : ℝ)^3963 := by
    have hnat : (1296251063 : ℕ)^4987*100000000000000^3963 ≤ 43756553793301^3963*2500000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296251063 2500000000 43756553793301 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (340623711/2000000000 : ℝ)^4987 ≤ (2155937454237/20000000000000 : ℝ)^3963 := by
    have hnat : (340623711 : ℕ)^4987*20000000000000^3963 ≤ 2155937454237^3963*2000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340623711 2000000000 2155937454237 20000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336282401/2500000000 : ℝ), (1296251063/2500000000 : ℝ), (-340623711/2000000000 : ℝ)] ![(45463758928317/100000000000000 : ℝ), (43756553793301/100000000000000 : ℝ), (2155937454237/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336282401/2500000000 : ℝ)|^4987 ≤ (45463758928317/100000000000000 : ℝ)^3963
        have hw : |(1336282401/2500000000 : ℝ)|=(1336282401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1296251063/2500000000 : ℝ)|^4987 ≤ (43756553793301/100000000000000 : ℝ)^3963
        have hw : |(1296251063/2500000000 : ℝ)|=(1296251063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-340623711/2000000000 : ℝ)|^4987 ≤ (2155937454237/20000000000000 : ℝ)^3963
        have hw : |(-340623711/2000000000 : ℝ)|=(340623711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_s4_3 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4167902967/10000000000 : ℝ)*x 0 + (3837555111/10000000000 : ℝ)*x 1 + (4517898563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4167902967/10000000000 : ℝ)^4987 ≤ (16621800721223/50000000000000 : ℝ)^3963 := by
    have hnat : (4167902967 : ℕ)^4987*50000000000000^3963 ≤ 16621800721223^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4167902967 10000000000 16621800721223 50000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3837555111/10000000000 : ℝ)^4987 ≤ (14981264071007/50000000000000 : ℝ)^3963 := by
    have hnat : (3837555111 : ℕ)^4987*50000000000000^3963 ≤ 14981264071007^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3837555111 10000000000 14981264071007 50000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4517898563/10000000000 : ℝ)^4987 ≤ (18396935202257/50000000000000 : ℝ)^3963 := by
    have hnat : (4517898563 : ℕ)^4987*50000000000000^3963 ≤ 18396935202257^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4517898563 10000000000 18396935202257 50000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4167902967/10000000000 : ℝ), (3837555111/10000000000 : ℝ), (4517898563/10000000000 : ℝ)] ![(16621800721223/50000000000000 : ℝ), (14981264071007/50000000000000 : ℝ), (18396935202257/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4167902967/10000000000 : ℝ)|^4987 ≤ (16621800721223/50000000000000 : ℝ)^3963
        have hw : |(4167902967/10000000000 : ℝ)|=(4167902967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3837555111/10000000000 : ℝ)|^4987 ≤ (14981264071007/50000000000000 : ℝ)^3963
        have hw : |(3837555111/10000000000 : ℝ)|=(3837555111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4517898563/10000000000 : ℝ)|^4987 ≤ (18396935202257/50000000000000 : ℝ)^3963
        have hw : |(4517898563/10000000000 : ℝ)|=(4517898563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_s4_4 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-392686007/2500000000 : ℝ)*x 0 + (5186964803/10000000000 : ℝ)*x 1 + (5440461841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (392686007/2500000000 : ℝ)^4987 ≤ (973614445117/10000000000000 : ℝ)^3963 := by
    have hnat : (392686007 : ℕ)^4987*10000000000000^3963 ≤ 973614445117^3963*2500000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      392686007 2500000000 973614445117 10000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5186964803/10000000000 : ℝ)^4987 ≤ (8755475026379/20000000000000 : ℝ)^3963 := by
    have hnat : (5186964803 : ℕ)^4987*20000000000000^3963 ≤ 8755475026379^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5186964803 10000000000 8755475026379 20000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5440461841/10000000000 : ℝ)^4987 ≤ (23243240205713/50000000000000 : ℝ)^3963 := by
    have hnat : (5440461841 : ℕ)^4987*50000000000000^3963 ≤ 23243240205713^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440461841 10000000000 23243240205713 50000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-392686007/2500000000 : ℝ), (5186964803/10000000000 : ℝ), (5440461841/10000000000 : ℝ)] ![(973614445117/10000000000000 : ℝ), (8755475026379/20000000000000 : ℝ), (23243240205713/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-392686007/2500000000 : ℝ)|^4987 ≤ (973614445117/10000000000000 : ℝ)^3963
        have hw : |(-392686007/2500000000 : ℝ)|=(392686007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5186964803/10000000000 : ℝ)|^4987 ≤ (8755475026379/20000000000000 : ℝ)^3963
        have hw : |(5186964803/10000000000 : ℝ)|=(5186964803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5440461841/10000000000 : ℝ)|^4987 ≤ (23243240205713/50000000000000 : ℝ)^3963
        have hw : |(5440461841/10000000000 : ℝ)|=(5440461841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_s4_5 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276228589/10000000000 : ℝ)*x 0 + (-28953219/200000000 : ℝ)*x 1 + (1360115439/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276228589/10000000000 : ℝ)^4987 ≤ (22363757415523/50000000000000 : ℝ)^3963 := by
    have hnat : (5276228589 : ℕ)^4987*50000000000000^3963 ≤ 22363757415523^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276228589 10000000000 22363757415523 50000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (28953219/200000000 : ℝ)^4987 ≤ (2196501413753/25000000000000 : ℝ)^3963 := by
    have hnat : (28953219 : ℕ)^4987*25000000000000^3963 ≤ 2196501413753^3963*200000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28953219 200000000 2196501413753 25000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1360115439/2500000000 : ℝ)^4987 ≤ (46486479497471/100000000000000 : ℝ)^3963 := by
    have hnat : (1360115439 : ℕ)^4987*100000000000000^3963 ≤ 46486479497471^3963*2500000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360115439 2500000000 46486479497471 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276228589/10000000000 : ℝ), (-28953219/200000000 : ℝ), (1360115439/2500000000 : ℝ)] ![(22363757415523/50000000000000 : ℝ), (2196501413753/25000000000000 : ℝ), (46486479497471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276228589/10000000000 : ℝ)|^4987 ≤ (22363757415523/50000000000000 : ℝ)^3963
        have hw : |(5276228589/10000000000 : ℝ)|=(5276228589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-28953219/200000000 : ℝ)|^4987 ≤ (2196501413753/25000000000000 : ℝ)^3963
        have hw : |(-28953219/200000000 : ℝ)|=(28953219/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1360115439/2500000000 : ℝ)|^4987 ≤ (46486479497471/100000000000000 : ℝ)^3963
        have hw : |(1360115439/2500000000 : ℝ)|=(1360115439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_s4_6 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638114183/5000000000 : ℝ)*x 0 + (1360115457/2500000000 : ℝ)*x 1 + (-1447661159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638114183/5000000000 : ℝ)^4987 ≤ (44727512452173/100000000000000 : ℝ)^3963 := by
    have hnat : (2638114183 : ℕ)^4987*100000000000000^3963 ≤ 44727512452173^3963*5000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638114183 5000000000 44727512452173 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1360115457/2500000000 : ℝ)^4987 ≤ (9297296054329/20000000000000 : ℝ)^3963 := by
    have hnat : (1360115457 : ℕ)^4987*20000000000000^3963 ≤ 9297296054329^3963*2500000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360115457 2500000000 9297296054329 20000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1447661159/10000000000 : ℝ)^4987 ≤ (1098250906401/12500000000000 : ℝ)^3963 := by
    have hnat : (1447661159 : ℕ)^4987*12500000000000^3963 ≤ 1098250906401^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1447661159 10000000000 1098250906401 12500000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638114183/5000000000 : ℝ), (1360115457/2500000000 : ℝ), (-1447661159/10000000000 : ℝ)] ![(44727512452173/100000000000000 : ℝ), (9297296054329/20000000000000 : ℝ), (1098250906401/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638114183/5000000000 : ℝ)|^4987 ≤ (44727512452173/100000000000000 : ℝ)^3963
        have hw : |(2638114183/5000000000 : ℝ)|=(2638114183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1360115457/2500000000 : ℝ)|^4987 ≤ (9297296054329/20000000000000 : ℝ)^3963
        have hw : |(1360115457/2500000000 : ℝ)|=(1360115457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1447661159/10000000000 : ℝ)|^4987 ≤ (1098250906401/12500000000000 : ℝ)^3963
        have hw : |(-1447661159/10000000000 : ℝ)|=(1447661159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_s4_7 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4168066911/10000000000 : ℝ)*x 0 + (4512716991/10000000000 : ℝ)*x 1 + (384279067/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4168066911/10000000000 : ℝ)^4987 ≤ (4155655870463/12500000000000 : ℝ)^3963 := by
    have hnat : (4168066911 : ℕ)^4987*12500000000000^3963 ≤ 4155655870463^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4168066911 10000000000 4155655870463 12500000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4512716991/10000000000 : ℝ)^4987 ≤ (36740775669503/100000000000000 : ℝ)^3963 := by
    have hnat : (4512716991 : ℕ)^4987*100000000000000^3963 ≤ 36740775669503^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4512716991 10000000000 36740775669503 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (384279067/1000000000 : ℝ)^4987 ≤ (15006988675367/50000000000000 : ℝ)^3963 := by
    have hnat : (384279067 : ℕ)^4987*50000000000000^3963 ≤ 15006988675367^3963*1000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      384279067 1000000000 15006988675367 50000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4168066911/10000000000 : ℝ), (4512716991/10000000000 : ℝ), (384279067/1000000000 : ℝ)] ![(4155655870463/12500000000000 : ℝ), (36740775669503/100000000000000 : ℝ), (15006988675367/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4168066911/10000000000 : ℝ)|^4987 ≤ (4155655870463/12500000000000 : ℝ)^3963
        have hw : |(4168066911/10000000000 : ℝ)|=(4168066911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4512716991/10000000000 : ℝ)|^4987 ≤ (36740775669503/100000000000000 : ℝ)^3963
        have hw : |(4512716991/10000000000 : ℝ)|=(4512716991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(384279067/1000000000 : ℝ)|^4987 ≤ (15006988675367/50000000000000 : ℝ)^3963
        have hw : |(384279067/1000000000 : ℝ)|=(384279067/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1667_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (182137009/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (336/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (2151/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8117/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (336/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (336/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (336/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (336/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (336/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (336/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (336/3125 : ℝ) ^ (4983/1024 : ℝ) ≤ (1936521945886057/100000000000000000000 : ℝ) := by
    have hpowers : (336/3125 : ℝ)^4983 ≤ (1936521945886057/100000000000000000000 : ℝ)^1024 := by
      have hnat : (336 : ℕ)^4983*100000000000000000000^1024 ≤ 1936521945886057^1024*3125^4983 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        336 3125 1936521945886057 100000000000000000000 4983 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (336/3125 : ℝ)) (X := (1936521945886057/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4983 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16237/100000 : ℝ) ^ (4983/1024 : ℝ) ≤ (2878621993358803/20000000000000000000 : ℝ) := by
    have hpowers : (16237/100000 : ℝ)^4983 ≤ (2878621993358803/20000000000000000000 : ℝ)^1024 := by
      have hnat : (16237 : ℕ)^4983*20000000000000000000^1024 ≤ 2878621993358803^1024*100000^4983 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16237 100000 2878621993358803 20000000000000000000 4983 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16237/100000 : ℝ)) (X := (2878621993358803/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4983 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001936521945886057/50000000000000000000 : ℝ) ≤ (2500019897330559/2500000000000000 : ℝ) ^ (4983/1024 : ℝ) := by
    have hpowers : (50001936521945886057/50000000000000000000 : ℝ)^1024 ≤ (2500019897330559/2500000000000000 : ℝ)^4983 := by
      have hnat : (50001936521945886057 : ℕ)^1024*2500000000000000^4983 ≤ 2500019897330559^4983*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001936521945886057 50000000000000000000 2500019897330559 2500000000000000 1024 4983 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500019897330559/2500000000000000 : ℝ)) (X := (50001936521945886057/50000000000000000000 : ℝ)) (by norm_num) 4983 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12502041203989085009/12500000000000000000 : ℝ) ≤ (10000335550039439/10000000000000000 : ℝ) ^ (4983/1024 : ℝ) := by
    have hpowers : (12502041203989085009/12500000000000000000 : ℝ)^1024 ≤ (10000335550039439/10000000000000000 : ℝ)^4983 := by
      have hnat : (12502041203989085009 : ℕ)^1024*10000000000000000^4983 ≤ 10000335550039439^4983*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502041203989085009 12500000000000000000 10000335550039439 10000000000000000 1024 4983 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000335550039439/10000000000000000 : ℝ)) (X := (12502041203989085009/12500000000000000000 : ℝ)) (by norm_num) 4983 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10002878621993358803/10000000000000000000 : ℝ) ≤ (5000295755378321/5000000000000000 : ℝ) ^ (4983/1024 : ℝ) := by
    have hpowers : (10002878621993358803/10000000000000000000 : ℝ)^1024 ≤ (5000295755378321/5000000000000000 : ℝ)^4983 := by
      have hnat : (10002878621993358803 : ℕ)^1024*5000000000000000^4983 ≤ 5000295755378321^4983*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002878621993358803 10000000000000000000 5000295755378321 5000000000000000 1024 4983 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000295755378321/5000000000000000 : ℝ)) (X := (10002878621993358803/10000000000000000000 : ℝ)) (by norm_num) 4983 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1936521945886057/100000000000000000000 : ℝ) ≤ ((13711233092042432787/13712500000000000000 : ℝ)+2*(255960717203/548500000000000 : ℝ)*(336/3125 : ℝ))^(4983/1024 : ℝ) := by
    rw [show (13711233092042432787/13712500000000000000 : ℝ)+2*(255960717203/548500000000000 : ℝ)*(336/3125 : ℝ)=(2500019897330559/2500000000000000 : ℝ) by norm_num, show 1+2*(1936521945886057/100000000000000000000 : ℝ)=(50001936521945886057/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2878621993358803/20000000000000000000 : ℝ)+(1936521945886057/100000000000000000000 : ℝ) ≤ ((13711233092042432787/13712500000000000000 : ℝ)+(255960717203/548500000000000 : ℝ)*((16237/100000 : ℝ)+(336/3125 : ℝ)))^(4983/1024 : ℝ) := by
    rw [show (13711233092042432787/13712500000000000000 : ℝ)+(255960717203/548500000000000 : ℝ)*((16237/100000 : ℝ)+(336/3125 : ℝ))=(10000335550039439/10000000000000000 : ℝ) by norm_num, show 1+(2878621993358803/20000000000000000000 : ℝ)+(1936521945886057/100000000000000000000 : ℝ)=(12502041203989085009/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2878621993358803/20000000000000000000 : ℝ) ≤ ((13711233092042432787/13712500000000000000 : ℝ)+2*(255960717203/548500000000000 : ℝ)*(16237/100000 : ℝ))^(4983/1024 : ℝ) := by
    rw [show (13711233092042432787/13712500000000000000 : ℝ)+2*(255960717203/548500000000000 : ℝ)*(16237/100000 : ℝ)=(5000295755378321/5000000000000000 : ℝ) by norm_num, show 1+2*(2878621993358803/20000000000000000000 : ℝ)=(10002878621993358803/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13711233092042432787/13712500000000000000 : ℝ)*(X 1 0+X 2 0)+(255960717203/548500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4983/1024 : ℝ)) (lo := (336/3125 : ℝ)) (hi := (16237/100000 : ℝ)) (c := (13711233092042432787/13712500000000000000 : ℝ)) (alpha := (255960717203/548500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13711233092042432787/13712500000000000000 : ℝ)*(X 0 1+X 2 1)+(255960717203/548500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4983/1024 : ℝ)) (lo := (336/3125 : ℝ)) (hi := (16237/100000 : ℝ)) (c := (13711233092042432787/13712500000000000000 : ℝ)) (alpha := (255960717203/548500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13711233092042432787/13712500000000000000 : ℝ)*(X 0 2+X 1 2)+(255960717203/548500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4983/1024 : ℝ)) (lo := (336/3125 : ℝ)) (hi := (16237/100000 : ℝ)) (c := (13711233092042432787/13712500000000000000 : ℝ)) (alpha := (255960717203/548500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-78534091/500000000 : ℝ)*X 0 0+(5442443469/10000000000 : ℝ)*X 0 1+(648125511/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345129347/10000000000 : ℝ)*X 1 0+(-1703118641/10000000000 : ℝ)*X 1 1+(5185004447/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336282401/2500000000 : ℝ)*X 2 0+(1296251063/2500000000 : ℝ)*X 2 1+(-340623711/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4167902967/10000000000 : ℝ)*X 0 0+(3837555111/10000000000 : ℝ)*X 0 1+(4517898563/10000000000 : ℝ)*X 0 2+(4167902967/10000000000 : ℝ)*X 1 0+(3837555111/10000000000 : ℝ)*X 1 1+(4517898563/10000000000 : ℝ)*X 1 2+(4167902967/10000000000 : ℝ)*X 2 0+(3837555111/10000000000 : ℝ)*X 2 1+(4517898563/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-392686007/2500000000 : ℝ)*X 0 0+(5186964803/10000000000 : ℝ)*X 0 1+(5440461841/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5276228589/10000000000 : ℝ)*X 1 0+(-28953219/200000000 : ℝ)*X 1 1+(1360115439/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2638114183/5000000000 : ℝ)*X 2 0+(1360115457/2500000000 : ℝ)*X 2 1+(-1447661159/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4168066911/10000000000 : ℝ)*X 0 0+(4512716991/10000000000 : ℝ)*X 0 1+(384279067/1000000000 : ℝ)*X 0 2+(4168066911/10000000000 : ℝ)*X 1 0+(4512716991/10000000000 : ℝ)*X 1 1+(384279067/1000000000 : ℝ)*X 1 2+(4168066911/10000000000 : ℝ)*X 2 0+(4512716991/10000000000 : ℝ)*X 2 1+(384279067/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (217608192179832640123239/27425000000000000000000000000 : ℝ) := by norm_num
    linear_combination (472807731/100000000000000 : ℝ)*(base19) + (74383319/12500000000000 : ℝ)*(base23) + (17240479/50000000000000 : ℝ)*(lower2) + (24951491/50000000000000 : ℝ)*(upper3) + (19783681/20000000000000 : ℝ)*(upper5) + (669285255601567/25000000000000 : ℝ)*(major0) + (669285255601567/25000000000000 : ℝ)*(major1) + (669285255601567/25000000000000 : ℝ)*(major2) + (971104813951557/25000000000000 : ℝ)*(sp0) + (194221560005671/5000000000000 : ℝ)*(sp1) + (3884431077854599/100000000000000 : ℝ)*(sp2) + (367461981011389/25000000000000 : ℝ)*(sp3) + (12417114923/100000000000000 : ℝ)*(sp4) + (109167849/5000000000000 : ℝ)*(sp7) + (1469850107402537/100000000000000 : ℝ)*(f.failure) + (60694244889393/1562500000000 : ℝ)*(f.sum) + (6599907703297/857031250000000000000000000 : ℝ)*base65 + (257723701694660271/342812500000000000000000000000000 : ℝ)*base68 + (612895971434714729/342812500000000000000000000000000 : ℝ)*base69 + (1263030331061847771/342812500000000000000000000000000 : ℝ)*base72 + (17168811020513/3428125000000000000000000000 : ℝ)*base73 + (2054297258934402229/342812500000000000000000000000000 : ℝ)*base75 + (467517317240652229/342812500000000000000000000000000 : ℝ)*base77 + (1127636078931847771/342812500000000000000000000000000 : ℝ)*base80 + (189444097209629/27425000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (48191833/10000000000000000000000 : ℝ)*base89 + (48191833/10000000000000000000000 : ℝ)*base91 + (48191833/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1935287619099337585336552623/171406250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (68439251/4000000000000 : ℝ)*(base19) + (189808763/12500000000000 : ℝ)*(base23) + (403221481/100000000000000 : ℝ)*(lower1) + (16018107/100000000000000 : ℝ)*(upper2) + (233548083/100000000000000 : ℝ)*(upper3) + (58019227/20000000000000 : ℝ)*(upper5) + (679687321548393/25000000000000 : ℝ)*(major0) + (679687321548393/25000000000000 : ℝ)*(major1) + (679687321548393/25000000000000 : ℝ)*(major2) + (2149636313/50000000000000 : ℝ)*(sp1) + (493100450310489/12500000000000 : ℝ)*(sp4) + (3944797592230011/100000000000000 : ℝ)*(sp5) + (246550130250863/6250000000000 : ℝ)*(sp6) + (298538918709659/20000000000000 : ℝ)*(sp7) + (298538918709659/20000000000000 : ℝ)*(f.failure) + (493100450310489/12500000000000 : ℝ)*(f.sum) + (59947203137709/27425000000000000000000000000 : ℝ)*base66 + (1374506303322023791/342812500000000000000000000000000 : ℝ)*base67 + (1996362139558288709/342812500000000000000000000000000 : ℝ)*base70 + (1686747893570461291/342812500000000000000000000000000 : ℝ)*base71 + (58767410268791/27425000000000000000000000000 : ℝ)*base73 + (701876478671413709/342812500000000000000000000000000 : ℝ)*base76 + (581621173810476209/342812500000000000000000000000000 : ℝ)*base78 + (864460990970476209/342812500000000000000000000000000 : ℝ)*base80 + (191768013918733/13712500000000000000000000000 : ℝ)*base81 + (10330069/2000000000000000000000 : ℝ)*base90 + (10330069/2000000000000000000000 : ℝ)*base92 + (10330069/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1667_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (182137009/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (336/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2151/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8117/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1667_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1667_box_0 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-659321517/5000000000 : ℝ)*x 0 + (168872383/312500000 : ℝ)*x 1 + (5403916291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (659321517/5000000000 : ℝ)^4987 ≤ (7812262510791/100000000000000 : ℝ)^3963 := by
    have hnat : (659321517 : ℕ)^4987*100000000000000^3963 ≤ 7812262510791^3963*5000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659321517 5000000000 7812262510791 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168872383/312500000 : ℝ)^4987 ≤ (23046934274653/50000000000000 : ℝ)^3963 := by
    have hnat : (168872383 : ℕ)^4987*50000000000000^3963 ≤ 23046934274653^3963*312500000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168872383 312500000 23046934274653 50000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5403916291/10000000000 : ℝ)^4987 ≤ (23046934462493/50000000000000 : ℝ)^3963 := by
    have hnat : (5403916291 : ℕ)^4987*50000000000000^3963 ≤ 23046934462493^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403916291 10000000000 23046934462493 50000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-659321517/5000000000 : ℝ), (168872383/312500000 : ℝ), (5403916291/10000000000 : ℝ)] ![(7812262510791/100000000000000 : ℝ), (23046934274653/50000000000000 : ℝ), (23046934462493/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-659321517/5000000000 : ℝ)|^4987 ≤ (7812262510791/100000000000000 : ℝ)^3963
        have hw : |(-659321517/5000000000 : ℝ)|=(659321517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168872383/312500000 : ℝ)|^4987 ≤ (23046934274653/50000000000000 : ℝ)^3963
        have hw : |(168872383/312500000 : ℝ)|=(168872383/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5403916291/10000000000 : ℝ)|^4987 ≤ (23046934462493/50000000000000 : ℝ)^3963
        have hw : |(5403916291/10000000000 : ℝ)|=(5403916291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_box_1 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625380409/5000000000 : ℝ)*x 0 + (-1533963277/10000000000 : ℝ)*x 1 + (1350979081/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625380409/5000000000 : ℝ)^4987 ≤ (22228002312721/50000000000000 : ℝ)^3963 := by
    have hnat : (2625380409 : ℕ)^4987*50000000000000^3963 ≤ 22228002312721^3963*5000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625380409 5000000000 22228002312721 50000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1533963277/10000000000 : ℝ)^4987 ≤ (2362531519419/25000000000000 : ℝ)^3963 := by
    have hnat : (1533963277 : ℕ)^4987*25000000000000^3963 ≤ 2362531519419^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1533963277 10000000000 2362531519419 25000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1350979081/2500000000 : ℝ)^4987 ≤ (23046934639599/50000000000000 : ℝ)^3963 := by
    have hnat : (1350979081 : ℕ)^4987*50000000000000^3963 ≤ 23046934639599^3963*2500000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350979081 2500000000 23046934639599 50000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625380409/5000000000 : ℝ), (-1533963277/10000000000 : ℝ), (1350979081/2500000000 : ℝ)] ![(22228002312721/50000000000000 : ℝ), (2362531519419/25000000000000 : ℝ), (23046934639599/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625380409/5000000000 : ℝ)|^4987 ≤ (22228002312721/50000000000000 : ℝ)^3963
        have hw : |(2625380409/5000000000 : ℝ)|=(2625380409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1533963277/10000000000 : ℝ)|^4987 ≤ (2362531519419/25000000000000 : ℝ)^3963
        have hw : |(-1533963277/10000000000 : ℝ)|=(1533963277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1350979081/2500000000 : ℝ)|^4987 ≤ (23046934639599/50000000000000 : ℝ)^3963
        have hw : |(1350979081/2500000000 : ℝ)|=(1350979081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_box_2 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (131269023/250000000 : ℝ)*x 0 + (5403916273/10000000000 : ℝ)*x 1 + (-1533963209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131269023/250000000 : ℝ)^4987 ≤ (44456005712177/100000000000000 : ℝ)^3963 := by
    have hnat : (131269023 : ℕ)^4987*100000000000000^3963 ≤ 44456005712177^3963*250000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131269023 250000000 44456005712177 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5403916273/10000000000 : ℝ)^4987 ≤ (46093868731779/100000000000000 : ℝ)^3963 := by
    have hnat : (5403916273 : ℕ)^4987*100000000000000^3963 ≤ 46093868731779^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403916273 10000000000 46093868731779 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1533963209/10000000000 : ℝ)^4987 ≤ (945012555051/10000000000000 : ℝ)^3963 := by
    have hnat : (1533963209 : ℕ)^4987*10000000000000^3963 ≤ 945012555051^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1533963209 10000000000 945012555051 10000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(131269023/250000000 : ℝ), (5403916273/10000000000 : ℝ), (-1533963209/10000000000 : ℝ)] ![(44456005712177/100000000000000 : ℝ), (46093868731779/100000000000000 : ℝ), (945012555051/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(131269023/250000000 : ℝ)|^4987 ≤ (44456005712177/100000000000000 : ℝ)^3963
        have hw : |(131269023/250000000 : ℝ)|=(131269023/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5403916273/10000000000 : ℝ)|^4987 ≤ (46093868731779/100000000000000 : ℝ)^3963
        have hw : |(5403916273/10000000000 : ℝ)|=(5403916273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1533963209/10000000000 : ℝ)|^4987 ≤ (945012555051/10000000000000 : ℝ)^3963
        have hw : |(-1533963209/10000000000 : ℝ)|=(1533963209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_box_3 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2221818559/5000000000 : ℝ)*x 0 + (80835791/200000000 : ℝ)*x 1 + (252611857/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2221818559/5000000000 : ℝ)^4987 ≤ (36034435316591/100000000000000 : ℝ)^3963 := by
    have hnat : (2221818559 : ℕ)^4987*100000000000000^3963 ≤ 36034435316591^3963*5000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2221818559 5000000000 36034435316591 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (80835791/200000000 : ℝ)^4987 ≤ (31982781531801/100000000000000 : ℝ)^3963 := by
    have hnat : (80835791 : ℕ)^4987*100000000000000^3963 ≤ 31982781531801^3963*200000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80835791 200000000 31982781531801 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (252611857/625000000 : ℝ)^4987 ≤ (1998923946559/6250000000000 : ℝ)^3963 := by
    have hnat : (252611857 : ℕ)^4987*6250000000000^3963 ≤ 1998923946559^3963*625000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252611857 625000000 1998923946559 6250000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2221818559/5000000000 : ℝ), (80835791/200000000 : ℝ), (252611857/625000000 : ℝ)] ![(36034435316591/100000000000000 : ℝ), (31982781531801/100000000000000 : ℝ), (1998923946559/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2221818559/5000000000 : ℝ)|^4987 ≤ (36034435316591/100000000000000 : ℝ)^3963
        have hw : |(2221818559/5000000000 : ℝ)|=(2221818559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(80835791/200000000 : ℝ)|^4987 ≤ (31982781531801/100000000000000 : ℝ)^3963
        have hw : |(80835791/200000000 : ℝ)|=(80835791/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(252611857/625000000 : ℝ)|^4987 ≤ (1998923946559/6250000000000 : ℝ)^3963
        have hw : |(252611857/625000000 : ℝ)|=(252611857/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_box_4 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1833257879/10000000000 : ℝ)*x 0 + (5216084083/10000000000 : ℝ)*x 1 + (5093832/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1833257879/10000000000 : ℝ)^4987 ≤ (11826270708369/100000000000000 : ℝ)^3963 := by
    have hnat : (1833257879 : ℕ)^4987*100000000000000^3963 ≤ 11826270708369^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1833257879 10000000000 11826270708369 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216084083/10000000000 : ℝ)^4987 ≤ (22043432624699/50000000000000 : ℝ)^3963 := by
    have hnat : (5216084083 : ℕ)^4987*50000000000000^3963 ≤ 22043432624699^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216084083 10000000000 22043432624699 50000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5093832/9765625 : ℝ)^4987 ≤ (44086864026253/100000000000000 : ℝ)^3963 := by
    have hnat : (5093832 : ℕ)^4987*100000000000000^3963 ≤ 44086864026253^3963*9765625^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5093832 9765625 44086864026253 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1833257879/10000000000 : ℝ), (5216084083/10000000000 : ℝ), (5093832/9765625 : ℝ)] ![(11826270708369/100000000000000 : ℝ), (22043432624699/50000000000000 : ℝ), (44086864026253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1833257879/10000000000 : ℝ)|^4987 ≤ (11826270708369/100000000000000 : ℝ)^3963
        have hw : |(-1833257879/10000000000 : ℝ)|=(1833257879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216084083/10000000000 : ℝ)|^4987 ≤ (22043432624699/50000000000000 : ℝ)^3963
        have hw : |(5216084083/10000000000 : ℝ)|=(5216084083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5093832/9765625 : ℝ)|^4987 ≤ (44086864026253/100000000000000 : ℝ)^3963
        have hw : |(5093832/9765625 : ℝ)|=(5093832/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_box_5 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5379393981/10000000000 : ℝ)*x 0 + (-1614966211/10000000000 : ℝ)*x 1 + (1304021053/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5379393981/10000000000 : ℝ)^4987 ≤ (45830808057307/100000000000000 : ℝ)^3963 := by
    have hnat : (5379393981 : ℕ)^4987*100000000000000^3963 ≤ 45830808057307^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5379393981 10000000000 45830808057307 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1614966211/10000000000 : ℝ)^4987 ≤ (5041162651323/50000000000000 : ℝ)^3963 := by
    have hnat : (1614966211 : ℕ)^4987*50000000000000^3963 ≤ 5041162651323^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1614966211 10000000000 5041162651323 50000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304021053/2500000000 : ℝ)^4987 ≤ (44086866621447/100000000000000 : ℝ)^3963 := by
    have hnat : (1304021053 : ℕ)^4987*100000000000000^3963 ≤ 44086866621447^3963*2500000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304021053 2500000000 44086866621447 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5379393981/10000000000 : ℝ), (-1614966211/10000000000 : ℝ), (1304021053/2500000000 : ℝ)] ![(45830808057307/100000000000000 : ℝ), (5041162651323/50000000000000 : ℝ), (44086866621447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5379393981/10000000000 : ℝ)|^4987 ≤ (45830808057307/100000000000000 : ℝ)^3963
        have hw : |(5379393981/10000000000 : ℝ)|=(5379393981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1614966211/10000000000 : ℝ)|^4987 ≤ (5041162651323/50000000000000 : ℝ)^3963
        have hw : |(-1614966211/10000000000 : ℝ)|=(1614966211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304021053/2500000000 : ℝ)|^4987 ≤ (44086866621447/100000000000000 : ℝ)^3963
        have hw : |(1304021053/2500000000 : ℝ)|=(1304021053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_box_6 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5379394313/10000000000 : ℝ)*x 0 + (1043216753/2000000000 : ℝ)*x 1 + (-1614966363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5379394313/10000000000 : ℝ)^4987 ≤ (45830811616713/100000000000000 : ℝ)^3963 := by
    have hnat : (5379394313 : ℕ)^4987*100000000000000^3963 ≤ 45830811616713^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5379394313 10000000000 45830811616713 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043216753/2000000000 : ℝ)^4987 ≤ (44086861867137/100000000000000 : ℝ)^3963 := by
    have hnat : (1043216753 : ℕ)^4987*100000000000000^3963 ≤ 44086861867137^3963*2000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043216753 2000000000 44086861867137 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1614966363/10000000000 : ℝ)^4987 ≤ (10082326496789/100000000000000 : ℝ)^3963 := by
    have hnat : (1614966363 : ℕ)^4987*100000000000000^3963 ≤ 10082326496789^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1614966363 10000000000 10082326496789 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5379394313/10000000000 : ℝ), (1043216753/2000000000 : ℝ), (-1614966363/10000000000 : ℝ)] ![(45830811616713/100000000000000 : ℝ), (44086861867137/100000000000000 : ℝ), (10082326496789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5379394313/10000000000 : ℝ)|^4987 ≤ (45830811616713/100000000000000 : ℝ)^3963
        have hw : |(5379394313/10000000000 : ℝ)|=(5379394313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043216753/2000000000 : ℝ)|^4987 ≤ (44086861867137/100000000000000 : ℝ)^3963
        have hw : |(1043216753/2000000000 : ℝ)|=(1043216753/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1614966363/10000000000 : ℝ)|^4987 ≤ (10082326496789/100000000000000 : ℝ)^3963
        have hw : |(-1614966363/10000000000 : ℝ)|=(1614966363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_box_7 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3885398371/10000000000 : ℝ)*x 0 + (34564727/80000000 : ℝ)*x 1 + (4320590819/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3885398371/10000000000 : ℝ)^4987 ≤ (3043335009041/10000000000000 : ℝ)^3963 := by
    have hnat : (3885398371 : ℕ)^4987*10000000000000^3963 ≤ 3043335009041^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3885398371 10000000000 3043335009041 10000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34564727/80000000 : ℝ)^4987 ≤ (6956665046537/20000000000000 : ℝ)^3963 := by
    have hnat : (34564727 : ℕ)^4987*20000000000000^3963 ≤ 6956665046537^3963*80000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34564727 80000000 6956665046537 20000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4320590819/10000000000 : ℝ)^4987 ≤ (34783324665361/100000000000000 : ℝ)^3963 := by
    have hnat : (4320590819 : ℕ)^4987*100000000000000^3963 ≤ 34783324665361^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320590819 10000000000 34783324665361 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3885398371/10000000000 : ℝ), (34564727/80000000 : ℝ), (4320590819/10000000000 : ℝ)] ![(3043335009041/10000000000000 : ℝ), (6956665046537/20000000000000 : ℝ), (34783324665361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3885398371/10000000000 : ℝ)|^4987 ≤ (3043335009041/10000000000000 : ℝ)^3963
        have hw : |(3885398371/10000000000 : ℝ)|=(3885398371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(34564727/80000000 : ℝ)|^4987 ≤ (6956665046537/20000000000000 : ℝ)^3963
        have hw : |(34564727/80000000 : ℝ)|=(34564727/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4320590819/10000000000 : ℝ)|^4987 ≤ (34783324665361/100000000000000 : ℝ)^3963
        have hw : |(4320590819/10000000000 : ℝ)|=(4320590819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_box_8 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-430840209/2500000000 : ℝ)*x 0 + (79384561/156250000 : ℝ)*x 1 + (5433161291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (430840209/2500000000 : ℝ)^4987 ≤ (10941160468297/100000000000000 : ℝ)^3963 := by
    have hnat : (430840209 : ℕ)^4987*100000000000000^3963 ≤ 10941160468297^3963*2500000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430840209 2500000000 10941160468297 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (79384561/156250000 : ℝ)^4987 ≤ (21325422031957/50000000000000 : ℝ)^3963 := by
    have hnat : (79384561 : ℕ)^4987*50000000000000^3963 ≤ 21325422031957^3963*156250000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79384561 156250000 21325422031957 50000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5433161291/10000000000 : ℝ)^4987 ≤ (9281599089991/20000000000000 : ℝ)^3963 := by
    have hnat : (5433161291 : ℕ)^4987*20000000000000^3963 ≤ 9281599089991^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433161291 10000000000 9281599089991 20000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-430840209/2500000000 : ℝ), (79384561/156250000 : ℝ), (5433161291/10000000000 : ℝ)] ![(10941160468297/100000000000000 : ℝ), (21325422031957/50000000000000 : ℝ), (9281599089991/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-430840209/2500000000 : ℝ)|^4987 ≤ (10941160468297/100000000000000 : ℝ)^3963
        have hw : |(-430840209/2500000000 : ℝ)|=(430840209/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(79384561/156250000 : ℝ)|^4987 ≤ (21325422031957/50000000000000 : ℝ)^3963
        have hw : |(79384561/156250000 : ℝ)|=(79384561/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5433161291/10000000000 : ℝ)|^4987 ≤ (9281599089991/20000000000000 : ℝ)^3963
        have hw : |(5433161291/10000000000 : ℝ)|=(5433161291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_box_9 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (104614723/200000000 : ℝ)*x 0 + (-1520935673/10000000000 : ℝ)*x 1 + (543316141/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (104614723/200000000 : ℝ)^4987 ≤ (44242761726223/100000000000000 : ℝ)^3963 := by
    have hnat : (104614723 : ℕ)^4987*100000000000000^3963 ≤ 44242761726223^3963*200000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104614723 200000000 44242761726223 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1520935673/10000000000 : ℝ)^4987 ≤ (9349241518829/100000000000000 : ℝ)^3963 := by
    have hnat : (1520935673 : ℕ)^4987*100000000000000^3963 ≤ 9349241518829^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1520935673 10000000000 9349241518829 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (543316141/1000000000 : ℝ)^4987 ≤ (46407996729049/100000000000000 : ℝ)^3963 := by
    have hnat : (543316141 : ℕ)^4987*100000000000000^3963 ≤ 46407996729049^3963*1000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543316141 1000000000 46407996729049 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(104614723/200000000 : ℝ), (-1520935673/10000000000 : ℝ), (543316141/1000000000 : ℝ)] ![(44242761726223/100000000000000 : ℝ), (9349241518829/100000000000000 : ℝ), (46407996729049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(104614723/200000000 : ℝ)|^4987 ≤ (44242761726223/100000000000000 : ℝ)^3963
        have hw : |(104614723/200000000 : ℝ)|=(104614723/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1520935673/10000000000 : ℝ)|^4987 ≤ (9349241518829/100000000000000 : ℝ)^3963
        have hw : |(-1520935673/10000000000 : ℝ)|=(1520935673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(543316141/1000000000 : ℝ)|^4987 ≤ (46407996729049/100000000000000 : ℝ)^3963
        have hw : |(543316141/1000000000 : ℝ)|=(543316141/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_box_10 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1307684041/2500000000 : ℝ)*x 0 + (2716580741/5000000000 : ℝ)*x 1 + (-304187111/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1307684041/2500000000 : ℝ)^4987 ≤ (11060690468809/25000000000000 : ℝ)^3963 := by
    have hnat : (1307684041 : ℕ)^4987*25000000000000^3963 ≤ 11060690468809^3963*2500000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307684041 2500000000 11060690468809 25000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2716580741/5000000000 : ℝ)^4987 ≤ (9281599500591/20000000000000 : ℝ)^3963 := by
    have hnat : (2716580741 : ℕ)^4987*20000000000000^3963 ≤ 9281599500591^3963*5000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716580741 5000000000 9281599500591 20000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (304187111/2000000000 : ℝ)^4987 ≤ (1869848121211/20000000000000 : ℝ)^3963 := by
    have hnat : (304187111 : ℕ)^4987*20000000000000^3963 ≤ 1869848121211^3963*2000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      304187111 2000000000 1869848121211 20000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1307684041/2500000000 : ℝ), (2716580741/5000000000 : ℝ), (-304187111/2000000000 : ℝ)] ![(11060690468809/25000000000000 : ℝ), (9281599500591/20000000000000 : ℝ), (1869848121211/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1307684041/2500000000 : ℝ)|^4987 ≤ (11060690468809/25000000000000 : ℝ)^3963
        have hw : |(1307684041/2500000000 : ℝ)|=(1307684041/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2716580741/5000000000 : ℝ)|^4987 ≤ (9281599500591/20000000000000 : ℝ)^3963
        have hw : |(2716580741/5000000000 : ℝ)|=(2716580741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-304187111/2000000000 : ℝ)|^4987 ≤ (1869848121211/20000000000000 : ℝ)^3963
        have hw : |(-304187111/2000000000 : ℝ)|=(304187111/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_box_11 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2264091639/5000000000 : ℝ)*x 0 + (799660423/2000000000 : ℝ)*x 1 + (799660307/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2264091639/5000000000 : ℝ)^4987 ≤ (36899302828943/100000000000000 : ℝ)^3963 := by
    have hnat : (2264091639 : ℕ)^4987*100000000000000^3963 ≤ 36899302828943^3963*5000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2264091639 5000000000 36899302828943 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (799660423/2000000000 : ℝ)^4987 ≤ (31550351458757/100000000000000 : ℝ)^3963 := by
    have hnat : (799660423 : ℕ)^4987*100000000000000^3963 ≤ 31550351458757^3963*2000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      799660423 2000000000 31550351458757 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (799660307/2000000000 : ℝ)^4987 ≤ (7887586424857/25000000000000 : ℝ)^3963 := by
    have hnat : (799660307 : ℕ)^4987*25000000000000^3963 ≤ 7887586424857^3963*2000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      799660307 2000000000 7887586424857 25000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2264091639/5000000000 : ℝ), (799660423/2000000000 : ℝ), (799660307/2000000000 : ℝ)] ![(36899302828943/100000000000000 : ℝ), (31550351458757/100000000000000 : ℝ), (7887586424857/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2264091639/5000000000 : ℝ)|^4987 ≤ (36899302828943/100000000000000 : ℝ)^3963
        have hw : |(2264091639/5000000000 : ℝ)|=(2264091639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(799660423/2000000000 : ℝ)|^4987 ≤ (31550351458757/100000000000000 : ℝ)^3963
        have hw : |(799660423/2000000000 : ℝ)|=(799660423/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(799660307/2000000000 : ℝ)|^4987 ≤ (7887586424857/25000000000000 : ℝ)^3963
        have hw : |(799660307/2000000000 : ℝ)|=(799660307/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_box_12 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1426578141/10000000000 : ℝ)*x 0 + (27671673/50000000 : ℝ)*x 1 + (1299076921/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1426578141/10000000000 : ℝ)^4987 ≤ (862529394509/10000000000000 : ℝ)^3963 := by
    have hnat : (1426578141 : ℕ)^4987*10000000000000^3963 ≤ 862529394509^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1426578141 10000000000 862529394509 10000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27671673/50000000 : ℝ)^4987 ≤ (47498080222163/100000000000000 : ℝ)^3963 := by
    have hnat : (27671673 : ℕ)^4987*100000000000000^3963 ≤ 47498080222163^3963*50000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27671673 50000000 47498080222163 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1299076921/2500000000 : ℝ)^4987 ≤ (10969156455643/25000000000000 : ℝ)^3963 := by
    have hnat : (1299076921 : ℕ)^4987*25000000000000^3963 ≤ 10969156455643^3963*2500000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299076921 2500000000 10969156455643 25000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1426578141/10000000000 : ℝ), (27671673/50000000 : ℝ), (1299076921/2500000000 : ℝ)] ![(862529394509/10000000000000 : ℝ), (47498080222163/100000000000000 : ℝ), (10969156455643/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1426578141/10000000000 : ℝ)|^4987 ≤ (862529394509/10000000000000 : ℝ)^3963
        have hw : |(-1426578141/10000000000 : ℝ)|=(1426578141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(27671673/50000000 : ℝ)|^4987 ≤ (47498080222163/100000000000000 : ℝ)^3963
        have hw : |(27671673/50000000 : ℝ)|=(27671673/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1299076921/2500000000 : ℝ)|^4987 ≤ (10969156455643/25000000000000 : ℝ)^3963
        have hw : |(1299076921/2500000000 : ℝ)|=(1299076921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_box_13 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (134823713/250000000 : ℝ)*x 0 + (-1623218081/10000000000 : ℝ)*x 1 + (5196307951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134823713/250000000 : ℝ)^4987 ≤ (9195234987919/20000000000000 : ℝ)^3963 := by
    have hnat : (134823713 : ℕ)^4987*20000000000000^3963 ≤ 9195234987919^3963*250000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134823713 250000000 9195234987919 20000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1623218081/10000000000 : ℝ)^4987 ≤ (10147196389989/100000000000000 : ℝ)^3963 := by
    have hnat : (1623218081 : ℕ)^4987*100000000000000^3963 ≤ 10147196389989^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1623218081 10000000000 10147196389989 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5196307951/10000000000 : ℝ)^4987 ≤ (43876628659609/100000000000000 : ℝ)^3963 := by
    have hnat : (5196307951 : ℕ)^4987*100000000000000^3963 ≤ 43876628659609^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196307951 10000000000 43876628659609 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134823713/250000000 : ℝ), (-1623218081/10000000000 : ℝ), (5196307951/10000000000 : ℝ)] ![(9195234987919/20000000000000 : ℝ), (10147196389989/100000000000000 : ℝ), (43876628659609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134823713/250000000 : ℝ)|^4987 ≤ (9195234987919/20000000000000 : ℝ)^3963
        have hw : |(134823713/250000000 : ℝ)|=(134823713/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1623218081/10000000000 : ℝ)|^4987 ≤ (10147196389989/100000000000000 : ℝ)^3963
        have hw : |(-1623218081/10000000000 : ℝ)|=(1623218081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5196307951/10000000000 : ℝ)|^4987 ≤ (43876628659609/100000000000000 : ℝ)^3963
        have hw : |(5196307951/10000000000 : ℝ)|=(5196307951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_box_14 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5392947651/10000000000 : ℝ)*x 0 + (1039261677/2000000000 : ℝ)*x 1 + (-1623218679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5392947651/10000000000 : ℝ)^4987 ≤ (45976165616897/100000000000000 : ℝ)^3963 := by
    have hnat : (5392947651 : ℕ)^4987*100000000000000^3963 ≤ 45976165616897^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392947651 10000000000 45976165616897 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1039261677/2000000000 : ℝ)^4987 ≤ (43876633271121/100000000000000 : ℝ)^3963 := by
    have hnat : (1039261677 : ℕ)^4987*100000000000000^3963 ≤ 43876633271121^3963*2000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039261677 2000000000 43876633271121 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1623218679/10000000000 : ℝ)^4987 ≤ (2536800273547/25000000000000 : ℝ)^3963 := by
    have hnat : (1623218679 : ℕ)^4987*25000000000000^3963 ≤ 2536800273547^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1623218679 10000000000 2536800273547 25000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5392947651/10000000000 : ℝ), (1039261677/2000000000 : ℝ), (-1623218679/10000000000 : ℝ)] ![(45976165616897/100000000000000 : ℝ), (43876633271121/100000000000000 : ℝ), (2536800273547/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5392947651/10000000000 : ℝ)|^4987 ≤ (45976165616897/100000000000000 : ℝ)^3963
        have hw : |(5392947651/10000000000 : ℝ)|=(5392947651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1039261677/2000000000 : ℝ)|^4987 ≤ (43876633271121/100000000000000 : ℝ)^3963
        have hw : |(1039261677/2000000000 : ℝ)|=(1039261677/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1623218679/10000000000 : ℝ)|^4987 ≤ (2536800273547/25000000000000 : ℝ)^3963
        have hw : |(-1623218679/10000000000 : ℝ)|=(1623218679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_box_15 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3824994347/10000000000 : ℝ)*x 0 + (2174945399/5000000000 : ℝ)*x 1 + (2174945331/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3824994347/10000000000 : ℝ)^4987 ≤ (14919584499551/50000000000000 : ℝ)^3963 := by
    have hnat : (3824994347 : ℕ)^4987*50000000000000^3963 ≤ 14919584499551^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3824994347 10000000000 14919584499551 50000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2174945399/5000000000 : ℝ)^4987 ≤ (35080416184641/100000000000000 : ℝ)^3963 := by
    have hnat : (2174945399 : ℕ)^4987*100000000000000^3963 ≤ 35080416184641^3963*5000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174945399 5000000000 35080416184641 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2174945331/5000000000 : ℝ)^4987 ≤ (7016082960889/20000000000000 : ℝ)^3963 := by
    have hnat : (2174945331 : ℕ)^4987*20000000000000^3963 ≤ 7016082960889^3963*5000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174945331 5000000000 7016082960889 20000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3824994347/10000000000 : ℝ), (2174945399/5000000000 : ℝ), (2174945331/5000000000 : ℝ)] ![(14919584499551/50000000000000 : ℝ), (35080416184641/100000000000000 : ℝ), (7016082960889/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3824994347/10000000000 : ℝ)|^4987 ≤ (14919584499551/50000000000000 : ℝ)^3963
        have hw : |(3824994347/10000000000 : ℝ)|=(3824994347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2174945399/5000000000 : ℝ)|^4987 ≤ (35080416184641/100000000000000 : ℝ)^3963
        have hw : |(2174945399/5000000000 : ℝ)|=(2174945399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2174945331/5000000000 : ℝ)|^4987 ≤ (7016082960889/20000000000000 : ℝ)^3963
        have hw : |(2174945331/5000000000 : ℝ)|=(2174945331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1667_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (182137009/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2151/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(65141/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58809/100000 : ℝ) ∧ (163/200 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (88387/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2151/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2151/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2151/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2151/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2151/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2151/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2151/20000 : ℝ) ^ (4983/1024 : ℝ) ≤ (969576347999403/50000000000000000000 : ℝ) := by
    have hpowers : (2151/20000 : ℝ)^4983 ≤ (969576347999403/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2151 : ℕ)^4983*50000000000000000000^1024 ≤ 969576347999403^1024*20000^4983 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2151 20000 969576347999403 50000000000000000000 4983 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2151/20000 : ℝ)) (X := (969576347999403/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4983 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8117/50000 : ℝ) ^ (4983/1024 : ℝ) ≤ (14380173790597487/100000000000000000000 : ℝ) := by
    have hpowers : (8117/50000 : ℝ)^4983 ≤ (14380173790597487/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8117 : ℕ)^4983*100000000000000000000^1024 ≤ 14380173790597487^1024*50000^4983 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8117 50000 14380173790597487 100000000000000000000 4983 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8117/50000 : ℝ)) (X := (14380173790597487/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4983 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000969576347999403/25000000000000000000 : ℝ) ≤ (200001593948841/200000000000000 : ℝ) ^ (4983/1024 : ℝ) := by
    have hpowers : (25000969576347999403/25000000000000000000 : ℝ)^1024 ≤ (200001593948841/200000000000000 : ℝ)^4983 := by
      have hnat : (25000969576347999403 : ℕ)^1024*200000000000000^4983 ≤ 200001593948841^4983*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000969576347999403 25000000000000000000 200001593948841 200000000000000 1024 4983 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200001593948841/200000000000000 : ℝ)) (X := (25000969576347999403/25000000000000000000 : ℝ)) (by norm_num) 4983 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100016319326486596293/100000000000000000000 : ℝ) ≤ (500016766914587/500000000000000 : ℝ) ^ (4983/1024 : ℝ) := by
    have hpowers : (100016319326486596293/100000000000000000000 : ℝ)^1024 ≤ (500016766914587/500000000000000 : ℝ)^4983 := by
      have hnat : (100016319326486596293 : ℕ)^1024*500000000000000^4983 ≤ 500016766914587^4983*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100016319326486596293 100000000000000000000 500016766914587 500000000000000 1024 4983 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500016766914587/500000000000000 : ℝ)) (X := (100016319326486596293/100000000000000000000 : ℝ)) (by norm_num) 4983 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50014380173790597487/50000000000000000000 : ℝ) ≤ (1000059097914143/1000000000000000 : ℝ) ^ (4983/1024 : ℝ) := by
    have hpowers : (50014380173790597487/50000000000000000000 : ℝ)^1024 ≤ (1000059097914143/1000000000000000 : ℝ)^4983 := by
      have hnat : (50014380173790597487 : ℕ)^1024*1000000000000000^4983 ≤ 1000059097914143^4983*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014380173790597487 50000000000000000000 1000059097914143 1000000000000000 1024 4983 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000059097914143/1000000000000000 : ℝ)) (X := (50014380173790597487/50000000000000000000 : ℝ)) (by norm_num) 4983 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(969576347999403/50000000000000000000 : ℝ) ≤ ((1095698756552163201/1095800000000000000 : ℝ)+2*(25564084969/54790000000000 : ℝ)*(2151/20000 : ℝ))^(4983/1024 : ℝ) := by
    rw [show (1095698756552163201/1095800000000000000 : ℝ)+2*(25564084969/54790000000000 : ℝ)*(2151/20000 : ℝ)=(200001593948841/200000000000000 : ℝ) by norm_num, show 1+2*(969576347999403/50000000000000000000 : ℝ)=(25000969576347999403/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14380173790597487/100000000000000000000 : ℝ)+(969576347999403/50000000000000000000 : ℝ) ≤ ((1095698756552163201/1095800000000000000 : ℝ)+(25564084969/54790000000000 : ℝ)*((8117/50000 : ℝ)+(2151/20000 : ℝ)))^(4983/1024 : ℝ) := by
    rw [show (1095698756552163201/1095800000000000000 : ℝ)+(25564084969/54790000000000 : ℝ)*((8117/50000 : ℝ)+(2151/20000 : ℝ))=(500016766914587/500000000000000 : ℝ) by norm_num, show 1+(14380173790597487/100000000000000000000 : ℝ)+(969576347999403/50000000000000000000 : ℝ)=(100016319326486596293/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14380173790597487/100000000000000000000 : ℝ) ≤ ((1095698756552163201/1095800000000000000 : ℝ)+2*(25564084969/54790000000000 : ℝ)*(8117/50000 : ℝ))^(4983/1024 : ℝ) := by
    rw [show (1095698756552163201/1095800000000000000 : ℝ)+2*(25564084969/54790000000000 : ℝ)*(8117/50000 : ℝ)=(1000059097914143/1000000000000000 : ℝ) by norm_num, show 1+2*(14380173790597487/100000000000000000000 : ℝ)=(50014380173790597487/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1095698756552163201/1095800000000000000 : ℝ)*(X 1 0+X 2 0)+(25564084969/54790000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4983/1024 : ℝ)) (lo := (2151/20000 : ℝ)) (hi := (8117/50000 : ℝ)) (c := (1095698756552163201/1095800000000000000 : ℝ)) (alpha := (25564084969/54790000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1095698756552163201/1095800000000000000 : ℝ)*(X 0 1+X 2 1)+(25564084969/54790000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4983/1024 : ℝ)) (lo := (2151/20000 : ℝ)) (hi := (8117/50000 : ℝ)) (c := (1095698756552163201/1095800000000000000 : ℝ)) (alpha := (25564084969/54790000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1095698756552163201/1095800000000000000 : ℝ)*(X 0 2+X 1 2)+(25564084969/54790000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4983/1024 : ℝ)) (lo := (2151/20000 : ℝ)) (hi := (8117/50000 : ℝ)) (c := (1095698756552163201/1095800000000000000 : ℝ)) (alpha := (25564084969/54790000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-659321517/5000000000 : ℝ)*X 0 0+(168872383/312500000 : ℝ)*X 0 1+(5403916291/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2625380409/5000000000 : ℝ)*X 1 0+(-1533963277/10000000000 : ℝ)*X 1 1+(1350979081/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((131269023/250000000 : ℝ)*X 2 0+(5403916273/10000000000 : ℝ)*X 2 1+(-1533963209/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2221818559/5000000000 : ℝ)*X 0 0+(80835791/200000000 : ℝ)*X 0 1+(252611857/625000000 : ℝ)*X 0 2+(2221818559/5000000000 : ℝ)*X 1 0+(80835791/200000000 : ℝ)*X 1 1+(252611857/625000000 : ℝ)*X 1 2+(2221818559/5000000000 : ℝ)*X 2 0+(80835791/200000000 : ℝ)*X 2 1+(252611857/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1833257879/10000000000 : ℝ)*X 0 0+(5216084083/10000000000 : ℝ)*X 0 1+(5093832/9765625 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5379393981/10000000000 : ℝ)*X 1 0+(-1614966211/10000000000 : ℝ)*X 1 1+(1304021053/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5379394313/10000000000 : ℝ)*X 2 0+(1043216753/2000000000 : ℝ)*X 2 1+(-1614966363/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3885398371/10000000000 : ℝ)*X 0 0+(34564727/80000000 : ℝ)*X 0 1+(4320590819/10000000000 : ℝ)*X 0 2+(3885398371/10000000000 : ℝ)*X 1 0+(34564727/80000000 : ℝ)*X 1 1+(4320590819/10000000000 : ℝ)*X 1 2+(3885398371/10000000000 : ℝ)*X 2 0+(34564727/80000000 : ℝ)*X 2 1+(4320590819/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-430840209/2500000000 : ℝ)*X 0 0+(79384561/156250000 : ℝ)*X 0 1+(5433161291/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((104614723/200000000 : ℝ)*X 1 0+(-1520935673/10000000000 : ℝ)*X 1 1+(543316141/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1307684041/2500000000 : ℝ)*X 2 0+(2716580741/5000000000 : ℝ)*X 2 1+(-304187111/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2264091639/5000000000 : ℝ)*X 0 0+(799660423/2000000000 : ℝ)*X 0 1+(799660307/2000000000 : ℝ)*X 0 2+(2264091639/5000000000 : ℝ)*X 1 0+(799660423/2000000000 : ℝ)*X 1 1+(799660307/2000000000 : ℝ)*X 1 2+(2264091639/5000000000 : ℝ)*X 2 0+(799660423/2000000000 : ℝ)*X 2 1+(799660307/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1426578141/10000000000 : ℝ)*X 0 0+(27671673/50000000 : ℝ)*X 0 1+(1299076921/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((134823713/250000000 : ℝ)*X 1 0+(-1623218081/10000000000 : ℝ)*X 1 1+(5196307951/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5392947651/10000000000 : ℝ)*X 2 0+(1039261677/2000000000 : ℝ)*X 2 1+(-1623218679/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3824994347/10000000000 : ℝ)*X 0 0+(2174945399/5000000000 : ℝ)*X 0 1+(2174945331/5000000000 : ℝ)*X 0 2+(3824994347/10000000000 : ℝ)*X 1 0+(2174945399/5000000000 : ℝ)*X 1 1+(2174945331/5000000000 : ℝ)*X 1 2+(3824994347/10000000000 : ℝ)*X 2 0+(2174945399/5000000000 : ℝ)*X 2 1+(2174945331/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-65141/100000 : ℝ) ≤ (-17844799878723310981649106658839/27395000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10050171/50000000000000 : ℝ)*(upper1) + (7406557/100000000000000 : ℝ)*(upper3) + (2279283/6250000000000 : ℝ)*(upper5) + (895550562436987/50000000000000 : ℝ)*(major0) + (895550562436987/50000000000000 : ℝ)*(major1) + (895550562436987/50000000000000 : ℝ)*(major2) + (1239465329/25000000000000 : ℝ)*(sp2) + (523934667/50000000000000 : ℝ)*(sp3) + (327566504254363/12500000000000 : ℝ)*(sp4) + (262051686718991/10000000000000 : ℝ)*(sp5) + (524105809068447/20000000000000 : ℝ)*(sp6) + (983380163180407/100000000000000 : ℝ)*(sp7) + (1969168647/100000000000000 : ℝ)*(sp8) + (428400341/2500000000000 : ℝ)*(sp13) + (49169060552487/5000000000000 : ℝ)*(f.failure) + (2620534003203551/100000000000000 : ℝ)*(f.sum) + (19582076444967/5479000000000000000000000000 : ℝ)*base66 + (489187869827774613/54790000000000000000000000000000 : ℝ)*base68 + (476168933993675387/54790000000000000000000000000000 : ℝ)*base69 + (148270692281234613/54790000000000000000000000000000 : ℝ)*base72 + (20861702779413/5479000000000000000000000000 : ℝ)*base74 + (207966941332985387/54790000000000000000000000000000 : ℝ)*base75 + (485477706845584613/54790000000000000000000000000000 : ℝ)*base78 + (473260587936944613/54790000000000000000000000000000 : ℝ)*base80 + (20698983016061/1369750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (308617/500000000000000000000 : ℝ)*base90 + (308617/500000000000000000000 : ℝ)*base92 + (308617/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (58809/100000 : ℝ) ≤ (32222677507333851430784832323961/54790000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3556309/20000000000000 : ℝ)*(lower1) + (2068279/100000000000000 : ℝ)*(lower2) + (20454377/100000000000000 : ℝ)*(lower3) + (20809213/100000000000000 : ℝ)*(upper4) + (1883912698610413/100000000000000 : ℝ)*(major0) + (1883912698610413/100000000000000 : ℝ)*(major1) + (1883912698610413/100000000000000 : ℝ)*(major2) + (4240442859577/156250000000 : ℝ)*(sp0) + (1356941405515679/50000000000000 : ℝ)*(sp1) + (542776636901223/20000000000000 : ℝ)*(sp2) + (517168766537673/50000000000000 : ℝ)*(sp3) + (619097923/100000000000000 : ℝ)*(sp5) + (122811583/50000000000000 : ℝ)*(sp6) + (2687071/390625000000 : ℝ)*(sp7) + (517169110482761/50000000000000 : ℝ)*(f.failure) + (4240442859577/156250000000 : ℝ)*(f.sum) + (6040961207539/2739500000000000000000000000 : ℝ)*base65 + (796840764409552013/109580000000000000000000000000000 : ℝ)*base67 + (908756900867872013/109580000000000000000000000000000 : ℝ)*base69 + (652428082068972013/109580000000000000000000000000000 : ℝ)*base71 + (1322449778979/1095800000000000000000000000 : ℝ)*base73 + (11704427446832013/109580000000000000000000000000000 : ℝ)*base75 + (122625609191607987/109580000000000000000000000000000 : ℝ)*base78 + (126199100984347987/109580000000000000000000000000000 : ℝ)*base80 + (49677255618157/5479000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (15398151/5000000000000000000000 : ℝ)*base90 + (15398151/5000000000000000000000 : ℝ)*base92 + (15398151/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (163/200 : ℝ) ≤ (2232767099881487801758041519/2739500000000000000000000000 : ℝ) := by norm_num
    linear_combination (6523111/100000000000000 : ℝ)*(upper3) + (62738239/100000000000000 : ℝ)*(upper4) + (3817931/6250000000000 : ℝ)*(lower5) + (1973620498993073/100000000000000 : ℝ)*(major0) + (1973620498993073/100000000000000 : ℝ)*(major1) + (1973620498993073/100000000000000 : ℝ)*(major2) + (315038039/100000000000000 : ℝ)*(sp0) + (9626354527/100000000000000 : ℝ)*(sp1) + (1217923993/3125000000000 : ℝ)*(sp2) + (155909091/3125000000000 : ℝ)*(sp3) + (1418240982418387/50000000000000 : ℝ)*(sp8) + (1418236326760143/50000000000000 : ℝ)*(sp9) + (709110826576759/25000000000000 : ℝ)*(sp10) + (270896538661743/25000000000000 : ℝ)*(sp11) + (270897785934471/25000000000000 : ℝ)*(f.failure) + (2836482279874813/100000000000000 : ℝ)*(f.sum) + (5144423922561/1369750000000000000000000000 : ℝ)*base66 + (74994135015553327/109580000000000000000000000000000 : ℝ)*base68 + (183025904026986673/109580000000000000000000000000000 : ℝ)*base69 + (619445954637193327/109580000000000000000000000000000 : ℝ)*base72 + (11336789530643/5479000000000000000000000000 : ℝ)*base74 + (117996210284513327/109580000000000000000000000000000 : ℝ)*base76 + (651911961954766673/109580000000000000000000000000000 : ℝ)*base77 + (621519738122846673/109580000000000000000000000000000 : ℝ)*base79 + (649622922337/2739500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (7062761/2500000000000000000000 : ℝ)*base90 + (7062761/2500000000000000000000 : ℝ)*base92 + (7062761/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-88387/100000 : ℝ) ≤ (-6053204350268675499634752991803/6848750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21391837/100000000000000 : ℝ)*(lower0) + (6206223/3125000000000 : ℝ)*(upper3) + (211067107/100000000000000 : ℝ)*(lower4) + (252322998502467/12500000000000 : ℝ)*(major0) + (252322998502467/12500000000000 : ℝ)*(major1) + (252322998502467/12500000000000 : ℝ)*(major2) + (51711409/25000000000000 : ℝ)*(sp0) + (31326812137/50000000000000 : ℝ)*(sp5) + (358864137/1250000000000 : ℝ)*(sp6) + (3776878209/10000000000000 : ℝ)*(sp7) + (1479175677059279/50000000000000 : ℝ)*(sp12) + (36978611341749/1250000000000 : ℝ)*(sp13) + (1479161425916617/50000000000000 : ℝ)*(sp14) + (554120002346613/50000000000000 : ℝ)*(sp15) + (277069443368829/25000000000000 : ℝ)*(f.failure) + (1479175780482097/50000000000000 : ℝ)*(f.sum) + (13683598554961/2739500000000000000000000000 : ℝ)*base66 + (83793026195561867/13697500000000000000000000000000 : ℝ)*base67 + (50216147804251867/13697500000000000000000000000000 : ℝ)*base69 + (45237942978391867/13697500000000000000000000000000 : ℝ)*base71 + (6406267066647/1369750000000000000000000000 : ℝ)*base74 + (68543262267901867/13697500000000000000000000000000 : ℝ)*base75 + (22661030110941867/13697500000000000000000000000000 : ℝ)*base77 + (66449719136446867/13697500000000000000000000000000 : ℝ)*base79 + (5149860032889/1369750000000000000000000000 : ℝ)*base82 + (2107539/2500000000000000000000 : ℝ)*base90 + (2107539/2500000000000000000000 : ℝ)*base92 + (2107539/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1667_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (182137009/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2151/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65141/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58809/100000 : ℝ) else (163/200 : ℝ) ≤ X j i ∧ X j i ≤ (88387/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1667_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1667_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (182137009/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4073/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10703/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65141/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58809/100000 : ℝ) else (163/200 : ℝ) ≤ X j i ∧ X j i ≤ (88387/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1667_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1667_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1667_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (182137009/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4073/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10703/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65141/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58809/100000 : ℝ) else (163/200 : ℝ) ≤ X j i ∧ X j i ≤ (88387/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1667_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1669_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:25:16.528808+00:00
-- url     : https://prove2.me/submissions/4736e2eb-b3bd-436f-b6d5-36d4ad9046ee

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
theorem support_rectangle_w1669_s0_0 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-729946017/5000000000 : ℝ)*x 0 + (720281221/1250000000 : ℝ)*x 1 + (4934164109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (729946017/5000000000 : ℝ)^4995 ≤ (8888418614643/100000000000000 : ℝ)^3971 := by
    have hnat : (729946017 : ℕ)^4995*100000000000000^3971 ≤ 8888418614643^3971*5000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      729946017 5000000000 8888418614643 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (720281221/1250000000 : ℝ)^4995 ≤ (24993441998807/50000000000000 : ℝ)^3971 := by
    have hnat : (720281221 : ℕ)^4995*50000000000000^3971 ≤ 24993441998807^3971*1250000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      720281221 1250000000 24993441998807 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4934164109/10000000000 : ℝ)^4995 ≤ (10281174343039/25000000000000 : ℝ)^3971 := by
    have hnat : (4934164109 : ℕ)^4995*25000000000000^3971 ≤ 10281174343039^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4934164109 10000000000 10281174343039 25000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-729946017/5000000000 : ℝ), (720281221/1250000000 : ℝ), (4934164109/10000000000 : ℝ)] ![(8888418614643/100000000000000 : ℝ), (24993441998807/50000000000000 : ℝ), (10281174343039/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-729946017/5000000000 : ℝ)|^4995 ≤ (8888418614643/100000000000000 : ℝ)^3971
        have hw : |(-729946017/5000000000 : ℝ)|=(729946017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(720281221/1250000000 : ℝ)|^4995 ≤ (24993441998807/50000000000000 : ℝ)^3971
        have hw : |(720281221/1250000000 : ℝ)|=(720281221/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4934164109/10000000000 : ℝ)|^4995 ≤ (10281174343039/25000000000000 : ℝ)^3971
        have hw : |(4934164109/10000000000 : ℝ)|=(4934164109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_s0_1 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5430077989/10000000000 : ℝ)*x 0 + (-1912725167/10000000000 : ℝ)*x 1 + (1233541269/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5430077989/10000000000 : ℝ)^4995 ≤ (46389599798313/100000000000000 : ℝ)^3971 := by
    have hnat : (5430077989 : ℕ)^4995*100000000000000^3971 ≤ 46389599798313^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430077989 10000000000 46389599798313 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1912725167/10000000000 : ℝ)^4995 ≤ (6242846341309/50000000000000 : ℝ)^3971 := by
    have hnat : (1912725167 : ℕ)^4995*50000000000000^3971 ≤ 6242846341309^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1912725167 10000000000 6242846341309 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1233541269/2500000000 : ℝ)^4995 ≤ (41124707510131/100000000000000 : ℝ)^3971 := by
    have hnat : (1233541269 : ℕ)^4995*100000000000000^3971 ≤ 41124707510131^3971*2500000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1233541269 2500000000 41124707510131 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5430077989/10000000000 : ℝ), (-1912725167/10000000000 : ℝ), (1233541269/2500000000 : ℝ)] ![(46389599798313/100000000000000 : ℝ), (6242846341309/50000000000000 : ℝ), (41124707510131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5430077989/10000000000 : ℝ)|^4995 ≤ (46389599798313/100000000000000 : ℝ)^3971
        have hw : |(5430077989/10000000000 : ℝ)|=(5430077989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1912725167/10000000000 : ℝ)|^4995 ≤ (6242846341309/50000000000000 : ℝ)^3971
        have hw : |(-1912725167/10000000000 : ℝ)|=(1912725167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1233541269/2500000000 : ℝ)|^4995 ≤ (41124707510131/100000000000000 : ℝ)^3971
        have hw : |(1233541269/2500000000 : ℝ)|=(1233541269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_s0_2 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1357520049/2500000000 : ℝ)*x 0 + (1233540931/2500000000 : ℝ)*x 1 + (-478181001/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1357520049/2500000000 : ℝ)^4995 ≤ (23194811757459/50000000000000 : ℝ)^3971 := by
    have hnat : (1357520049 : ℕ)^4995*50000000000000^3971 ≤ 23194811757459^3971*2500000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357520049 2500000000 23194811757459 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1233540931/2500000000 : ℝ)^4995 ≤ (20562346667919/50000000000000 : ℝ)^3971 := by
    have hnat : (1233540931 : ℕ)^4995*50000000000000^3971 ≤ 20562346667919^3971*2500000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1233540931 2500000000 20562346667919 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (478181001/2500000000 : ℝ)^4995 ≤ (6242841566617/50000000000000 : ℝ)^3971 := by
    have hnat : (478181001 : ℕ)^4995*50000000000000^3971 ≤ 6242841566617^3971*2500000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478181001 2500000000 6242841566617 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1357520049/2500000000 : ℝ), (1233540931/2500000000 : ℝ), (-478181001/2500000000 : ℝ)] ![(23194811757459/50000000000000 : ℝ), (20562346667919/50000000000000 : ℝ), (6242841566617/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1357520049/2500000000 : ℝ)|^4995 ≤ (23194811757459/50000000000000 : ℝ)^3971
        have hw : |(1357520049/2500000000 : ℝ)|=(1357520049/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1233540931/2500000000 : ℝ)|^4995 ≤ (20562346667919/50000000000000 : ℝ)^3971
        have hw : |(1233540931/2500000000 : ℝ)|=(1233540931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-478181001/2500000000 : ℝ)|^4995 ≤ (6242841566617/50000000000000 : ℝ)^3971
        have hw : |(-478181001/2500000000 : ℝ)|=(478181001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_s0_3 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4081810801/10000000000 : ℝ)*x 0 + (3087662081/10000000000 : ℝ)*x 1 + (5281493433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4081810801/10000000000 : ℝ)^4995 ≤ (16198458145069/50000000000000 : ℝ)^3971 := by
    have hnat : (4081810801 : ℕ)^4995*50000000000000^3971 ≤ 16198458145069^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4081810801 10000000000 16198458145069 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3087662081/10000000000 : ℝ)^4995 ≤ (22804513893691/100000000000000 : ℝ)^3971 := by
    have hnat : (3087662081 : ℕ)^4995*100000000000000^3971 ≤ 22804513893691^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3087662081 10000000000 22804513893691 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5281493433/10000000000 : ℝ)^4995 ≤ (44798569799541/100000000000000 : ℝ)^3971 := by
    have hnat : (5281493433 : ℕ)^4995*100000000000000^3971 ≤ 44798569799541^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281493433 10000000000 44798569799541 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4081810801/10000000000 : ℝ), (3087662081/10000000000 : ℝ), (5281493433/10000000000 : ℝ)] ![(16198458145069/50000000000000 : ℝ), (22804513893691/100000000000000 : ℝ), (44798569799541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4081810801/10000000000 : ℝ)|^4995 ≤ (16198458145069/50000000000000 : ℝ)^3971
        have hw : |(4081810801/10000000000 : ℝ)|=(4081810801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3087662081/10000000000 : ℝ)|^4995 ≤ (22804513893691/100000000000000 : ℝ)^3971
        have hw : |(3087662081/10000000000 : ℝ)|=(3087662081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5281493433/10000000000 : ℝ)|^4995 ≤ (44798569799541/100000000000000 : ℝ)^3971
        have hw : |(5281493433/10000000000 : ℝ)|=(5281493433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_s0_4 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1461983737/10000000000 : ℝ)*x 0 + (4954492313/10000000000 : ℝ)*x 1 + (2870615103/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1461983737/10000000000 : ℝ)^4995 ≤ (4452220359937/50000000000000 : ℝ)^3971 := by
    have hnat : (1461983737 : ℕ)^4995*50000000000000^3971 ≤ 4452220359937^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1461983737 10000000000 4452220359937 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4954492313/10000000000 : ℝ)^4995 ≤ (10334482559157/25000000000000 : ℝ)^3971 := by
    have hnat : (4954492313 : ℕ)^4995*25000000000000^3971 ≤ 10334482559157^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4954492313 10000000000 10334482559157 25000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2870615103/5000000000 : ℝ)^4995 ≤ (12439407256871/25000000000000 : ℝ)^3971 := by
    have hnat : (2870615103 : ℕ)^4995*25000000000000^3971 ≤ 12439407256871^3971*5000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2870615103 5000000000 12439407256871 25000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1461983737/10000000000 : ℝ), (4954492313/10000000000 : ℝ), (2870615103/5000000000 : ℝ)] ![(4452220359937/50000000000000 : ℝ), (10334482559157/25000000000000 : ℝ), (12439407256871/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1461983737/10000000000 : ℝ)|^4995 ≤ (4452220359937/50000000000000 : ℝ)^3971
        have hw : |(-1461983737/10000000000 : ℝ)|=(1461983737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4954492313/10000000000 : ℝ)|^4995 ≤ (10334482559157/25000000000000 : ℝ)^3971
        have hw : |(4954492313/10000000000 : ℝ)|=(4954492313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2870615103/5000000000 : ℝ)|^4995 ≤ (12439407256871/25000000000000 : ℝ)^3971
        have hw : |(2870615103/5000000000 : ℝ)|=(2870615103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_s0_5 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2602135697/5000000000 : ℝ)*x 0 + (-138207369/1250000000 : ℝ)*x 1 + (5741231963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2602135697/5000000000 : ℝ)^4995 ≤ (85891035459/195312500000 : ℝ)^3971 := by
    have hnat : (2602135697 : ℕ)^4995*195312500000^3971 ≤ 85891035459^3971*5000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2602135697 5000000000 85891035459 195312500000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (138207369/1250000000 : ℝ)^4995 ≤ (6266141650857/100000000000000 : ℝ)^3971 := by
    have hnat : (138207369 : ℕ)^4995*100000000000000^3971 ≤ 6266141650857^3971*1250000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138207369 1250000000 6266141650857 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5741231963/10000000000 : ℝ)^4995 ≤ (49757648181599/100000000000000 : ℝ)^3971 := by
    have hnat : (5741231963 : ℕ)^4995*100000000000000^3971 ≤ 49757648181599^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5741231963 10000000000 49757648181599 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2602135697/5000000000 : ℝ), (-138207369/1250000000 : ℝ), (5741231963/10000000000 : ℝ)] ![(85891035459/195312500000 : ℝ), (6266141650857/100000000000000 : ℝ), (49757648181599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2602135697/5000000000 : ℝ)|^4995 ≤ (85891035459/195312500000 : ℝ)^3971
        have hw : |(2602135697/5000000000 : ℝ)|=(2602135697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-138207369/1250000000 : ℝ)|^4995 ≤ (6266141650857/100000000000000 : ℝ)^3971
        have hw : |(-138207369/1250000000 : ℝ)|=(138207369/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5741231963/10000000000 : ℝ)|^4995 ≤ (49757648181599/100000000000000 : ℝ)^3971
        have hw : |(5741231963/10000000000 : ℝ)|=(5741231963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_s0_6 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1040854349/2000000000 : ℝ)*x 0 + (5741231437/10000000000 : ℝ)*x 1 + (-1105659233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1040854349/2000000000 : ℝ)^4995 ≤ (10994053471449/25000000000000 : ℝ)^3971 := by
    have hnat : (1040854349 : ℕ)^4995*25000000000000^3971 ≤ 10994053471449^3971*2000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040854349 2000000000 10994053471449 25000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5741231437/10000000000 : ℝ)^4995 ≤ (12439410611839/25000000000000 : ℝ)^3971 := by
    have hnat : (5741231437 : ℕ)^4995*25000000000000^3971 ≤ 12439410611839^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5741231437 10000000000 12439410611839 25000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1105659233/10000000000 : ℝ)^4995 ≤ (3133071827021/50000000000000 : ℝ)^3971 := by
    have hnat : (1105659233 : ℕ)^4995*50000000000000^3971 ≤ 3133071827021^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105659233 10000000000 3133071827021 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1040854349/2000000000 : ℝ), (5741231437/10000000000 : ℝ), (-1105659233/10000000000 : ℝ)] ![(10994053471449/25000000000000 : ℝ), (12439410611839/25000000000000 : ℝ), (3133071827021/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1040854349/2000000000 : ℝ)|^4995 ≤ (10994053471449/25000000000000 : ℝ)^3971
        have hw : |(1040854349/2000000000 : ℝ)|=(1040854349/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5741231437/10000000000 : ℝ)|^4995 ≤ (12439410611839/25000000000000 : ℝ)^3971
        have hw : |(5741231437/10000000000 : ℝ)|=(5741231437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1105659233/10000000000 : ℝ)|^4995 ≤ (3133071827021/50000000000000 : ℝ)^3971
        have hw : |(-1105659233/10000000000 : ℝ)|=(1105659233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_s0_7 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2043675899/5000000000 : ℝ)*x 0 + (5227638001/10000000000 : ℝ)*x 1 + (3143346949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2043675899/5000000000 : ℝ)^4995 ≤ (32452244969581/100000000000000 : ℝ)^3971 := by
    have hnat : (2043675899 : ℕ)^4995*100000000000000^3971 ≤ 32452244969581^3971*5000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2043675899 5000000000 32452244969581 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5227638001/10000000000 : ℝ)^4995 ≤ (5528089755921/12500000000000 : ℝ)^3971 := by
    have hnat : (5227638001 : ℕ)^4995*12500000000000^3971 ≤ 5528089755921^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227638001 10000000000 5528089755921 12500000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3143346949/10000000000 : ℝ)^4995 ≤ (4664607392833/20000000000000 : ℝ)^3971 := by
    have hnat : (3143346949 : ℕ)^4995*20000000000000^3971 ≤ 4664607392833^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3143346949 10000000000 4664607392833 20000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2043675899/5000000000 : ℝ), (5227638001/10000000000 : ℝ), (3143346949/10000000000 : ℝ)] ![(32452244969581/100000000000000 : ℝ), (5528089755921/12500000000000 : ℝ), (4664607392833/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2043675899/5000000000 : ℝ)|^4995 ≤ (32452244969581/100000000000000 : ℝ)^3971
        have hw : |(2043675899/5000000000 : ℝ)|=(2043675899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5227638001/10000000000 : ℝ)|^4995 ≤ (5528089755921/12500000000000 : ℝ)^3971
        have hw : |(5227638001/10000000000 : ℝ)|=(5227638001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3143346949/10000000000 : ℝ)|^4995 ≤ (4664607392833/20000000000000 : ℝ)^3971
        have hw : |(3143346949/10000000000 : ℝ)|=(3143346949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1669_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (182463933/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2601/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (287/1250 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4991/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4991 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4991*1^1024 ≤ 0^1024*1^4991 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4991 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4991 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4991/1024 : ℝ) ≤ (143661727367461389/12500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4991 ≤ (143661727367461389/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4991*12500000000000000000^1024 ≤ 143661727367461389^1024*5^4991 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 143661727367461389 12500000000000000000 4991 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (143661727367461389/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4991 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4991/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4991 := by
      have hnat : (1 : ℕ)^1024*1^4991 ≤ 1^4991*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4991 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4991 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12643661727367461389/12500000000000000000 : ℝ) ≤ (25058682537929/25000000000000 : ℝ) ^ (4991/1024 : ℝ) := by
    have hpowers : (12643661727367461389/12500000000000000000 : ℝ)^1024 ≤ (25058682537929/25000000000000 : ℝ)^4991 := by
      have hnat : (12643661727367461389 : ℕ)^1024*25000000000000^4991 ≤ 25058682537929^4991*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12643661727367461389 12500000000000000000 25058682537929 25000000000000 1024 4991 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (25058682537929/25000000000000 : ℝ)) (X := (12643661727367461389/12500000000000000000 : ℝ)) (by norm_num) 4991 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6393661727367461389/6250000000000000000 : ℝ) ≤ (12558682537929/12500000000000 : ℝ) ^ (4991/1024 : ℝ) := by
    have hpowers : (6393661727367461389/6250000000000000000 : ℝ)^1024 ≤ (12558682537929/12500000000000 : ℝ)^4991 := by
      have hnat : (6393661727367461389 : ℕ)^1024*12500000000000^4991 ≤ 12558682537929^4991*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6393661727367461389 6250000000000000000 12558682537929 12500000000000 1024 4991 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12558682537929/12500000000000 : ℝ)) (X := (6393661727367461389/6250000000000000000 : ℝ)) (by norm_num) 4991 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(58682537929/10000000000000 : ℝ)*(0 : ℝ))^(4991/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(58682537929/10000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(143661727367461389/12500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(58682537929/10000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4991/1024 : ℝ) := by
    rw [show (1 : ℝ)+(58682537929/10000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(25058682537929/25000000000000 : ℝ) by norm_num, show 1+(143661727367461389/12500000000000000000 : ℝ)+(0 : ℝ)=(12643661727367461389/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(143661727367461389/12500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(58682537929/10000000000000 : ℝ)*(2/5 : ℝ))^(4991/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(58682537929/10000000000000 : ℝ)*(2/5 : ℝ)=(12558682537929/12500000000000 : ℝ) by norm_num, show 1+2*(143661727367461389/12500000000000000000 : ℝ)=(6393661727367461389/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(58682537929/10000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4991/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (58682537929/10000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(58682537929/10000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4991/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (58682537929/10000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(58682537929/10000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4991/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (58682537929/10000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-729946017/5000000000 : ℝ)*X 0 0+(720281221/1250000000 : ℝ)*X 0 1+(4934164109/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5430077989/10000000000 : ℝ)*X 1 0+(-1912725167/10000000000 : ℝ)*X 1 1+(1233541269/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1357520049/2500000000 : ℝ)*X 2 0+(1233540931/2500000000 : ℝ)*X 2 1+(-478181001/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4081810801/10000000000 : ℝ)*X 0 0+(3087662081/10000000000 : ℝ)*X 0 1+(5281493433/10000000000 : ℝ)*X 0 2+(4081810801/10000000000 : ℝ)*X 1 0+(3087662081/10000000000 : ℝ)*X 1 1+(5281493433/10000000000 : ℝ)*X 1 2+(4081810801/10000000000 : ℝ)*X 2 0+(3087662081/10000000000 : ℝ)*X 2 1+(5281493433/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1461983737/10000000000 : ℝ)*X 0 0+(4954492313/10000000000 : ℝ)*X 0 1+(2870615103/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2602135697/5000000000 : ℝ)*X 1 0+(-138207369/1250000000 : ℝ)*X 1 1+(5741231963/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1040854349/2000000000 : ℝ)*X 2 0+(5741231437/10000000000 : ℝ)*X 2 1+(-1105659233/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2043675899/5000000000 : ℝ)*X 0 0+(5227638001/10000000000 : ℝ)*X 0 1+(3143346949/10000000000 : ℝ)*X 0 2+(2043675899/5000000000 : ℝ)*X 1 0+(5227638001/10000000000 : ℝ)*X 1 1+(3143346949/10000000000 : ℝ)*X 1 2+(2043675899/5000000000 : ℝ)*X 2 0+(5227638001/10000000000 : ℝ)*X 2 1+(3143346949/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (268910080558078059033/62500000000000000000000000 : ℝ) := by norm_num
    linear_combination (62167587/50000000000000 : ℝ)*(base1) + (640391073/100000000000000 : ℝ)*(base19) + (505377941/50000000000000 : ℝ)*(base23) + (15057023/12500000000000 : ℝ)*(base24) + (13131029/10000000000000 : ℝ)*(upper5) + (207929792719633/25000000000000 : ℝ)*(major0) + (207929792719633/25000000000000 : ℝ)*(major1) + (207929792719633/25000000000000 : ℝ)*(major2) + (603803500222709/50000000000000 : ℝ)*(sp0) + (24152218842627/2000000000000 : ℝ)*(sp1) + (603805225655179/50000000000000 : ℝ)*(sp2) + (113956256256407/25000000000000 : ℝ)*(sp3) + (2353206089/50000000000000 : ℝ)*(sp4) + (18330689/1250000000000 : ℝ)*(sp7) + (227913307907961/50000000000000 : ℝ)*(f.failure) + (1207611582522423/100000000000000 : ℝ)*(f.sum) + (90864911307/125000000000000000000000000 : ℝ)*base65 + (3176691028557/250000000000000000000000000 : ℝ)*base67 + (1730315201557/250000000000000000000000000 : ℝ)*base69 + (1103493225557/250000000000000000000000000 : ℝ)*base71 + (729442767807/125000000000000000000000000 : ℝ)*base73 + (131130140943/250000000000000000000000000 : ℝ)*base76 + (892589471057/250000000000000000000000000 : ℝ)*base77 + (131134584943/250000000000000000000000000 : ℝ)*base80 + (567123413557/125000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base87 + (33929387/5000000000000000000000 : ℝ)*base90 + (33929387/5000000000000000000000 : ℝ)*base92 + (33929387/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (107102857857974864889/50000000000000000000000000 : ℝ) := by norm_num
    linear_combination (109404373/100000000000000 : ℝ)*(base19) + (207987409/100000000000000 : ℝ)*(base23) + (44986223/50000000000000 : ℝ)*(base32) + (89545177/50000000000000 : ℝ)*(upper3) + (517583/3125000000000 : ℝ)*(upper5) + (175084962836849/20000000000000 : ℝ)*(major0) + (175084962836849/20000000000000 : ℝ)*(major1) + (175084962836849/20000000000000 : ℝ)*(major2) + (1125426097/100000000000000 : ℝ)*(sp1) + (710859233/50000000000000 : ℝ)*(sp2) + (635534954836813/50000000000000 : ℝ)*(sp4) + (317767168710789/25000000000000 : ℝ)*(sp5) + (5084273119871/400000000000 : ℝ)*(sp6) + (95955911464101/20000000000000 : ℝ)*(sp7) + (9595592945859/2000000000000 : ℝ)*(f.failure) + (635534954836813/50000000000000 : ℝ)*(f.sum) + (51538417079/100000000000000000000000000 : ℝ)*base66 + (2659188142879/200000000000000000000000000 : ℝ)*base68 + (893045894479/200000000000000000000000000 : ℝ)*base70 + (1442593931679/200000000000000000000000000 : ℝ)*base72 + (824788133679/100000000000000000000000000 : ℝ)*base74 + (1189573223279/200000000000000000000000000 : ℝ)*base76 + (557986869479/200000000000000000000000000 : ℝ)*base78 + (652877582079/200000000000000000000000000 : ℝ)*base80 + (196008217379/100000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (796553/200000000000000000000 : ℝ)*base90 + (796553/200000000000000000000 : ℝ)*base92 + (796553/200000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1669_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (182463933/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2601/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (287/1250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1669_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1669_s1_0 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1558156279/10000000000 : ℝ)*x 0 + (548271937/1000000000 : ℝ)*x 1 + (32185423/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1558156279/10000000000 : ℝ)^4995 ≤ (9647393127433/100000000000000 : ℝ)^3971 := by
    have hnat : (1558156279 : ℕ)^4995*100000000000000^3971 ≤ 9647393127433^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1558156279 10000000000 9647393127433 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (548271937/1000000000 : ℝ)^4995 ≤ (5869499225637/12500000000000 : ℝ)^3971 := by
    have hnat : (548271937 : ℕ)^4995*12500000000000^3971 ≤ 5869499225637^3971*1000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548271937 1000000000 5869499225637 12500000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32185423/62500000 : ℝ)^4995 ≤ (21698306524471/50000000000000 : ℝ)^3971 := by
    have hnat : (32185423 : ℕ)^4995*50000000000000^3971 ≤ 21698306524471^3971*62500000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32185423 62500000 21698306524471 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1558156279/10000000000 : ℝ), (548271937/1000000000 : ℝ), (32185423/62500000 : ℝ)] ![(9647393127433/100000000000000 : ℝ), (5869499225637/12500000000000 : ℝ), (21698306524471/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1558156279/10000000000 : ℝ)|^4995 ≤ (9647393127433/100000000000000 : ℝ)^3971
        have hw : |(-1558156279/10000000000 : ℝ)|=(1558156279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(548271937/1000000000 : ℝ)|^4995 ≤ (5869499225637/12500000000000 : ℝ)^3971
        have hw : |(548271937/1000000000 : ℝ)|=(548271937/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(32185423/62500000 : ℝ)|^4995 ≤ (21698306524471/50000000000000 : ℝ)^3971
        have hw : |(32185423/62500000 : ℝ)|=(32185423/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_s1_1 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338929047/2500000000 : ℝ)*x 0 + (-1730899627/10000000000 : ℝ)*x 1 + (5149667397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338929047/2500000000 : ℝ)^4995 ≤ (45591917527513/100000000000000 : ℝ)^3971 := by
    have hnat : (1338929047 : ℕ)^4995*100000000000000^3971 ≤ 45591917527513^3971*2500000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338929047 2500000000 45591917527513 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1730899627/10000000000 : ℝ)^4995 ≤ (11011472402499/100000000000000 : ℝ)^3971 := by
    have hnat : (1730899627 : ℕ)^4995*100000000000000^3971 ≤ 11011472402499^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1730899627 10000000000 11011472402499 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5149667397/10000000000 : ℝ)^4995 ≤ (21698305024549/50000000000000 : ℝ)^3971 := by
    have hnat : (5149667397 : ℕ)^4995*50000000000000^3971 ≤ 21698305024549^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5149667397 10000000000 21698305024549 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338929047/2500000000 : ℝ), (-1730899627/10000000000 : ℝ), (5149667397/10000000000 : ℝ)] ![(45591917527513/100000000000000 : ℝ), (11011472402499/100000000000000 : ℝ), (21698305024549/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338929047/2500000000 : ℝ)|^4995 ≤ (45591917527513/100000000000000 : ℝ)^3971
        have hw : |(1338929047/2500000000 : ℝ)|=(1338929047/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1730899627/10000000000 : ℝ)|^4995 ≤ (11011472402499/100000000000000 : ℝ)^3971
        have hw : |(-1730899627/10000000000 : ℝ)|=(1730899627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5149667397/10000000000 : ℝ)|^4995 ≤ (21698305024549/50000000000000 : ℝ)^3971
        have hw : |(5149667397/10000000000 : ℝ)|=(5149667397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_s1_2 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5355715609/10000000000 : ℝ)*x 0 + (5149668053/10000000000 : ℝ)*x 1 + (-865449767/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355715609/10000000000 : ℝ)^4995 ≤ (356186807247/781250000000 : ℝ)^3971 := by
    have hnat : (5355715609 : ℕ)^4995*781250000000^3971 ≤ 356186807247^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355715609 10000000000 356186807247 781250000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5149668053/10000000000 : ℝ)^4995 ≤ (108491542507/250000000000 : ℝ)^3971 := by
    have hnat : (5149668053 : ℕ)^4995*250000000000^3971 ≤ 108491542507^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5149668053 10000000000 108491542507 250000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (865449767/5000000000 : ℝ)^4995 ≤ (2202294331659/20000000000000 : ℝ)^3971 := by
    have hnat : (865449767 : ℕ)^4995*20000000000000^3971 ≤ 2202294331659^3971*5000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865449767 5000000000 2202294331659 20000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355715609/10000000000 : ℝ), (5149668053/10000000000 : ℝ), (-865449767/5000000000 : ℝ)] ![(356186807247/781250000000 : ℝ), (108491542507/250000000000 : ℝ), (2202294331659/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355715609/10000000000 : ℝ)|^4995 ≤ (356186807247/781250000000 : ℝ)^3971
        have hw : |(5355715609/10000000000 : ℝ)|=(5355715609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5149668053/10000000000 : ℝ)|^4995 ≤ (108491542507/250000000000 : ℝ)^3971
        have hw : |(5149668053/10000000000 : ℝ)|=(5149668053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-865449767/5000000000 : ℝ)|^4995 ≤ (2202294331659/20000000000000 : ℝ)^3971
        have hw : |(-865449767/5000000000 : ℝ)|=(865449767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_s1_3 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4160336717/10000000000 : ℝ)*x 0 + (3735636059/10000000000 : ℝ)*x 1 + (2308991729/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4160336717/10000000000 : ℝ)^4995 ≤ (33182821665957/100000000000000 : ℝ)^3971 := by
    have hnat : (4160336717 : ℕ)^4995*100000000000000^3971 ≤ 33182821665957^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4160336717 10000000000 33182821665957 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3735636059/10000000000 : ℝ)^4995 ≤ (5795893463439/20000000000000 : ℝ)^3971 := by
    have hnat : (3735636059 : ℕ)^4995*20000000000000^3971 ≤ 5795893463439^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3735636059 10000000000 5795893463439 20000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2308991729/5000000000 : ℝ)^4995 ≤ (37837711006849/100000000000000 : ℝ)^3971 := by
    have hnat : (2308991729 : ℕ)^4995*100000000000000^3971 ≤ 37837711006849^3971*5000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2308991729 5000000000 37837711006849 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4160336717/10000000000 : ℝ), (3735636059/10000000000 : ℝ), (2308991729/5000000000 : ℝ)] ![(33182821665957/100000000000000 : ℝ), (5795893463439/20000000000000 : ℝ), (37837711006849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4160336717/10000000000 : ℝ)|^4995 ≤ (33182821665957/100000000000000 : ℝ)^3971
        have hw : |(4160336717/10000000000 : ℝ)|=(4160336717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3735636059/10000000000 : ℝ)|^4995 ≤ (5795893463439/20000000000000 : ℝ)^3971
        have hw : |(3735636059/10000000000 : ℝ)|=(3735636059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2308991729/5000000000 : ℝ)|^4995 ≤ (37837711006849/100000000000000 : ℝ)^3971
        have hw : |(2308991729/5000000000 : ℝ)|=(2308991729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_s1_4 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1558289957/10000000000 : ℝ)*x 0 + (2576476137/5000000000 : ℝ)*x 1 + (2739695131/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1558289957/10000000000 : ℝ)^4995 ≤ (9648434243889/100000000000000 : ℝ)^3971 := by
    have hnat : (1558289957 : ℕ)^4995*100000000000000^3971 ≤ 9648434243889^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1558289957 10000000000 9648434243889 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2576476137/5000000000 : ℝ)^4995 ≤ (21715716559513/50000000000000 : ℝ)^3971 := by
    have hnat : (2576476137 : ℕ)^4995*50000000000000^3971 ≤ 21715716559513^3971*5000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2576476137 5000000000 21715716559513 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2739695131/5000000000 : ℝ)^4995 ≤ (11730033157793/25000000000000 : ℝ)^3971 := by
    have hnat : (2739695131 : ℕ)^4995*25000000000000^3971 ≤ 11730033157793^3971*5000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2739695131 5000000000 11730033157793 25000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1558289957/10000000000 : ℝ), (2576476137/5000000000 : ℝ), (2739695131/5000000000 : ℝ)] ![(9648434243889/100000000000000 : ℝ), (21715716559513/50000000000000 : ℝ), (11730033157793/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1558289957/10000000000 : ℝ)|^4995 ≤ (9648434243889/100000000000000 : ℝ)^3971
        have hw : |(-1558289957/10000000000 : ℝ)|=(1558289957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2576476137/5000000000 : ℝ)|^4995 ≤ (21715716559513/50000000000000 : ℝ)^3971
        have hw : |(2576476137/5000000000 : ℝ)|=(2576476137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2739695131/5000000000 : ℝ)|^4995 ≤ (11730033157793/25000000000000 : ℝ)^3971
        have hw : |(2739695131/5000000000 : ℝ)|=(2739695131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_s1_5 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (329156829/625000000 : ℝ)*x 0 + (-43786793/312500000 : ℝ)*x 1 + (5479390259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (329156829/625000000 : ℝ)^4995 ≤ (11159688780137/25000000000000 : ℝ)^3971 := by
    have hnat : (329156829 : ℕ)^4995*25000000000000^3971 ≤ 11159688780137^3971*625000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329156829 625000000 11159688780137 25000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43786793/312500000 : ℝ)^4995 ≤ (8441112273347/100000000000000 : ℝ)^3971 := by
    have hnat : (43786793 : ℕ)^4995*100000000000000^3971 ≤ 8441112273347^3971*312500000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43786793 312500000 8441112273347 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5479390259/10000000000 : ℝ)^4995 ≤ (23460066299429/50000000000000 : ℝ)^3971 := by
    have hnat : (5479390259 : ℕ)^4995*50000000000000^3971 ≤ 23460066299429^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5479390259 10000000000 23460066299429 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(329156829/625000000 : ℝ), (-43786793/312500000 : ℝ), (5479390259/10000000000 : ℝ)] ![(11159688780137/25000000000000 : ℝ), (8441112273347/100000000000000 : ℝ), (23460066299429/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(329156829/625000000 : ℝ)|^4995 ≤ (11159688780137/25000000000000 : ℝ)^3971
        have hw : |(329156829/625000000 : ℝ)|=(329156829/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-43786793/312500000 : ℝ)|^4995 ≤ (8441112273347/100000000000000 : ℝ)^3971
        have hw : |(-43786793/312500000 : ℝ)|=(43786793/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5479390259/10000000000 : ℝ)|^4995 ≤ (23460066299429/50000000000000 : ℝ)^3971
        have hw : |(5479390259/10000000000 : ℝ)|=(5479390259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_s1_6 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5266509229/10000000000 : ℝ)*x 0 + (21917561/40000000 : ℝ)*x 1 + (-1401177437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5266509229/10000000000 : ℝ)^4995 ≤ (4463875474739/10000000000000 : ℝ)^3971 := by
    have hnat : (5266509229 : ℕ)^4995*10000000000000^3971 ≤ 4463875474739^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266509229 10000000000 4463875474739 10000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21917561/40000000 : ℝ)^4995 ≤ (23460066250959/50000000000000 : ℝ)^3971 := by
    have hnat : (21917561 : ℕ)^4995*50000000000000^3971 ≤ 23460066250959^3971*40000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21917561 40000000 23460066250959 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1401177437/10000000000 : ℝ)^4995 ≤ (8441112735591/100000000000000 : ℝ)^3971 := by
    have hnat : (1401177437 : ℕ)^4995*100000000000000^3971 ≤ 8441112735591^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1401177437 10000000000 8441112735591 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5266509229/10000000000 : ℝ), (21917561/40000000 : ℝ), (-1401177437/10000000000 : ℝ)] ![(4463875474739/10000000000000 : ℝ), (23460066250959/50000000000000 : ℝ), (8441112735591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5266509229/10000000000 : ℝ)|^4995 ≤ (4463875474739/10000000000000 : ℝ)^3971
        have hw : |(5266509229/10000000000 : ℝ)|=(5266509229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21917561/40000000 : ℝ)|^4995 ≤ (23460066250959/50000000000000 : ℝ)^3971
        have hw : |(21917561/40000000 : ℝ)|=(21917561/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1401177437/10000000000 : ℝ)|^4995 ≤ (8441112735591/100000000000000 : ℝ)^3971
        have hw : |(-1401177437/10000000000 : ℝ)|=(1401177437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_s1_7 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2080345837/5000000000 : ℝ)*x 0 + (460928171/1000000000 : ℝ)*x 1 + (1872228491/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2080345837/5000000000 : ℝ)^4995 ≤ (33186382903633/100000000000000 : ℝ)^3971 := by
    have hnat : (2080345837 : ℕ)^4995*100000000000000^3971 ≤ 33186382903633^3971*5000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080345837 5000000000 33186382903633 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (460928171/1000000000 : ℝ)^4995 ≤ (7549609776889/20000000000000 : ℝ)^3971 := by
    have hnat : (460928171 : ℕ)^4995*20000000000000^3971 ≤ 7549609776889^3971*1000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      460928171 1000000000 7549609776889 20000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1872228491/5000000000 : ℝ)^4995 ≤ (14532784099639/50000000000000 : ℝ)^3971 := by
    have hnat : (1872228491 : ℕ)^4995*50000000000000^3971 ≤ 14532784099639^3971*5000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1872228491 5000000000 14532784099639 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2080345837/5000000000 : ℝ), (460928171/1000000000 : ℝ), (1872228491/5000000000 : ℝ)] ![(33186382903633/100000000000000 : ℝ), (7549609776889/20000000000000 : ℝ), (14532784099639/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2080345837/5000000000 : ℝ)|^4995 ≤ (33186382903633/100000000000000 : ℝ)^3971
        have hw : |(2080345837/5000000000 : ℝ)|=(2080345837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(460928171/1000000000 : ℝ)|^4995 ≤ (7549609776889/20000000000000 : ℝ)^3971
        have hw : |(460928171/1000000000 : ℝ)|=(460928171/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1872228491/5000000000 : ℝ)|^4995 ≤ (14532784099639/50000000000000 : ℝ)^3971
        have hw : |(1872228491/5000000000 : ℝ)|=(1872228491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1669_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (182463933/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (287/1250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2601/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (9999/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3417/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (287/1250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2601/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (287/1250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2601/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (287/1250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2601/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (287/1250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2601/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (287/1250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2601/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (287/1250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2601/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2601/50000 : ℝ) ^ (4991/1024 : ℝ) ≤ (55282055892969/100000000000000000000 : ℝ) := by
    have hpowers : (2601/50000 : ℝ)^4991 ≤ (55282055892969/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2601 : ℕ)^4991*100000000000000000000^1024 ≤ 55282055892969^1024*50000^4991 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2601 50000 55282055892969 100000000000000000000 4991 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2601/50000 : ℝ)) (X := (55282055892969/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4991 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (287/1250 : ℝ) ^ (4991/1024 : ℝ) ≤ (76800135109574027/100000000000000000000 : ℝ) := by
    have hpowers : (287/1250 : ℝ)^4991 ≤ (76800135109574027/100000000000000000000 : ℝ)^1024 := by
      have hnat : (287 : ℕ)^4991*100000000000000000000^1024 ≤ 76800135109574027^1024*1250^4991 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        287 1250 76800135109574027 100000000000000000000 4991 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (287/1250 : ℝ)) (X := (76800135109574027/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4991 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000055282055892969/50000000000000000000 : ℝ) ≤ (5000001134217599/5000000000000000 : ℝ) ^ (4991/1024 : ℝ) := by
    have hpowers : (50000055282055892969/50000000000000000000 : ℝ)^1024 ≤ (5000001134217599/5000000000000000 : ℝ)^4991 := by
      have hnat : (50000055282055892969 : ℕ)^1024*5000000000000000^4991 ≤ 5000001134217599^4991*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000055282055892969 50000000000000000000 5000001134217599 5000000000000000 1024 4991 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000001134217599/5000000000000000 : ℝ)) (X := (50000055282055892969/50000000000000000000 : ℝ)) (by norm_num) 4991 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25019213854291366749/25000000000000000000 : ℝ) ≤ (10001576355850297/10000000000000000 : ℝ) ^ (4991/1024 : ℝ) := by
    have hpowers : (25019213854291366749/25000000000000000000 : ℝ)^1024 ≤ (10001576355850297/10000000000000000 : ℝ)^4991 := by
      have hnat : (25019213854291366749 : ℕ)^1024*10000000000000000^4991 ≤ 10001576355850297^4991*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25019213854291366749 25000000000000000000 10001576355850297 10000000000000000 1024 4991 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001576355850297/10000000000000000 : ℝ)) (X := (25019213854291366749/25000000000000000000 : ℝ)) (by norm_num) 4991 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50076800135109574027/50000000000000000000 : ℝ) ≤ (2500787610816349/2500000000000000 : ℝ) ^ (4991/1024 : ℝ) := by
    have hpowers : (50076800135109574027/50000000000000000000 : ℝ)^1024 ≤ (2500787610816349/2500000000000000 : ℝ)^4991 := by
      have hnat : (50076800135109574027 : ℕ)^1024*2500000000000000^4991 ≤ 2500787610816349^4991*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50076800135109574027 50000000000000000000 2500787610816349 2500000000000000 1024 4991 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500787610816349/2500000000000000 : ℝ)) (X := (50076800135109574027/50000000000000000000 : ℝ)) (by norm_num) 4991 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(55282055892969/100000000000000000000 : ℝ) ≤ ((22195457934675694511/22197500000000000000 : ℝ)+2*(1574087415099/1775800000000000 : ℝ)*(2601/50000 : ℝ))^(4991/1024 : ℝ) := by
    rw [show (22195457934675694511/22197500000000000000 : ℝ)+2*(1574087415099/1775800000000000 : ℝ)*(2601/50000 : ℝ)=(5000001134217599/5000000000000000 : ℝ) by norm_num, show 1+2*(55282055892969/100000000000000000000 : ℝ)=(50000055282055892969/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(76800135109574027/100000000000000000000 : ℝ)+(55282055892969/100000000000000000000 : ℝ) ≤ ((22195457934675694511/22197500000000000000 : ℝ)+(1574087415099/1775800000000000 : ℝ)*((287/1250 : ℝ)+(2601/50000 : ℝ)))^(4991/1024 : ℝ) := by
    rw [show (22195457934675694511/22197500000000000000 : ℝ)+(1574087415099/1775800000000000 : ℝ)*((287/1250 : ℝ)+(2601/50000 : ℝ))=(10001576355850297/10000000000000000 : ℝ) by norm_num, show 1+(76800135109574027/100000000000000000000 : ℝ)+(55282055892969/100000000000000000000 : ℝ)=(25019213854291366749/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(76800135109574027/100000000000000000000 : ℝ) ≤ ((22195457934675694511/22197500000000000000 : ℝ)+2*(1574087415099/1775800000000000 : ℝ)*(287/1250 : ℝ))^(4991/1024 : ℝ) := by
    rw [show (22195457934675694511/22197500000000000000 : ℝ)+2*(1574087415099/1775800000000000 : ℝ)*(287/1250 : ℝ)=(2500787610816349/2500000000000000 : ℝ) by norm_num, show 1+2*(76800135109574027/100000000000000000000 : ℝ)=(50076800135109574027/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22195457934675694511/22197500000000000000 : ℝ)*(X 1 0+X 2 0)+(1574087415099/1775800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4991/1024 : ℝ)) (lo := (2601/50000 : ℝ)) (hi := (287/1250 : ℝ)) (c := (22195457934675694511/22197500000000000000 : ℝ)) (alpha := (1574087415099/1775800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22195457934675694511/22197500000000000000 : ℝ)*(X 0 1+X 2 1)+(1574087415099/1775800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4991/1024 : ℝ)) (lo := (2601/50000 : ℝ)) (hi := (287/1250 : ℝ)) (c := (22195457934675694511/22197500000000000000 : ℝ)) (alpha := (1574087415099/1775800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22195457934675694511/22197500000000000000 : ℝ)*(X 0 2+X 1 2)+(1574087415099/1775800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4991/1024 : ℝ)) (lo := (2601/50000 : ℝ)) (hi := (287/1250 : ℝ)) (c := (22195457934675694511/22197500000000000000 : ℝ)) (alpha := (1574087415099/1775800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1558156279/10000000000 : ℝ)*X 0 0+(548271937/1000000000 : ℝ)*X 0 1+(32185423/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338929047/2500000000 : ℝ)*X 1 0+(-1730899627/10000000000 : ℝ)*X 1 1+(5149667397/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5355715609/10000000000 : ℝ)*X 2 0+(5149668053/10000000000 : ℝ)*X 2 1+(-865449767/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4160336717/10000000000 : ℝ)*X 0 0+(3735636059/10000000000 : ℝ)*X 0 1+(2308991729/5000000000 : ℝ)*X 0 2+(4160336717/10000000000 : ℝ)*X 1 0+(3735636059/10000000000 : ℝ)*X 1 1+(2308991729/5000000000 : ℝ)*X 1 2+(4160336717/10000000000 : ℝ)*X 2 0+(3735636059/10000000000 : ℝ)*X 2 1+(2308991729/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1558289957/10000000000 : ℝ)*X 0 0+(2576476137/5000000000 : ℝ)*X 0 1+(2739695131/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((329156829/625000000 : ℝ)*X 1 0+(-43786793/312500000 : ℝ)*X 1 1+(5479390259/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5266509229/10000000000 : ℝ)*X 2 0+(21917561/40000000 : ℝ)*X 2 1+(-1401177437/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2080345837/5000000000 : ℝ)*X 0 0+(460928171/1000000000 : ℝ)*X 0 1+(1872228491/5000000000 : ℝ)*X 0 2+(2080345837/5000000000 : ℝ)*X 1 0+(460928171/1000000000 : ℝ)*X 1 1+(1872228491/5000000000 : ℝ)*X 1 2+(2080345837/5000000000 : ℝ)*X 2 0+(460928171/1000000000 : ℝ)*X 2 1+(1872228491/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (45533559134958457312563/11098750000000000000000000000 : ℝ) := by norm_num
    linear_combination (341898701/20000000000000 : ℝ)*(base19) + (1203843123/100000000000000 : ℝ)*(base23) + (266202821/100000000000000 : ℝ)*(upper3) + (19392681/20000000000000 : ℝ)*(upper4) + (77529471/50000000000000 : ℝ)*(upper5) + (258495035429909/12500000000000 : ℝ)*(major0) + (258495035429909/12500000000000 : ℝ)*(major1) + (258495035429909/12500000000000 : ℝ)*(major2) + (750638257376487/25000000000000 : ℝ)*(sp0) + (150128290830757/5000000000000 : ℝ)*(sp1) + (1501283161132761/50000000000000 : ℝ)*(sp2) + (1133346320546687/100000000000000 : ℝ)*(sp3) + (7248301349/50000000000000 : ℝ)*(sp4) + (6583470389/100000000000000 : ℝ)*(sp7) + (283338226004269/25000000000000 : ℝ)*(f.failure) + (1501283763054323/50000000000000 : ℝ)*(f.sum) + (176947663477401/44395000000000000000000000000 : ℝ)*base66 + (21998856575720327/21343750000000000000000000000000 : ℝ)*base68 + (45425274740564077/21343750000000000000000000000000 : ℝ)*base70 + (218331781608532827/21343750000000000000000000000000 : ℝ)*base72 + (11916539709479/44395000000000000000000000000 : ℝ)*base73 + (273298744237185923/21343750000000000000000000000000 : ℝ)*base75 + (85730286742279673/21343750000000000000000000000000 : ℝ)*base77 + (177280893215467173/21343750000000000000000000000000 : ℝ)*base79 + (13047725920989/11098750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3470023/2500000000000000000000 : ℝ)*base90 + (3470023/2500000000000000000000 : ℝ)*base92 + (3470023/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6398110241800240876146458997/554937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (928151807/50000000000000 : ℝ)*(base19) + (1889782091/100000000000000 : ℝ)*(base23) + (256991457/100000000000000 : ℝ)*(upper3) + (16231049/50000000000000 : ℝ)*(lower4) + (36514723/12500000000000 : ℝ)*(upper5) + (1054918211560303/50000000000000 : ℝ)*(major0) + (1054918211560303/50000000000000 : ℝ)*(major1) + (1054918211560303/50000000000000 : ℝ)*(major2) + (3525700033/20000000000000 : ℝ)*(sp1) + (536500253/3125000000000 : ℝ)*(sp2) + (306336919232657/10000000000000 : ℝ)*(sp4) + (3063349707522791/100000000000000 : ℝ)*(sp5) + (47864845852131/1562500000000 : ℝ)*(sp6) + (289075817400117/25000000000000 : ℝ)*(sp7) + (289075817400117/25000000000000 : ℝ)*(f.failure) + (306336919232657/10000000000000 : ℝ)*(f.sum) + (212222834380093/44395000000000000000000000000 : ℝ)*base66 + (827385114605572359/85375000000000000000000000000000 : ℝ)*base68 + (975132396536572359/85375000000000000000000000000000 : ℝ)*base70 + (1214812580146572359/85375000000000000000000000000000 : ℝ)*base72 + (4187341221/22197500000000000000000000000 : ℝ)*base73 + (544300438939322359/85375000000000000000000000000000 : ℝ)*base76 + (1216012231740072359/85375000000000000000000000000000 : ℝ)*base78 + (1181204121626072359/85375000000000000000000000000000 : ℝ)*base80 + (101062622399917/44395000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (32480161/2500000000000000000000 : ℝ)*base89 + (32480161/2500000000000000000000 : ℝ)*base91 + (32480161/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1669_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (182463933/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (287/1250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2601/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9999/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3417/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1669_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1669_s2_0 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1565808771/10000000000 : ℝ)*x 0 + (2722274349/5000000000 : ℝ)*x 1 + (259138597/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1565808771/10000000000 : ℝ)^4995 ≤ (9707029612731/100000000000000 : ℝ)^3971 := by
    have hnat : (1565808771 : ℕ)^4995*100000000000000^3971 ≤ 9707029612731^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1565808771 10000000000 9707029612731 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2722274349/5000000000 : ℝ)^4995 ≤ (1861806264989/4000000000000 : ℝ)^3971 := by
    have hnat : (2722274349 : ℕ)^4995*4000000000000^3971 ≤ 1861806264989^3971*5000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2722274349 5000000000 1861806264989 4000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (259138597/500000000 : ℝ)^4995 ≤ (1749912549739/4000000000000 : ℝ)^3971 := by
    have hnat : (259138597 : ℕ)^4995*4000000000000^3971 ≤ 1749912549739^3971*500000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259138597 500000000 1749912549739 4000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1565808771/10000000000 : ℝ), (2722274349/5000000000 : ℝ), (259138597/500000000 : ℝ)] ![(9707029612731/100000000000000 : ℝ), (1861806264989/4000000000000 : ℝ), (1749912549739/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1565808771/10000000000 : ℝ)|^4995 ≤ (9707029612731/100000000000000 : ℝ)^3971
        have hw : |(-1565808771/10000000000 : ℝ)|=(1565808771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2722274349/5000000000 : ℝ)|^4995 ≤ (1861806264989/4000000000000 : ℝ)^3971
        have hw : |(2722274349/5000000000 : ℝ)|=(2722274349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(259138597/500000000 : ℝ)|^4995 ≤ (1749912549739/4000000000000 : ℝ)^3971
        have hw : |(259138597/500000000 : ℝ)|=(259138597/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_s2_1 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672775893/5000000000 : ℝ)*x 0 + (-1700539899/10000000000 : ℝ)*x 1 + (2591386069/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672775893/5000000000 : ℝ)^4995 ≤ (4548310437137/10000000000000 : ℝ)^3971 := by
    have hnat : (2672775893 : ℕ)^4995*10000000000000^3971 ≤ 4548310437137^3971*5000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672775893 5000000000 4548310437137 10000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1700539899/10000000000 : ℝ)^4995 ≤ (2692269941859/25000000000000 : ℝ)^3971 := by
    have hnat : (1700539899 : ℕ)^4995*25000000000000^3971 ≤ 2692269941859^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1700539899 10000000000 2692269941859 25000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2591386069/5000000000 : ℝ)^4995 ≤ (43747815845777/100000000000000 : ℝ)^3971 := by
    have hnat : (2591386069 : ℕ)^4995*100000000000000^3971 ≤ 43747815845777^3971*5000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591386069 5000000000 43747815845777 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672775893/5000000000 : ℝ), (-1700539899/10000000000 : ℝ), (2591386069/5000000000 : ℝ)] ![(4548310437137/10000000000000 : ℝ), (2692269941859/25000000000000 : ℝ), (43747815845777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672775893/5000000000 : ℝ)|^4995 ≤ (4548310437137/10000000000000 : ℝ)^3971
        have hw : |(2672775893/5000000000 : ℝ)|=(2672775893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1700539899/10000000000 : ℝ)|^4995 ≤ (2692269941859/25000000000000 : ℝ)^3971
        have hw : |(-1700539899/10000000000 : ℝ)|=(1700539899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2591386069/5000000000 : ℝ)|^4995 ≤ (43747815845777/100000000000000 : ℝ)^3971
        have hw : |(2591386069/5000000000 : ℝ)|=(2591386069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_s2_2 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345551747/10000000000 : ℝ)*x 0 + (80980813/156250000 : ℝ)*x 1 + (-425135023/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345551747/10000000000 : ℝ)^4995 ≤ (9096620790793/20000000000000 : ℝ)^3971 := by
    have hnat : (5345551747 : ℕ)^4995*20000000000000^3971 ≤ 9096620790793^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345551747 10000000000 9096620790793 20000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (80980813/156250000 : ℝ)^4995 ≤ (21873907360151/50000000000000 : ℝ)^3971 := by
    have hnat : (80980813 : ℕ)^4995*50000000000000^3971 ≤ 21873907360151^3971*156250000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80980813 156250000 21873907360151 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (425135023/2500000000 : ℝ)^4995 ≤ (10769081304829/100000000000000 : ℝ)^3971 := by
    have hnat : (425135023 : ℕ)^4995*100000000000000^3971 ≤ 10769081304829^3971*2500000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425135023 2500000000 10769081304829 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345551747/10000000000 : ℝ), (80980813/156250000 : ℝ), (-425135023/2500000000 : ℝ)] ![(9096620790793/20000000000000 : ℝ), (21873907360151/50000000000000 : ℝ), (10769081304829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345551747/10000000000 : ℝ)|^4995 ≤ (9096620790793/20000000000000 : ℝ)^3971
        have hw : |(5345551747/10000000000 : ℝ)|=(5345551747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(80980813/156250000 : ℝ)|^4995 ≤ (21873907360151/50000000000000 : ℝ)^3971
        have hw : |(80980813/156250000 : ℝ)|=(80980813/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-425135023/2500000000 : ℝ)|^4995 ≤ (10769081304829/100000000000000 : ℝ)^3971
        have hw : |(-425135023/2500000000 : ℝ)|=(425135023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_s2_3 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4166066657/10000000000 : ℝ)*x 0 + (957372037/2500000000 : ℝ)*x 1 + (4523007303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4166066657/10000000000 : ℝ)^4995 ≤ (4155039873201/12500000000000 : ℝ)^3971 := by
    have hnat : (4166066657 : ℕ)^4995*12500000000000^3971 ≤ 4155039873201^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4166066657 10000000000 4155039873201 12500000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (957372037/2500000000 : ℝ)^4995 ≤ (14949112833049/50000000000000 : ℝ)^3971 := by
    have hnat : (957372037 : ℕ)^4995*50000000000000^3971 ≤ 14949112833049^3971*2500000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      957372037 2500000000 14949112833049 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4523007303/10000000000 : ℝ)^4995 ≤ (18430727662091/50000000000000 : ℝ)^3971 := by
    have hnat : (4523007303 : ℕ)^4995*50000000000000^3971 ≤ 18430727662091^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4523007303 10000000000 18430727662091 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4166066657/10000000000 : ℝ), (957372037/2500000000 : ℝ), (4523007303/10000000000 : ℝ)] ![(4155039873201/12500000000000 : ℝ), (14949112833049/50000000000000 : ℝ), (18430727662091/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4166066657/10000000000 : ℝ)|^4995 ≤ (4155039873201/12500000000000 : ℝ)^3971
        have hw : |(4166066657/10000000000 : ℝ)|=(4166066657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(957372037/2500000000 : ℝ)|^4995 ≤ (14949112833049/50000000000000 : ℝ)^3971
        have hw : |(957372037/2500000000 : ℝ)|=(957372037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4523007303/10000000000 : ℝ)|^4995 ≤ (18430727662091/50000000000000 : ℝ)^3971
        have hw : |(4523007303/10000000000 : ℝ)|=(4523007303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_s2_4 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1565873931/10000000000 : ℝ)*x 0 + (5184806219/10000000000 : ℝ)*x 1 + (5442492651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1565873931/10000000000 : ℝ)^4995 ≤ (4853768866573/50000000000000 : ℝ)^3971 := by
    have hnat : (1565873931 : ℕ)^4995*50000000000000^3971 ≤ 4853768866573^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1565873931 10000000000 4853768866573 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184806219/10000000000 : ℝ)^4995 ≤ (43769414171303/100000000000000 : ℝ)^3971 := by
    have hnat : (5184806219 : ℕ)^4995*100000000000000^3971 ≤ 43769414171303^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184806219 10000000000 43769414171303 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5442492651/10000000000 : ℝ)^4995 ≤ (11630762020659/25000000000000 : ℝ)^3971 := by
    have hnat : (5442492651 : ℕ)^4995*25000000000000^3971 ≤ 11630762020659^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442492651 10000000000 11630762020659 25000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1565873931/10000000000 : ℝ), (5184806219/10000000000 : ℝ), (5442492651/10000000000 : ℝ)] ![(4853768866573/50000000000000 : ℝ), (43769414171303/100000000000000 : ℝ), (11630762020659/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1565873931/10000000000 : ℝ)|^4995 ≤ (4853768866573/50000000000000 : ℝ)^3971
        have hw : |(-1565873931/10000000000 : ℝ)|=(1565873931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184806219/10000000000 : ℝ)|^4995 ≤ (43769414171303/100000000000000 : ℝ)^3971
        have hw : |(5184806219/10000000000 : ℝ)|=(5184806219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5442492651/10000000000 : ℝ)|^4995 ≤ (11630762020659/25000000000000 : ℝ)^3971
        have hw : |(5442492651/10000000000 : ℝ)|=(5442492651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_s2_5 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (659434219/1250000000 : ℝ)*x 0 + (-720409651/5000000000 : ℝ)*x 1 + (5442492753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (659434219/1250000000 : ℝ)^4995 ≤ (44734352410609/100000000000000 : ℝ)^3971 := by
    have hnat : (659434219 : ℕ)^4995*100000000000000^3971 ≤ 44734352410609^3971*1250000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659434219 1250000000 44734352410609 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (720409651/5000000000 : ℝ)^4995 ≤ (4371299202161/50000000000000 : ℝ)^3971 := by
    have hnat : (720409651 : ℕ)^4995*50000000000000^3971 ≤ 4371299202161^3971*5000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      720409651 5000000000 4371299202161 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5442492753/10000000000 : ℝ)^4995 ≤ (23261524589691/50000000000000 : ℝ)^3971 := by
    have hnat : (5442492753 : ℕ)^4995*50000000000000^3971 ≤ 23261524589691^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442492753 10000000000 23261524589691 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(659434219/1250000000 : ℝ), (-720409651/5000000000 : ℝ), (5442492753/10000000000 : ℝ)] ![(44734352410609/100000000000000 : ℝ), (4371299202161/50000000000000 : ℝ), (23261524589691/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(659434219/1250000000 : ℝ)|^4995 ≤ (44734352410609/100000000000000 : ℝ)^3971
        have hw : |(659434219/1250000000 : ℝ)|=(659434219/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-720409651/5000000000 : ℝ)|^4995 ≤ (4371299202161/50000000000000 : ℝ)^3971
        have hw : |(-720409651/5000000000 : ℝ)|=(720409651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5442492753/10000000000 : ℝ)|^4995 ≤ (23261524589691/50000000000000 : ℝ)^3971
        have hw : |(5442492753/10000000000 : ℝ)|=(5442492753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_s2_6 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (659434231/1250000000 : ℝ)*x 0 + (5442492603/10000000000 : ℝ)*x 1 + (-720409689/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (659434231/1250000000 : ℝ)^4995 ≤ (44734353434577/100000000000000 : ℝ)^3971 := by
    have hnat : (659434231 : ℕ)^4995*100000000000000^3971 ≤ 44734353434577^3971*1250000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659434231 1250000000 44734353434577 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5442492603/10000000000 : ℝ)^4995 ≤ (46523047566521/100000000000000 : ℝ)^3971 := by
    have hnat : (5442492603 : ℕ)^4995*100000000000000^3971 ≤ 46523047566521^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442492603 10000000000 46523047566521 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (720409689/5000000000 : ℝ)^4995 ≤ (8742598984391/100000000000000 : ℝ)^3971 := by
    have hnat : (720409689 : ℕ)^4995*100000000000000^3971 ≤ 8742598984391^3971*5000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      720409689 5000000000 8742598984391 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(659434231/1250000000 : ℝ), (5442492603/10000000000 : ℝ), (-720409689/5000000000 : ℝ)] ![(44734353434577/100000000000000 : ℝ), (46523047566521/100000000000000 : ℝ), (8742598984391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(659434231/1250000000 : ℝ)|^4995 ≤ (44734353434577/100000000000000 : ℝ)^3971
        have hw : |(659434231/1250000000 : ℝ)|=(659434231/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5442492603/10000000000 : ℝ)|^4995 ≤ (46523047566521/100000000000000 : ℝ)^3971
        have hw : |(5442492603/10000000000 : ℝ)|=(5442492603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-720409689/5000000000 : ℝ)|^4995 ≤ (8742598984391/100000000000000 : ℝ)^3971
        have hw : |(-720409689/5000000000 : ℝ)|=(720409689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_s2_7 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4166239507/10000000000 : ℝ)*x 0 + (1129404589/2500000000 : ℝ)*x 1 + (3834934923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4166239507/10000000000 : ℝ)^4995 ≤ (6648410754619/20000000000000 : ℝ)^3971 := by
    have hnat : (4166239507 : ℕ)^4995*20000000000000^3971 ≤ 6648410754619^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4166239507 10000000000 6648410754619 20000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1129404589/2500000000 : ℝ)^4995 ≤ (36806219865411/100000000000000 : ℝ)^3971 := by
    have hnat : (1129404589 : ℕ)^4995*100000000000000^3971 ≤ 36806219865411^3971*2500000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129404589 2500000000 36806219865411 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3834934923/10000000000 : ℝ)^4995 ≤ (14975863175109/50000000000000 : ℝ)^3971 := by
    have hnat : (3834934923 : ℕ)^4995*50000000000000^3971 ≤ 14975863175109^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3834934923 10000000000 14975863175109 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4166239507/10000000000 : ℝ), (1129404589/2500000000 : ℝ), (3834934923/10000000000 : ℝ)] ![(6648410754619/20000000000000 : ℝ), (36806219865411/100000000000000 : ℝ), (14975863175109/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4166239507/10000000000 : ℝ)|^4995 ≤ (6648410754619/20000000000000 : ℝ)^3971
        have hw : |(4166239507/10000000000 : ℝ)|=(4166239507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1129404589/2500000000 : ℝ)|^4995 ≤ (36806219865411/100000000000000 : ℝ)^3971
        have hw : |(1129404589/2500000000 : ℝ)|=(1129404589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3834934923/10000000000 : ℝ)|^4995 ≤ (14975863175109/50000000000000 : ℝ)^3971
        have hw : |(3834934923/10000000000 : ℝ)|=(3834934923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1669_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (182463933/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3417/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9999/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5357/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8143/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3417/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9999/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3417/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9999/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3417/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9999/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3417/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9999/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3417/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9999/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3417/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9999/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9999/100000 : ℝ) ^ (4991/1024 : ℝ) ≤ (667936044098697/50000000000000000000 : ℝ) := by
    have hpowers : (9999/100000 : ℝ)^4991 ≤ (667936044098697/50000000000000000000 : ℝ)^1024 := by
      have hnat : (9999 : ℕ)^4991*50000000000000000000^1024 ≤ 667936044098697^1024*100000^4991 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9999 100000 667936044098697 50000000000000000000 4991 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9999/100000 : ℝ)) (X := (667936044098697/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4991 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3417/20000 : ℝ) ^ (4991/1024 : ℝ) ≤ (3637285890118139/20000000000000000000 : ℝ) := by
    have hpowers : (3417/20000 : ℝ)^4991 ≤ (3637285890118139/20000000000000000000 : ℝ)^1024 := by
      have hnat : (3417 : ℕ)^4991*20000000000000000000^1024 ≤ 3637285890118139^1024*20000^4991 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3417 20000 3637285890118139 20000000000000000000 4991 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3417/20000 : ℝ)) (X := (3637285890118139/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4991 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000667936044098697/25000000000000000000 : ℝ) ≤ (2500013703851873/2500000000000000 : ℝ) ^ (4991/1024 : ℝ) := by
    have hpowers : (25000667936044098697/25000000000000000000 : ℝ)^1024 ≤ (2500013703851873/2500000000000000 : ℝ)^4991 := by
      have hnat : (25000667936044098697 : ℕ)^1024*2500000000000000^4991 ≤ 2500013703851873^4991*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000667936044098697 25000000000000000000 2500013703851873 2500000000000000 1024 4991 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500013703851873/2500000000000000 : ℝ)) (X := (25000667936044098697/25000000000000000000 : ℝ)) (by norm_num) 4991 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100019522301538788089/100000000000000000000 : ℝ) ≤ (10000400506631443/10000000000000000 : ℝ) ^ (4991/1024 : ℝ) := by
    have hpowers : (100019522301538788089/100000000000000000000 : ℝ)^1024 ≤ (10000400506631443/10000000000000000 : ℝ)^4991 := by
      have hnat : (100019522301538788089 : ℕ)^1024*10000000000000000^4991 ≤ 10000400506631443^4991*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100019522301538788089 100000000000000000000 10000400506631443 10000000000000000 1024 4991 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000400506631443/10000000000000000 : ℝ)) (X := (100019522301538788089/100000000000000000000 : ℝ)) (by norm_num) 4991 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10003637285890118139/10000000000000000000 : ℝ) ≤ (5000373098927697/5000000000000000 : ℝ) ^ (4991/1024 : ℝ) := by
    have hpowers : (10003637285890118139/10000000000000000000 : ℝ)^1024 ≤ (5000373098927697/5000000000000000 : ℝ)^4991 := by
      have hnat : (10003637285890118139 : ℕ)^1024*5000000000000000^4991 ≤ 5000373098927697^4991*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003637285890118139 10000000000000000000 5000373098927697 5000000000000000 1024 4991 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000373098927697/5000000000000000 : ℝ)) (X := (10003637285890118139/10000000000000000000 : ℝ)) (by norm_num) 4991 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(667936044098697/50000000000000000000 : ℝ) ≤ ((11808912548146819369/11810000000000000000 : ℝ)+2*(345691223951/708600000000000 : ℝ)*(9999/100000 : ℝ))^(4991/1024 : ℝ) := by
    rw [show (11808912548146819369/11810000000000000000 : ℝ)+2*(345691223951/708600000000000 : ℝ)*(9999/100000 : ℝ)=(2500013703851873/2500000000000000 : ℝ) by norm_num, show 1+2*(667936044098697/50000000000000000000 : ℝ)=(25000667936044098697/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3637285890118139/20000000000000000000 : ℝ)+(667936044098697/50000000000000000000 : ℝ) ≤ ((11808912548146819369/11810000000000000000 : ℝ)+(345691223951/708600000000000 : ℝ)*((3417/20000 : ℝ)+(9999/100000 : ℝ)))^(4991/1024 : ℝ) := by
    rw [show (11808912548146819369/11810000000000000000 : ℝ)+(345691223951/708600000000000 : ℝ)*((3417/20000 : ℝ)+(9999/100000 : ℝ))=(10000400506631443/10000000000000000 : ℝ) by norm_num, show 1+(3637285890118139/20000000000000000000 : ℝ)+(667936044098697/50000000000000000000 : ℝ)=(100019522301538788089/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3637285890118139/20000000000000000000 : ℝ) ≤ ((11808912548146819369/11810000000000000000 : ℝ)+2*(345691223951/708600000000000 : ℝ)*(3417/20000 : ℝ))^(4991/1024 : ℝ) := by
    rw [show (11808912548146819369/11810000000000000000 : ℝ)+2*(345691223951/708600000000000 : ℝ)*(3417/20000 : ℝ)=(5000373098927697/5000000000000000 : ℝ) by norm_num, show 1+2*(3637285890118139/20000000000000000000 : ℝ)=(10003637285890118139/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11808912548146819369/11810000000000000000 : ℝ)*(X 1 0+X 2 0)+(345691223951/708600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4991/1024 : ℝ)) (lo := (9999/100000 : ℝ)) (hi := (3417/20000 : ℝ)) (c := (11808912548146819369/11810000000000000000 : ℝ)) (alpha := (345691223951/708600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11808912548146819369/11810000000000000000 : ℝ)*(X 0 1+X 2 1)+(345691223951/708600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4991/1024 : ℝ)) (lo := (9999/100000 : ℝ)) (hi := (3417/20000 : ℝ)) (c := (11808912548146819369/11810000000000000000 : ℝ)) (alpha := (345691223951/708600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11808912548146819369/11810000000000000000 : ℝ)*(X 0 2+X 1 2)+(345691223951/708600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4991/1024 : ℝ)) (lo := (9999/100000 : ℝ)) (hi := (3417/20000 : ℝ)) (c := (11808912548146819369/11810000000000000000 : ℝ)) (alpha := (345691223951/708600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1565808771/10000000000 : ℝ)*X 0 0+(2722274349/5000000000 : ℝ)*X 0 1+(259138597/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672775893/5000000000 : ℝ)*X 1 0+(-1700539899/10000000000 : ℝ)*X 1 1+(2591386069/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345551747/10000000000 : ℝ)*X 2 0+(80980813/156250000 : ℝ)*X 2 1+(-425135023/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4166066657/10000000000 : ℝ)*X 0 0+(957372037/2500000000 : ℝ)*X 0 1+(4523007303/10000000000 : ℝ)*X 0 2+(4166066657/10000000000 : ℝ)*X 1 0+(957372037/2500000000 : ℝ)*X 1 1+(4523007303/10000000000 : ℝ)*X 1 2+(4166066657/10000000000 : ℝ)*X 2 0+(957372037/2500000000 : ℝ)*X 2 1+(4523007303/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1565873931/10000000000 : ℝ)*X 0 0+(5184806219/10000000000 : ℝ)*X 0 1+(5442492651/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((659434219/1250000000 : ℝ)*X 1 0+(-720409651/5000000000 : ℝ)*X 1 1+(5442492753/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((659434231/1250000000 : ℝ)*X 2 0+(5442492603/10000000000 : ℝ)*X 2 1+(-720409689/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4166239507/10000000000 : ℝ)*X 0 0+(1129404589/2500000000 : ℝ)*X 0 1+(3834934923/10000000000 : ℝ)*X 0 2+(4166239507/10000000000 : ℝ)*X 1 0+(1129404589/2500000000 : ℝ)*X 1 1+(3834934923/10000000000 : ℝ)*X 1 2+(4166239507/10000000000 : ℝ)*X 2 0+(1129404589/2500000000 : ℝ)*X 2 1+(3834934923/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2156213498348154943691405009/295250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1148951427/100000000000000 : ℝ)*(base19) + (1089757607/100000000000000 : ℝ)*(base23) + (334881/2000000000000 : ℝ)*(lower2) + (131614701/50000000000000 : ℝ)*(upper3) + (20240411/25000000000000 : ℝ)*(upper5) + (1315503499627187/50000000000000 : ℝ)*(major0) + (1315503499627187/50000000000000 : ℝ)*(major1) + (1315503499627187/50000000000000 : ℝ)*(major2) + (3820067031251579/100000000000000 : ℝ)*(sp0) + (3820079969905437/100000000000000 : ℝ)*(sp1) + (1910040014549629/50000000000000 : ℝ)*(sp2) + (360481544434417/25000000000000 : ℝ)*(sp3) + (2817521057/20000000000000 : ℝ)*(sp4) + (6458480567/100000000000000 : ℝ)*(sp7) + (288386527243647/20000000000000 : ℝ)*(f.failure) + (119377534964277/3125000000000 : ℝ)*(f.sum) + (16326389377939/8857500000000000000000000000 : ℝ)*base66 + (9158166996164105009/1771500000000000000000000000000000 : ℝ)*base67 + (6981396010826394991/1771500000000000000000000000000000 : ℝ)*base70 + (16500062732753105009/1771500000000000000000000000000000 : ℝ)*base71 + (9792603590029/8857500000000000000000000000 : ℝ)*base74 + (19125312856062894991/1771500000000000000000000000000000 : ℝ)*base76 + (9065947573992894991/1771500000000000000000000000000000 : ℝ)*base78 + (5499561827114394991/1771500000000000000000000000000000 : ℝ)*base80 + (26433748244299/8857500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (883651/2000000000000000000000 : ℝ)*base89 + (883651/2000000000000000000000 : ℝ)*base91 + (883651/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (329129006710628644069829691/29525000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (803312659/50000000000000 : ℝ)*(base19) + (228146881/12500000000000 : ℝ)*(base23) + (63805381/25000000000000 : ℝ)*(upper3) + (69118459/100000000000000 : ℝ)*(lower4) + (109725703/50000000000000 : ℝ)*(upper5) + (133637300065029/5000000000000 : ℝ)*(major0) + (133637300065029/5000000000000 : ℝ)*(major1) + (133637300065029/5000000000000 : ℝ)*(major2) + (2486239411/12500000000000 : ℝ)*(sp1) + (4232631071/20000000000000 : ℝ)*(sp2) + (3880683787980333/100000000000000 : ℝ)*(sp4) + (1940331145719863/50000000000000 : ℝ)*(sp5) + (388066079964993/10000000000000 : ℝ)*(sp6) + (183100980379817/12500000000000 : ℝ)*(sp7) + (183100980379817/12500000000000 : ℝ)*(f.failure) + (3880683787980333/100000000000000 : ℝ)*(f.sum) + (4572819456563/1181000000000000000000000000 : ℝ)*base66 + (508671448652246701/59050000000000000000000000000000 : ℝ)*base67 + (665374336951846701/59050000000000000000000000000000 : ℝ)*base69 + (373815401224796701/59050000000000000000000000000000 : ℝ)*base71 + (197962941313/590500000000000000000000000 : ℝ)*base74 + (663430491318896701/59050000000000000000000000000000 : ℝ)*base75 + (181164214954546701/59050000000000000000000000000000 : ℝ)*base77 + (284788793084096701/59050000000000000000000000000000 : ℝ)*base79 + (100619323409/590500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (6359739/1250000000000000000000 : ℝ)*base90 + (6359739/1250000000000000000000 : ℝ)*base92 + (6359739/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1669_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (182463933/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3417/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9999/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5357/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8143/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1669_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1669_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (182463933/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5357/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8143/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1669_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1669_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1669_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (182463933/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5357/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8143/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1669_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

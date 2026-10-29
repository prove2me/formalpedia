-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1448_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:58:52.536834+00:00
-- url     : https://prove2.me/submissions/8456733f-eae9-4b0b-abf1-680da3f88ab6

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
theorem support_rectangle_w1448_s3_0 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-488717989/2500000000 : ℝ)*x 0 + (1083081251/2000000000 : ℝ)*x 1 + (523977247/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (488717989/2500000000 : ℝ)^551 ≤ (1192917428803/10000000000000 : ℝ)^423 := by
    have hnat : (488717989 : ℕ)^551*10000000000000^423 ≤ 1192917428803^423*2500000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      488717989 2500000000 1192917428803 10000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083081251/2000000000 : ℝ)^551 ≤ (44980851210171/100000000000000 : ℝ)^423 := by
    have hnat : (1083081251 : ℕ)^551*100000000000000^423 ≤ 44980851210171^423*2000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083081251 2000000000 44980851210171 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (523977247/1000000000 : ℝ)^551 ≤ (43089974489231/100000000000000 : ℝ)^423 := by
    have hnat : (523977247 : ℕ)^551*100000000000000^423 ≤ 43089974489231^423*1000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523977247 1000000000 43089974489231 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-488717989/2500000000 : ℝ), (1083081251/2000000000 : ℝ), (523977247/1000000000 : ℝ)] ![(1192917428803/10000000000000 : ℝ), (44980851210171/100000000000000 : ℝ), (43089974489231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-488717989/2500000000 : ℝ)|^551 ≤ (1192917428803/10000000000000 : ℝ)^423
        have hw : |(-488717989/2500000000 : ℝ)|=(488717989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083081251/2000000000 : ℝ)|^551 ≤ (44980851210171/100000000000000 : ℝ)^423
        have hw : |(1083081251/2000000000 : ℝ)|=(1083081251/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(523977247/1000000000 : ℝ)|^551 ≤ (43089974489231/100000000000000 : ℝ)^423
        have hw : |(523977247/1000000000 : ℝ)|=(523977247/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s3_1 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2674517171/5000000000 : ℝ)*x 0 + (-2044431469/10000000000 : ℝ)*x 1 + (5239772477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674517171/5000000000 : ℝ)^551 ≤ (44264074642007/100000000000000 : ℝ)^423 := by
    have hnat : (2674517171 : ℕ)^551*100000000000000^423 ≤ 44264074642007^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674517171 5000000000 44264074642007 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2044431469/10000000000 : ℝ)^551 ≤ (12645950778253/100000000000000 : ℝ)^423 := by
    have hnat : (2044431469 : ℕ)^551*100000000000000^423 ≤ 12645950778253^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2044431469 10000000000 12645950778253 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5239772477/10000000000 : ℝ)^551 ≤ (5386246820527/12500000000000 : ℝ)^423 := by
    have hnat : (5239772477 : ℕ)^551*12500000000000^423 ≤ 5386246820527^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239772477 10000000000 5386246820527 12500000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674517171/5000000000 : ℝ), (-2044431469/10000000000 : ℝ), (5239772477/10000000000 : ℝ)] ![(44264074642007/100000000000000 : ℝ), (12645950778253/100000000000000 : ℝ), (5386246820527/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674517171/5000000000 : ℝ)|^551 ≤ (44264074642007/100000000000000 : ℝ)^423
        have hw : |(2674517171/5000000000 : ℝ)|=(2674517171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2044431469/10000000000 : ℝ)|^551 ≤ (12645950778253/100000000000000 : ℝ)^423
        have hw : |(-2044431469/10000000000 : ℝ)|=(2044431469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5239772477/10000000000 : ℝ)|^551 ≤ (5386246820527/12500000000000 : ℝ)^423
        have hw : |(5239772477/10000000000 : ℝ)|=(5239772477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s3_2 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (668629323/1250000000 : ℝ)*x 0 + (2619886173/5000000000 : ℝ)*x 1 + (-2044431319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668629323/1250000000 : ℝ)^551 ≤ (44264077250577/100000000000000 : ℝ)^423 := by
    have hnat : (668629323 : ℕ)^551*100000000000000^423 ≤ 44264077250577^423*1250000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668629323 1250000000 44264077250577 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2619886173/5000000000 : ℝ)^551 ≤ (43089973160929/100000000000000 : ℝ)^423 := by
    have hnat : (2619886173 : ℕ)^551*100000000000000^423 ≤ 43089973160929^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619886173 5000000000 43089973160929 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2044431319/10000000000 : ℝ)^551 ≤ (1580743696207/12500000000000 : ℝ)^423 := by
    have hnat : (2044431319 : ℕ)^551*12500000000000^423 ≤ 1580743696207^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2044431319 10000000000 1580743696207 12500000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668629323/1250000000 : ℝ), (2619886173/5000000000 : ℝ), (-2044431319/10000000000 : ℝ)] ![(44264077250577/100000000000000 : ℝ), (43089973160929/100000000000000 : ℝ), (1580743696207/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668629323/1250000000 : ℝ)|^551 ≤ (44264077250577/100000000000000 : ℝ)^423
        have hw : |(668629323/1250000000 : ℝ)|=(668629323/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2619886173/5000000000 : ℝ)|^551 ≤ (43089973160929/100000000000000 : ℝ)^423
        have hw : |(2619886173/5000000000 : ℝ)|=(2619886173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2044431319/10000000000 : ℝ)|^551 ≤ (1580743696207/12500000000000 : ℝ)^423
        have hw : |(-2044431319/10000000000 : ℝ)|=(2044431319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s3_3 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4299066359/10000000000 : ℝ)*x 0 + (2055780731/5000000000 : ℝ)*x 1 + (4494162977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4299066359/10000000000 : ℝ)^551 ≤ (6659827624773/20000000000000 : ℝ)^423 := by
    have hnat : (4299066359 : ℕ)^551*20000000000000^423 ≤ 6659827624773^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4299066359 10000000000 6659827624773 20000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2055780731/5000000000 : ℝ)^551 ≤ (31419918767663/100000000000000 : ℝ)^423 := by
    have hnat : (2055780731 : ℕ)^551*100000000000000^423 ≤ 31419918767663^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2055780731 5000000000 31419918767663 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4494162977/10000000000 : ℝ)^551 ≤ (4410117886339/12500000000000 : ℝ)^423 := by
    have hnat : (4494162977 : ℕ)^551*12500000000000^423 ≤ 4410117886339^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4494162977 10000000000 4410117886339 12500000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4299066359/10000000000 : ℝ), (2055780731/5000000000 : ℝ), (4494162977/10000000000 : ℝ)] ![(6659827624773/20000000000000 : ℝ), (31419918767663/100000000000000 : ℝ), (4410117886339/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4299066359/10000000000 : ℝ)|^551 ≤ (6659827624773/20000000000000 : ℝ)^423
        have hw : |(4299066359/10000000000 : ℝ)|=(4299066359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2055780731/5000000000 : ℝ)|^551 ≤ (31419918767663/100000000000000 : ℝ)^423
        have hw : |(2055780731/5000000000 : ℝ)|=(2055780731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4494162977/10000000000 : ℝ)|^551 ≤ (4410117886339/12500000000000 : ℝ)^423
        have hw : |(4494162977/10000000000 : ℝ)|=(4494162977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s3_4 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1954886257/10000000000 : ℝ)*x 0 + (2620234519/5000000000 : ℝ)*x 1 + (1353676517/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1954886257/10000000000 : ℝ)^551 ≤ (11929287964397/100000000000000 : ℝ)^423 := by
    have hnat : (1954886257 : ℕ)^551*100000000000000^423 ≤ 11929287964397^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1954886257 10000000000 11929287964397 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620234519/5000000000 : ℝ)^551 ≤ (21548718176311/50000000000000 : ℝ)^423 := by
    have hnat : (2620234519 : ℕ)^551*50000000000000^423 ≤ 21548718176311^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620234519 5000000000 21548718176311 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353676517/2500000000 : ℝ)^551 ≤ (44973275673481/100000000000000 : ℝ)^423 := by
    have hnat : (1353676517 : ℕ)^551*100000000000000^423 ≤ 44973275673481^423*2500000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353676517 2500000000 44973275673481 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1954886257/10000000000 : ℝ), (2620234519/5000000000 : ℝ), (1353676517/2500000000 : ℝ)] ![(11929287964397/100000000000000 : ℝ), (21548718176311/50000000000000 : ℝ), (44973275673481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1954886257/10000000000 : ℝ)|^551 ≤ (11929287964397/100000000000000 : ℝ)^423
        have hw : |(-1954886257/10000000000 : ℝ)|=(1954886257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620234519/5000000000 : ℝ)|^551 ≤ (21548718176311/50000000000000 : ℝ)^423
        have hw : |(2620234519/5000000000 : ℝ)|=(2620234519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353676517/2500000000 : ℝ)|^551 ≤ (44973275673481/100000000000000 : ℝ)^423
        have hw : |(1353676517/2500000000 : ℝ)|=(1353676517/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s3_5 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2651645773/5000000000 : ℝ)*x 0 + (-1869498107/10000000000 : ℝ)*x 1 + (1353676507/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651645773/5000000000 : ℝ)^551 ≤ (21885821166509/50000000000000 : ℝ)^423 := by
    have hnat : (2651645773 : ℕ)^551*50000000000000^423 ≤ 21885821166509^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651645773 5000000000 21885821166509 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1869498107/10000000000 : ℝ)^551 ≤ (225101648269/2000000000000 : ℝ)^423 := by
    have hnat : (1869498107 : ℕ)^551*2000000000000^423 ≤ 225101648269^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1869498107 10000000000 225101648269 2000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353676507/2500000000 : ℝ)^551 ≤ (44973275240717/100000000000000 : ℝ)^423 := by
    have hnat : (1353676507 : ℕ)^551*100000000000000^423 ≤ 44973275240717^423*2500000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353676507 2500000000 44973275240717 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651645773/5000000000 : ℝ), (-1869498107/10000000000 : ℝ), (1353676507/2500000000 : ℝ)] ![(21885821166509/50000000000000 : ℝ), (225101648269/2000000000000 : ℝ), (44973275240717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651645773/5000000000 : ℝ)|^551 ≤ (21885821166509/50000000000000 : ℝ)^423
        have hw : |(2651645773/5000000000 : ℝ)|=(2651645773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1869498107/10000000000 : ℝ)|^551 ≤ (225101648269/2000000000000 : ℝ)^423
        have hw : |(-1869498107/10000000000 : ℝ)|=(1869498107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353676507/2500000000 : ℝ)|^551 ≤ (44973275240717/100000000000000 : ℝ)^423
        have hw : |(1353676507/2500000000 : ℝ)|=(1353676507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s3_6 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1325822591/2500000000 : ℝ)*x 0 + (5414706969/10000000000 : ℝ)*x 1 + (-1869498429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325822591/2500000000 : ℝ)^551 ≤ (43771629625053/100000000000000 : ℝ)^423 := by
    have hnat : (1325822591 : ℕ)^551*100000000000000^423 ≤ 43771629625053^423*2500000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325822591 2500000000 43771629625053 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414706969/10000000000 : ℝ)^551 ≤ (11243321355371/25000000000000 : ℝ)^423 := by
    have hnat : (5414706969 : ℕ)^551*25000000000000^423 ≤ 11243321355371^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414706969 10000000000 11243321355371 25000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1869498429/10000000000 : ℝ)^551 ≤ (11255084938621/100000000000000 : ℝ)^423 := by
    have hnat : (1869498429 : ℕ)^551*100000000000000^423 ≤ 11255084938621^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1869498429 10000000000 11255084938621 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325822591/2500000000 : ℝ), (5414706969/10000000000 : ℝ), (-1869498429/10000000000 : ℝ)] ![(43771629625053/100000000000000 : ℝ), (11243321355371/25000000000000 : ℝ), (11255084938621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325822591/2500000000 : ℝ)|^551 ≤ (43771629625053/100000000000000 : ℝ)^423
        have hw : |(1325822591/2500000000 : ℝ)|=(1325822591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414706969/10000000000 : ℝ)|^551 ≤ (11243321355371/25000000000000 : ℝ)^423
        have hw : |(5414706969/10000000000 : ℝ)|=(5414706969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1869498429/10000000000 : ℝ)|^551 ≤ (11255084938621/100000000000000 : ℝ)^423
        have hw : |(-1869498429/10000000000 : ℝ)|=(1869498429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s3_7 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (859819501/2000000000 : ℝ)*x 0 + (280790393/625000000 : ℝ)*x 1 + (4113087807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (859819501/2000000000 : ℝ)^551 ≤ (4162431546511/12500000000000 : ℝ)^423 := by
    have hnat : (859819501 : ℕ)^551*12500000000000^423 ≤ 4162431546511^423*2000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859819501 2000000000 4162431546511 12500000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (280790393/625000000 : ℝ)^551 ≤ (35265434334873/100000000000000 : ℝ)^423 := by
    have hnat : (280790393 : ℕ)^551*100000000000000^423 ≤ 35265434334873^423*625000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280790393 625000000 35265434334873 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4113087807/10000000000 : ℝ)^551 ≤ (49117364491/156250000000 : ℝ)^423 := by
    have hnat : (4113087807 : ℕ)^551*156250000000^423 ≤ 49117364491^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4113087807 10000000000 49117364491 156250000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(859819501/2000000000 : ℝ), (280790393/625000000 : ℝ), (4113087807/10000000000 : ℝ)] ![(4162431546511/12500000000000 : ℝ), (35265434334873/100000000000000 : ℝ), (49117364491/156250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(859819501/2000000000 : ℝ)|^551 ≤ (4162431546511/12500000000000 : ℝ)^423
        have hw : |(859819501/2000000000 : ℝ)|=(859819501/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(280790393/625000000 : ℝ)|^551 ≤ (35265434334873/100000000000000 : ℝ)^423
        have hw : |(280790393/625000000 : ℝ)|=(280790393/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4113087807/10000000000 : ℝ)|^551 ≤ (49117364491/156250000000 : ℝ)^423
        have hw : |(4113087807/10000000000 : ℝ)|=(4113087807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1448_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79460081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15743/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10467/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11217/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14937/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15743/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10467/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15743/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10467/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15743/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10467/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15743/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10467/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15743/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10467/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15743/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10467/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (10467/100000 : ℝ) ^ (4407/1024 : ℝ) ≤ (604781065015963/10000000000000000000 : ℝ) := by
    have hpowers : (10467/100000 : ℝ)^4407 ≤ (604781065015963/10000000000000000000 : ℝ)^1024 := by
      have hnat : (10467 : ℕ)^4407*10000000000000000000^1024 ≤ 604781065015963^1024*100000^4407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10467 100000 604781065015963 10000000000000000000 4407 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10467/100000 : ℝ)) (X := (604781065015963/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15743/100000 : ℝ) ^ (4407/1024 : ℝ) ≤ (218966002402271/625000000000000000 : ℝ) := by
    have hpowers : (15743/100000 : ℝ)^4407 ≤ (218966002402271/625000000000000000 : ℝ)^1024 := by
      have hnat : (15743 : ℕ)^4407*625000000000000000^1024 ≤ 218966002402271^1024*100000^4407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15743 100000 218966002402271 625000000000000000 4407 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15743/100000 : ℝ)) (X := (218966002402271/625000000000000000 : ℝ)) (by norm_num) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000604781065015963/5000000000000000000 : ℝ) ≤ (10000281037922157/10000000000000000 : ℝ) ^ (4407/1024 : ℝ) := by
    have hpowers : (5000604781065015963/5000000000000000000 : ℝ)^1024 ≤ (10000281037922157/10000000000000000 : ℝ)^4407 := by
      have hnat : (5000604781065015963 : ℕ)^1024*10000000000000000^4407 ≤ 10000281037922157^4407*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000604781065015963 5000000000000000000 10000281037922157 10000000000000000 1024 4407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000281037922157/10000000000000000 : ℝ)) (X := (5000604781065015963/5000000000000000000 : ℝ)) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004108237103452299/10000000000000000000 : ℝ) ≤ (5000477214841023/5000000000000000 : ℝ) ^ (4407/1024 : ℝ) := by
    have hpowers : (10004108237103452299/10000000000000000000 : ℝ)^1024 ≤ (5000477214841023/5000000000000000 : ℝ)^4407 := by
      have hnat : (10004108237103452299 : ℕ)^1024*5000000000000000^4407 ≤ 5000477214841023^4407*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004108237103452299 10000000000000000000 5000477214841023 5000000000000000 1024 4407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000477214841023/5000000000000000 : ℝ)) (X := (10004108237103452299/10000000000000000000 : ℝ)) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (312718966002402271/312500000000000000 : ℝ) ≤ (2000325564288387/2000000000000000 : ℝ) ^ (4407/1024 : ℝ) := by
    have hpowers : (312718966002402271/312500000000000000 : ℝ)^1024 ≤ (2000325564288387/2000000000000000 : ℝ)^4407 := by
      have hnat : (312718966002402271 : ℕ)^1024*2000000000000000^4407 ≤ 2000325564288387^4407*312500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        312718966002402271 312500000000000000 2000325564288387 2000000000000000 1024 4407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000325564288387/2000000000000000 : ℝ)) (X := (312718966002402271/312500000000000000 : ℝ)) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(604781065015963/10000000000000000000 : ℝ) ≤ ((26373692986487892003/26380000000000000000 : ℝ)+2*(673391759889/527600000000000 : ℝ)*(10467/100000 : ℝ))^(4407/1024 : ℝ) := by
    rw [show (26373692986487892003/26380000000000000000 : ℝ)+2*(673391759889/527600000000000 : ℝ)*(10467/100000 : ℝ)=(10000281037922157/10000000000000000 : ℝ) by norm_num, show 1+2*(604781065015963/10000000000000000000 : ℝ)=(5000604781065015963/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(218966002402271/625000000000000000 : ℝ)+(604781065015963/10000000000000000000 : ℝ) ≤ ((26373692986487892003/26380000000000000000 : ℝ)+(673391759889/527600000000000 : ℝ)*((15743/100000 : ℝ)+(10467/100000 : ℝ)))^(4407/1024 : ℝ) := by
    rw [show (26373692986487892003/26380000000000000000 : ℝ)+(673391759889/527600000000000 : ℝ)*((15743/100000 : ℝ)+(10467/100000 : ℝ))=(5000477214841023/5000000000000000 : ℝ) by norm_num, show 1+(218966002402271/625000000000000000 : ℝ)+(604781065015963/10000000000000000000 : ℝ)=(10004108237103452299/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(218966002402271/625000000000000000 : ℝ) ≤ ((26373692986487892003/26380000000000000000 : ℝ)+2*(673391759889/527600000000000 : ℝ)*(15743/100000 : ℝ))^(4407/1024 : ℝ) := by
    rw [show (26373692986487892003/26380000000000000000 : ℝ)+2*(673391759889/527600000000000 : ℝ)*(15743/100000 : ℝ)=(2000325564288387/2000000000000000 : ℝ) by norm_num, show 1+2*(218966002402271/625000000000000000 : ℝ)=(312718966002402271/312500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26373692986487892003/26380000000000000000 : ℝ)*(X 1 0+X 2 0)+(673391759889/527600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4407/1024 : ℝ)) (lo := (10467/100000 : ℝ)) (hi := (15743/100000 : ℝ)) (c := (26373692986487892003/26380000000000000000 : ℝ)) (alpha := (673391759889/527600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26373692986487892003/26380000000000000000 : ℝ)*(X 0 1+X 2 1)+(673391759889/527600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4407/1024 : ℝ)) (lo := (10467/100000 : ℝ)) (hi := (15743/100000 : ℝ)) (c := (26373692986487892003/26380000000000000000 : ℝ)) (alpha := (673391759889/527600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26373692986487892003/26380000000000000000 : ℝ)*(X 0 2+X 1 2)+(673391759889/527600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4407/1024 : ℝ)) (lo := (10467/100000 : ℝ)) (hi := (15743/100000 : ℝ)) (c := (26373692986487892003/26380000000000000000 : ℝ)) (alpha := (673391759889/527600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-488717989/2500000000 : ℝ)*X 0 0+(1083081251/2000000000 : ℝ)*X 0 1+(523977247/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674517171/5000000000 : ℝ)*X 1 0+(-2044431469/10000000000 : ℝ)*X 1 1+(5239772477/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668629323/1250000000 : ℝ)*X 2 0+(2619886173/5000000000 : ℝ)*X 2 1+(-2044431319/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4299066359/10000000000 : ℝ)*X 0 0+(2055780731/5000000000 : ℝ)*X 0 1+(4494162977/10000000000 : ℝ)*X 0 2+(4299066359/10000000000 : ℝ)*X 1 0+(2055780731/5000000000 : ℝ)*X 1 1+(4494162977/10000000000 : ℝ)*X 1 2+(4299066359/10000000000 : ℝ)*X 2 0+(2055780731/5000000000 : ℝ)*X 2 1+(4494162977/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1954886257/10000000000 : ℝ)*X 0 0+(2620234519/5000000000 : ℝ)*X 0 1+(1353676517/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2651645773/5000000000 : ℝ)*X 1 0+(-1869498107/10000000000 : ℝ)*X 1 1+(1353676507/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1325822591/2500000000 : ℝ)*X 2 0+(5414706969/10000000000 : ℝ)*X 2 1+(-1869498429/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((859819501/2000000000 : ℝ)*X 0 0+(280790393/625000000 : ℝ)*X 0 1+(4113087807/10000000000 : ℝ)*X 0 2+(859819501/2000000000 : ℝ)*X 1 0+(280790393/625000000 : ℝ)*X 1 1+(4113087807/10000000000 : ℝ)*X 1 2+(859819501/2000000000 : ℝ)*X 2 0+(280790393/625000000 : ℝ)*X 2 1+(4113087807/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3169333169584451395145699679/329750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1680048851/100000000000000 : ℝ)*(base19) + (1801473561/100000000000000 : ℝ)*(base23) + (18209453/25000000000000 : ℝ)*(lower2) + (137186241/100000000000000 : ℝ)*(upper3) + (257137579/100000000000000 : ℝ)*(upper5) + (1038431593910877/25000000000000 : ℝ)*(major0) + (1038431593910877/25000000000000 : ℝ)*(major1) + (1038431593910877/25000000000000 : ℝ)*(major2) + (1423423846790827/25000000000000 : ℝ)*(sp0) + (5693731809620651/100000000000000 : ℝ)*(sp1) + (5693731688195941/100000000000000 : ℝ)*(sp2) + (1306851119687447/50000000000000 : ℝ)*(sp3) + (19051253097/50000000000000 : ℝ)*(sp4) + (8350932621/50000000000000 : ℝ)*(sp7) + (326714867655017/12500000000000 : ℝ)*(f.failure) + (2846866744834751/50000000000000 : ℝ)*(f.sum) + (30876794968097/6595000000000000000000000000 : ℝ)*base66 + (1413488971926333369/659500000000000000000000000000000 : ℝ)*base68 + (981747328582333369/659500000000000000000000000000000 : ℝ)*base70 + (2925154749265333369/659500000000000000000000000000000 : ℝ)*base72 + (1681044654161/3297500000000000000000000000 : ℝ)*base74 + (3361689314794833369/659500000000000000000000000000000 : ℝ)*base76 + (6081539491134333369/659500000000000000000000000000000 : ℝ)*base78 + (2449784189429333369/659500000000000000000000000000000 : ℝ)*base80 + (6744934600309/3297500000000000000000000000 : ℝ)*base81 + (5876377/625000000000000000000 : ℝ)*base89 + (5876377/625000000000000000000 : ℝ)*base91 + (5876377/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15225880930929356172389787/20609375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7453547/2000000000000 : ℝ)*(base8) + (165920639/20000000000000 : ℝ)*(base21) + (66506367/25000000000000 : ℝ)*(base29) + (71662473/25000000000000 : ℝ)*(upper2) + (523371561657163/12500000000000 : ℝ)*(major0) + (1046743189820693/25000000000000 : ℝ)*(major1) + (1046743189820693/25000000000000 : ℝ)*(major2) + (1315468331/100000000000000 : ℝ)*(sp0) + (1661863379/50000000000000 : ℝ)*(sp1) + (945431623/25000000000000 : ℝ)*(sp2) + (2869652342373511/50000000000000 : ℝ)*(sp4) + (2869651391570239/50000000000000 : ℝ)*(sp5) + (1434825373884387/25000000000000 : ℝ)*(sp6) + (2634639121046687/100000000000000 : ℝ)*(sp7) + (2634639121046687/100000000000000 : ℝ)*(f.failure) + (5739306372892703/100000000000000 : ℝ)*(f.sum) + (16660260887651/3297500000000000000000000000 : ℝ)*base65 + (4695168441800968079/659500000000000000000000000000000 : ℝ)*base67 + (8176497882009968079/659500000000000000000000000000000 : ℝ)*base69 + (2473233850902042489/329750000000000000000000000000000 : ℝ)*base71 + (7635401040629/13190000000000000000000000000 : ℝ)*base74 + (7680143664848818079/659500000000000000000000000000000 : ℝ)*base75 + (5780143406966042489/329750000000000000000000000000000 : ℝ)*base77 + (9980529957659318079/659500000000000000000000000000000 : ℝ)*base79 + (24353794114219/13190000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (46198353/5000000000000000000000 : ℝ)*base90 + (46198353/5000000000000000000000 : ℝ)*base92 + (46198353/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1448_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79460081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15743/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10467/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11217/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14937/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1448_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1448_s4_0 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1955684577/10000000000 : ℝ)*x 0 + (5408437301/10000000000 : ℝ)*x 1 + (20492991/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1955684577/10000000000 : ℝ)^551 ≤ (11935634081769/100000000000000 : ℝ)^423 := by
    have hnat : (1955684577 : ℕ)^551*100000000000000^423 ≤ 11935634081769^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1955684577 10000000000 11935634081769 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408437301/10000000000 : ℝ)^551 ≤ (44905465181707/100000000000000 : ℝ)^423 := by
    have hnat : (5408437301 : ℕ)^551*100000000000000^423 ≤ 44905465181707^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408437301 10000000000 44905465181707 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20492991/39062500 : ℝ)^551 ≤ (43158900714157/100000000000000 : ℝ)^423 := by
    have hnat : (20492991 : ℕ)^551*100000000000000^423 ≤ 43158900714157^423*39062500^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20492991 39062500 43158900714157 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1955684577/10000000000 : ℝ), (5408437301/10000000000 : ℝ), (20492991/39062500 : ℝ)] ![(11935634081769/100000000000000 : ℝ), (44905465181707/100000000000000 : ℝ), (43158900714157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1955684577/10000000000 : ℝ)|^551 ≤ (11935634081769/100000000000000 : ℝ)^423
        have hw : |(-1955684577/10000000000 : ℝ)|=(1955684577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408437301/10000000000 : ℝ)|^551 ≤ (44905465181707/100000000000000 : ℝ)^423
        have hw : |(5408437301/10000000000 : ℝ)|=(5408437301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(20492991/39062500 : ℝ)|^551 ≤ (43158900714157/100000000000000 : ℝ)^423
        have hw : |(20492991/39062500 : ℝ)|=(20492991/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s4_1 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5347230583/10000000000 : ℝ)*x 0 + (-1019143599/5000000000 : ℝ)*x 1 + (5246205673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347230583/10000000000 : ℝ)^551 ≤ (44244632523509/100000000000000 : ℝ)^423 := by
    have hnat : (5347230583 : ℕ)^551*100000000000000^423 ≤ 44244632523509^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347230583 10000000000 44244632523509 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1019143599/5000000000 : ℝ)^551 ≤ (393639593717/3125000000000 : ℝ)^423 := by
    have hnat : (1019143599 : ℕ)^551*3125000000000^423 ≤ 393639593717^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019143599 5000000000 393639593717 3125000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246205673/10000000000 : ℝ)^551 ≤ (21579450233843/50000000000000 : ℝ)^423 := by
    have hnat : (5246205673 : ℕ)^551*50000000000000^423 ≤ 21579450233843^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246205673 10000000000 21579450233843 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347230583/10000000000 : ℝ), (-1019143599/5000000000 : ℝ), (5246205673/10000000000 : ℝ)] ![(44244632523509/100000000000000 : ℝ), (393639593717/3125000000000 : ℝ), (21579450233843/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347230583/10000000000 : ℝ)|^551 ≤ (44244632523509/100000000000000 : ℝ)^423
        have hw : |(5347230583/10000000000 : ℝ)|=(5347230583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1019143599/5000000000 : ℝ)|^551 ≤ (393639593717/3125000000000 : ℝ)^423
        have hw : |(-1019143599/5000000000 : ℝ)|=(1019143599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246205673/10000000000 : ℝ)|^551 ≤ (21579450233843/50000000000000 : ℝ)^423
        have hw : |(5246205673/10000000000 : ℝ)|=(5246205673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s4_2 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2673615157/5000000000 : ℝ)*x 0 + (1311551461/2500000000 : ℝ)*x 1 + (-203828733/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673615157/5000000000 : ℝ)^551 ≤ (8848925924839/20000000000000 : ℝ)^423 := by
    have hnat : (2673615157 : ℕ)^551*20000000000000^423 ≤ 8848925924839^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673615157 5000000000 8848925924839 20000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311551461/2500000000 : ℝ)^551 ≤ (21579451150069/50000000000000 : ℝ)^423 := by
    have hnat : (1311551461 : ℕ)^551*50000000000000^423 ≤ 21579451150069^423*2500000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311551461 2500000000 21579451150069 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (203828733/1000000000 : ℝ)^551 ≤ (12596468061541/100000000000000 : ℝ)^423 := by
    have hnat : (203828733 : ℕ)^551*100000000000000^423 ≤ 12596468061541^423*1000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203828733 1000000000 12596468061541 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673615157/5000000000 : ℝ), (1311551461/2500000000 : ℝ), (-203828733/1000000000 : ℝ)] ![(8848925924839/20000000000000 : ℝ), (21579451150069/50000000000000 : ℝ), (12596468061541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673615157/5000000000 : ℝ)|^551 ≤ (8848925924839/20000000000000 : ℝ)^423
        have hw : |(2673615157/5000000000 : ℝ)|=(2673615157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311551461/2500000000 : ℝ)|^551 ≤ (21579451150069/50000000000000 : ℝ)^423
        have hw : |(1311551461/2500000000 : ℝ)|=(1311551461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-203828733/1000000000 : ℝ)|^551 ≤ (12596468061541/100000000000000 : ℝ)^423
        have hw : |(-203828733/1000000000 : ℝ)|=(203828733/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s4_3 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4299563369/10000000000 : ℝ)*x 0 + (1031524923/2500000000 : ℝ)*x 1 + (895901153/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4299563369/10000000000 : ℝ)^551 ≤ (16652076399473/50000000000000 : ℝ)^423 := by
    have hnat : (4299563369 : ℕ)^551*50000000000000^423 ≤ 16652076399473^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4299563369 10000000000 16652076399473 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1031524923/2500000000 : ℝ)^551 ≤ (31564713621781/100000000000000 : ℝ)^423 := by
    have hnat : (1031524923 : ℕ)^551*100000000000000^423 ≤ 31564713621781^423*2500000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031524923 2500000000 31564713621781 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (895901153/2000000000 : ℝ)^551 ≤ (1756556677869/5000000000000 : ℝ)^423 := by
    have hnat : (895901153 : ℕ)^551*5000000000000^423 ≤ 1756556677869^423*2000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895901153 2000000000 1756556677869 5000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4299563369/10000000000 : ℝ), (1031524923/2500000000 : ℝ), (895901153/2000000000 : ℝ)] ![(16652076399473/50000000000000 : ℝ), (31564713621781/100000000000000 : ℝ), (1756556677869/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4299563369/10000000000 : ℝ)|^551 ≤ (16652076399473/50000000000000 : ℝ)^423
        have hw : |(4299563369/10000000000 : ℝ)|=(4299563369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1031524923/2500000000 : ℝ)|^551 ≤ (31564713621781/100000000000000 : ℝ)^423
        have hw : |(1031524923/2500000000 : ℝ)|=(1031524923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(895901153/2000000000 : ℝ)|^551 ≤ (1756556677869/5000000000000 : ℝ)^423
        have hw : |(895901153/2000000000 : ℝ)|=(895901153/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s4_4 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-122231001/625000000 : ℝ)*x 0 + (5246800209/10000000000 : ℝ)*x 1 + (2703919907/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (122231001/625000000 : ℝ)^551 ≤ (1193572501997/10000000000000 : ℝ)^423 := by
    have hnat : (122231001 : ℕ)^551*10000000000000^423 ≤ 1193572501997^423*625000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122231001 625000000 1193572501997 10000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246800209/10000000000 : ℝ)^551 ≤ (43165271677303/100000000000000 : ℝ)^423 := by
    have hnat : (5246800209 : ℕ)^551*100000000000000^423 ≤ 43165271677303^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246800209 10000000000 43165271677303 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703919907/5000000000 : ℝ)^551 ≤ (44899003287659/100000000000000 : ℝ)^423 := by
    have hnat : (2703919907 : ℕ)^551*100000000000000^423 ≤ 44899003287659^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703919907 5000000000 44899003287659 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-122231001/625000000 : ℝ), (5246800209/10000000000 : ℝ), (2703919907/5000000000 : ℝ)] ![(1193572501997/10000000000000 : ℝ), (43165271677303/100000000000000 : ℝ), (44899003287659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-122231001/625000000 : ℝ)|^551 ≤ (1193572501997/10000000000000 : ℝ)^423
        have hw : |(-122231001/625000000 : ℝ)|=(122231001/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246800209/10000000000 : ℝ)|^551 ≤ (43165271677303/100000000000000 : ℝ)^423
        have hw : |(5246800209/10000000000 : ℝ)|=(5246800209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703919907/5000000000 : ℝ)|^551 ≤ (44899003287659/100000000000000 : ℝ)^423
        have hw : |(2703919907/5000000000 : ℝ)|=(2703919907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s4_5 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5304977633/10000000000 : ℝ)*x 0 + (-1876653211/10000000000 : ℝ)*x 1 + (5407839789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304977633/10000000000 : ℝ)^551 ≤ (10947442682879/25000000000000 : ℝ)^423 := by
    have hnat : (5304977633 : ℕ)^551*25000000000000^423 ≤ 10947442682879^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304977633 10000000000 10947442682879 25000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1876653211/10000000000 : ℝ)^551 ≤ (11311226241701/100000000000000 : ℝ)^423 := by
    have hnat : (1876653211 : ℕ)^551*100000000000000^423 ≤ 11311226241701^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1876653211 10000000000 11311226241701 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407839789/10000000000 : ℝ)^551 ≤ (8979800603457/20000000000000 : ℝ)^423 := by
    have hnat : (5407839789 : ℕ)^551*20000000000000^423 ≤ 8979800603457^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407839789 10000000000 8979800603457 20000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304977633/10000000000 : ℝ), (-1876653211/10000000000 : ℝ), (5407839789/10000000000 : ℝ)] ![(10947442682879/25000000000000 : ℝ), (11311226241701/100000000000000 : ℝ), (8979800603457/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304977633/10000000000 : ℝ)|^551 ≤ (10947442682879/25000000000000 : ℝ)^423
        have hw : |(5304977633/10000000000 : ℝ)|=(5304977633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1876653211/10000000000 : ℝ)|^551 ≤ (11311226241701/100000000000000 : ℝ)^423
        have hw : |(-1876653211/10000000000 : ℝ)|=(1876653211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407839789/10000000000 : ℝ)|^551 ≤ (8979800603457/20000000000000 : ℝ)^423
        have hw : |(5407839789/10000000000 : ℝ)|=(5407839789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s4_6 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (663122209/1250000000 : ℝ)*x 0 + (2703919889/5000000000 : ℝ)*x 1 + (-1876653173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663122209/1250000000 : ℝ)^551 ≤ (21894885575427/50000000000000 : ℝ)^423 := by
    have hnat : (663122209 : ℕ)^551*50000000000000^423 ≤ 21894885575427^423*1250000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663122209 1250000000 21894885575427 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703919889/5000000000 : ℝ)^551 ≤ (44899002898321/100000000000000 : ℝ)^423 := by
    have hnat : (2703919889 : ℕ)^551*100000000000000^423 ≤ 44899002898321^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703919889 5000000000 44899002898321 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1876653173/10000000000 : ℝ)^551 ≤ (2262245188671/20000000000000 : ℝ)^423 := by
    have hnat : (1876653173 : ℕ)^551*20000000000000^423 ≤ 2262245188671^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1876653173 10000000000 2262245188671 20000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663122209/1250000000 : ℝ), (2703919889/5000000000 : ℝ), (-1876653173/10000000000 : ℝ)] ![(21894885575427/50000000000000 : ℝ), (44899002898321/100000000000000 : ℝ), (2262245188671/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663122209/1250000000 : ℝ)|^551 ≤ (21894885575427/50000000000000 : ℝ)^423
        have hw : |(663122209/1250000000 : ℝ)|=(663122209/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703919889/5000000000 : ℝ)|^551 ≤ (44899002898321/100000000000000 : ℝ)^423
        have hw : |(2703919889/5000000000 : ℝ)|=(2703919889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1876653173/10000000000 : ℝ)|^551 ≤ (2262245188671/20000000000000 : ℝ)^423
        have hw : |(-1876653173/10000000000 : ℝ)|=(1876653173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s4_7 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (107489721/250000000 : ℝ)*x 0 + (4478210571/10000000000 : ℝ)*x 1 + (4127401589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107489721/250000000 : ℝ)^551 ≤ (8326102449519/25000000000000 : ℝ)^423 := by
    have hnat : (107489721 : ℕ)^551*25000000000000^423 ≤ 8326102449519^423*250000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107489721 250000000 8326102449519 25000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4478210571/10000000000 : ℝ)^551 ≤ (17558951332787/50000000000000 : ℝ)^423 := by
    have hnat : (4478210571 : ℕ)^551*50000000000000^423 ≤ 17558951332787^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4478210571 10000000000 17558951332787 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4127401589/10000000000 : ℝ)^551 ≤ (31577687527129/100000000000000 : ℝ)^423 := by
    have hnat : (4127401589 : ℕ)^551*100000000000000^423 ≤ 31577687527129^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4127401589 10000000000 31577687527129 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107489721/250000000 : ℝ), (4478210571/10000000000 : ℝ), (4127401589/10000000000 : ℝ)] ![(8326102449519/25000000000000 : ℝ), (17558951332787/50000000000000 : ℝ), (31577687527129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107489721/250000000 : ℝ)|^551 ≤ (8326102449519/25000000000000 : ℝ)^423
        have hw : |(107489721/250000000 : ℝ)|=(107489721/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4478210571/10000000000 : ℝ)|^551 ≤ (17558951332787/50000000000000 : ℝ)^423
        have hw : |(4478210571/10000000000 : ℝ)|=(4478210571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4127401589/10000000000 : ℝ)|^551 ≤ (31577687527129/100000000000000 : ℝ)^423
        have hw : |(4127401589/10000000000 : ℝ)|=(4127401589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1448_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79460081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14937/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11217/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2271/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1849/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14937/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11217/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14937/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11217/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14937/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11217/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14937/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11217/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14937/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11217/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14937/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11217/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11217/100000 : ℝ) ^ (4407/1024 : ℝ) ≤ (1018249159688109/12500000000000000000 : ℝ) := by
    have hpowers : (11217/100000 : ℝ)^4407 ≤ (1018249159688109/12500000000000000000 : ℝ)^1024 := by
      have hnat : (11217 : ℕ)^4407*12500000000000000000^1024 ≤ 1018249159688109^1024*100000^4407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11217 100000 1018249159688109 12500000000000000000 4407 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11217/100000 : ℝ)) (X := (1018249159688109/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14937/100000 : ℝ) ^ (4407/1024 : ℝ) ≤ (5588538883247631/20000000000000000000 : ℝ) := by
    have hpowers : (14937/100000 : ℝ)^4407 ≤ (5588538883247631/20000000000000000000 : ℝ)^1024 := by
      have hnat : (14937 : ℕ)^4407*20000000000000000000^1024 ≤ 5588538883247631^1024*100000^4407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14937 100000 5588538883247631 20000000000000000000 4407 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14937/100000 : ℝ)) (X := (5588538883247631/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251018249159688109/6250000000000000000 : ℝ) ≤ (10000378533040841/10000000000000000 : ℝ) ^ (4407/1024 : ℝ) := by
    have hpowers : (6251018249159688109/6250000000000000000 : ℝ)^1024 ≤ (10000378533040841/10000000000000000 : ℝ)^4407 := by
      have hnat : (6251018249159688109 : ℕ)^1024*10000000000000000^4407 ≤ 10000378533040841^4407*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251018249159688109 6250000000000000000 10000378533040841 10000000000000000 1024 4407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000378533040841/10000000000000000 : ℝ)) (X := (6251018249159688109/6250000000000000000 : ℝ)) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100036088687693743027/100000000000000000000 : ℝ) ≤ (10000838432004813/10000000000000000 : ℝ) ^ (4407/1024 : ℝ) := by
    have hpowers : (100036088687693743027/100000000000000000000 : ℝ)^1024 ≤ (10000838432004813/10000000000000000 : ℝ)^4407 := by
      have hnat : (100036088687693743027 : ℕ)^1024*10000000000000000^4407 ≤ 10000838432004813^4407*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100036088687693743027 100000000000000000000 10000838432004813 10000000000000000 1024 4407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000838432004813/10000000000000000 : ℝ)) (X := (100036088687693743027/100000000000000000000 : ℝ)) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10005588538883247631/10000000000000000000 : ℝ) ≤ (2000259666193757/2000000000000000 : ℝ) ^ (4407/1024 : ℝ) := by
    have hpowers : (10005588538883247631/10000000000000000000 : ℝ)^1024 ≤ (2000259666193757/2000000000000000 : ℝ)^4407 := by
      have hnat : (10005588538883247631 : ℕ)^1024*2000000000000000^4407 ≤ 2000259666193757^4407*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005588538883247631 10000000000000000000 2000259666193757 2000000000000000 1024 4407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000259666193757/2000000000000000 : ℝ)) (X := (10005588538883247631/10000000000000000000 : ℝ)) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1018249159688109/12500000000000000000 : ℝ) ≤ ((193703597758094691/193750000000000000 : ℝ)+2*(114974740993/93000000000000 : ℝ)*(11217/100000 : ℝ))^(4407/1024 : ℝ) := by
    rw [show (193703597758094691/193750000000000000 : ℝ)+2*(114974740993/93000000000000 : ℝ)*(11217/100000 : ℝ)=(10000378533040841/10000000000000000 : ℝ) by norm_num, show 1+2*(1018249159688109/12500000000000000000 : ℝ)=(6251018249159688109/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5588538883247631/20000000000000000000 : ℝ)+(1018249159688109/12500000000000000000 : ℝ) ≤ ((193703597758094691/193750000000000000 : ℝ)+(114974740993/93000000000000 : ℝ)*((14937/100000 : ℝ)+(11217/100000 : ℝ)))^(4407/1024 : ℝ) := by
    rw [show (193703597758094691/193750000000000000 : ℝ)+(114974740993/93000000000000 : ℝ)*((14937/100000 : ℝ)+(11217/100000 : ℝ))=(10000838432004813/10000000000000000 : ℝ) by norm_num, show 1+(5588538883247631/20000000000000000000 : ℝ)+(1018249159688109/12500000000000000000 : ℝ)=(100036088687693743027/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5588538883247631/20000000000000000000 : ℝ) ≤ ((193703597758094691/193750000000000000 : ℝ)+2*(114974740993/93000000000000 : ℝ)*(14937/100000 : ℝ))^(4407/1024 : ℝ) := by
    rw [show (193703597758094691/193750000000000000 : ℝ)+2*(114974740993/93000000000000 : ℝ)*(14937/100000 : ℝ)=(2000259666193757/2000000000000000 : ℝ) by norm_num, show 1+2*(5588538883247631/20000000000000000000 : ℝ)=(10005588538883247631/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (193703597758094691/193750000000000000 : ℝ)*(X 1 0+X 2 0)+(114974740993/93000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4407/1024 : ℝ)) (lo := (11217/100000 : ℝ)) (hi := (14937/100000 : ℝ)) (c := (193703597758094691/193750000000000000 : ℝ)) (alpha := (114974740993/93000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (193703597758094691/193750000000000000 : ℝ)*(X 0 1+X 2 1)+(114974740993/93000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4407/1024 : ℝ)) (lo := (11217/100000 : ℝ)) (hi := (14937/100000 : ℝ)) (c := (193703597758094691/193750000000000000 : ℝ)) (alpha := (114974740993/93000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (193703597758094691/193750000000000000 : ℝ)*(X 0 2+X 1 2)+(114974740993/93000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4407/1024 : ℝ)) (lo := (11217/100000 : ℝ)) (hi := (14937/100000 : ℝ)) (c := (193703597758094691/193750000000000000 : ℝ)) (alpha := (114974740993/93000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1955684577/10000000000 : ℝ)*X 0 0+(5408437301/10000000000 : ℝ)*X 0 1+(20492991/39062500 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347230583/10000000000 : ℝ)*X 1 0+(-1019143599/5000000000 : ℝ)*X 1 1+(5246205673/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673615157/5000000000 : ℝ)*X 2 0+(1311551461/2500000000 : ℝ)*X 2 1+(-203828733/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4299563369/10000000000 : ℝ)*X 0 0+(1031524923/2500000000 : ℝ)*X 0 1+(895901153/2000000000 : ℝ)*X 0 2+(4299563369/10000000000 : ℝ)*X 1 0+(1031524923/2500000000 : ℝ)*X 1 1+(895901153/2000000000 : ℝ)*X 1 2+(4299563369/10000000000 : ℝ)*X 2 0+(1031524923/2500000000 : ℝ)*X 2 1+(895901153/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-122231001/625000000 : ℝ)*X 0 0+(5246800209/10000000000 : ℝ)*X 0 1+(2703919907/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5304977633/10000000000 : ℝ)*X 1 0+(-1876653211/10000000000 : ℝ)*X 1 1+(5407839789/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663122209/1250000000 : ℝ)*X 2 0+(2703919889/5000000000 : ℝ)*X 2 1+(-1876653173/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((107489721/250000000 : ℝ)*X 0 0+(4478210571/10000000000 : ℝ)*X 0 1+(4127401589/10000000000 : ℝ)*X 0 2+(107489721/250000000 : ℝ)*X 1 0+(4478210571/10000000000 : ℝ)*X 1 1+(4127401589/10000000000 : ℝ)*X 1 2+(107489721/250000000 : ℝ)*X 2 0+(4478210571/10000000000 : ℝ)*X 2 1+(4127401589/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5255394788168976387979/1550000000000000000000000000 : ℝ) := by norm_num
    linear_combination (98317047/12500000000000 : ℝ)*(base19) + (470903479/100000000000000 : ℝ)*(base23) + (25783357/50000000000000 : ℝ)*(upper2) + (223243977/100000000000000 : ℝ)*(upper3) + (54529839/100000000000000 : ℝ)*(upper4) + (4496837864121553/100000000000000 : ℝ)*(major0) + (4496837864121553/100000000000000 : ℝ)*(major1) + (4496837864121553/100000000000000 : ℝ)*(major2) + (6164046431263097/100000000000000 : ℝ)*(sp0) + (6164054088606969/100000000000000 : ℝ)*(sp1) + (1232810880847973/20000000000000 : ℝ)*(sp2) + (70740308010017/2500000000000 : ℝ)*(sp3) + (8443880247/100000000000000 : ℝ)*(sp4) + (1683935967/20000000000000 : ℝ)*(sp7) + (565924148016103/20000000000000 : ℝ)*(f.failure) + (385253429696459/6250000000000 : ℝ)*(f.sum) + (5909759583221/4650000000000000000000000000 : ℝ)*base66 + (222434980328393381/58125000000000000000000000000000 : ℝ)*base68 + (109106914634106619/58125000000000000000000000000000 : ℝ)*base69 + (340596483844643381/58125000000000000000000000000000 : ℝ)*base72 + (3240221726179/4650000000000000000000000000 : ℝ)*base73 + (161164794177231619/58125000000000000000000000000000 : ℝ)*base75 + (255095562705981619/58125000000000000000000000000000 : ℝ)*base77 + (51002165528393381/58125000000000000000000000000000 : ℝ)*base80 + (33396775255121/4650000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (3684343/1000000000000000000000 : ℝ)*base89 + (3684343/1000000000000000000000 : ℝ)*base91 + (3684343/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (109923318456356724724224887/9687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1737627419/100000000000000 : ℝ)*(base19) + (2008250049/100000000000000 : ℝ)*(base23) + (97628249/50000000000000 : ℝ)*(upper3) + (12778889/12500000000000 : ℝ)*(lower4) + (253330697/100000000000000 : ℝ)*(upper5) + (4530103047826673/100000000000000 : ℝ)*(major0) + (4530103047826673/100000000000000 : ℝ)*(major1) + (4530103047826673/100000000000000 : ℝ)*(major2) + (454085541/1250000000000 : ℝ)*(sp1) + (20188983621/50000000000000 : ℝ)*(sp2) + (310482648382731/5000000000000 : ℝ)*(sp4) + (3104807451591961/50000000000000 : ℝ)*(sp5) + (6209610581437329/100000000000000 : ℝ)*(sp6) + (570110549953589/20000000000000 : ℝ)*(sp7) + (570110549953589/20000000000000 : ℝ)*(f.failure) + (310482648382731/5000000000000 : ℝ)*(f.sum) + (19150841464289/4650000000000000000000000000 : ℝ)*base65 + (725909924339089621/58125000000000000000000000000000 : ℝ)*base68 + (815634180107839621/58125000000000000000000000000000 : ℝ)*base70 + (15728240378464621/58125000000000000000000000000000 : ℝ)*base72 + (2522825894161/4650000000000000000000000000 : ℝ)*base74 + (563229809654089621/58125000000000000000000000000000 : ℝ)*base76 + (293242751959714621/58125000000000000000000000000000 : ℝ)*base78 + (699487440332839621/58125000000000000000000000000000 : ℝ)*base80 + (3952153193911/4650000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1819291/1000000000000000000000 : ℝ)*base90 + (1819291/1000000000000000000000 : ℝ)*base92 + (1819291/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1448_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79460081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14937/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11217/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2271/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1849/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1448_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1448_s5_0 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-977899419/5000000000 : ℝ)*x 0 + (2703696959/5000000000 : ℝ)*x 1 + (1311793479/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (977899419/5000000000 : ℝ)^551 ≤ (298413561137/2500000000000 : ℝ)^423 := by
    have hnat : (977899419 : ℕ)^551*2500000000000^423 ≤ 298413561137^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977899419 5000000000 298413561137 2500000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703696959/5000000000 : ℝ)^551 ≤ (897883620187/2000000000000 : ℝ)^423 := by
    have hnat : (2703696959 : ℕ)^551*2000000000000^423 ≤ 897883620187^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703696959 5000000000 897883620187 2000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311793479/2500000000 : ℝ)^551 ≤ (21584638267531/50000000000000 : ℝ)^423 := by
    have hnat : (1311793479 : ℕ)^551*50000000000000^423 ≤ 21584638267531^423*2500000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311793479 2500000000 21584638267531 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-977899419/5000000000 : ℝ), (2703696959/5000000000 : ℝ), (1311793479/2500000000 : ℝ)] ![(298413561137/2500000000000 : ℝ), (897883620187/2000000000000 : ℝ), (21584638267531/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-977899419/5000000000 : ℝ)|^551 ≤ (298413561137/2500000000000 : ℝ)^423
        have hw : |(-977899419/5000000000 : ℝ)|=(977899419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703696959/5000000000 : ℝ)|^551 ≤ (897883620187/2000000000000 : ℝ)^423
        have hw : |(2703696959/5000000000 : ℝ)|=(2703696959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311793479/2500000000 : ℝ)|^551 ≤ (21584638267531/50000000000000 : ℝ)^423
        have hw : |(1311793479/2500000000 : ℝ)|=(1311793479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s5_1 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2673480403/5000000000 : ℝ)*x 0 + (-1018679661/5000000000 : ℝ)*x 1 + (5247173959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673480403/5000000000 : ℝ)^551 ≤ (22120862428757/50000000000000 : ℝ)^423 := by
    have hnat : (2673480403 : ℕ)^551*50000000000000^423 ≤ 22120862428757^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673480403 5000000000 22120862428757 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1018679661/5000000000 : ℝ)^551 ≤ (629449906677/5000000000000 : ℝ)^423 := by
    have hnat : (1018679661 : ℕ)^551*5000000000000^423 ≤ 629449906677^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018679661 5000000000 629449906677 5000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247173959/10000000000 : ℝ)^551 ≤ (1079231924897/2500000000000 : ℝ)^423 := by
    have hnat : (5247173959 : ℕ)^551*2500000000000^423 ≤ 1079231924897^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247173959 10000000000 1079231924897 2500000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673480403/5000000000 : ℝ), (-1018679661/5000000000 : ℝ), (5247173959/10000000000 : ℝ)] ![(22120862428757/50000000000000 : ℝ), (629449906677/5000000000000 : ℝ), (1079231924897/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673480403/5000000000 : ℝ)|^551 ≤ (22120862428757/50000000000000 : ℝ)^423
        have hw : |(2673480403/5000000000 : ℝ)|=(2673480403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1018679661/5000000000 : ℝ)|^551 ≤ (629449906677/5000000000000 : ℝ)^423
        have hw : |(-1018679661/5000000000 : ℝ)|=(1018679661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247173959/10000000000 : ℝ)|^551 ≤ (1079231924897/2500000000000 : ℝ)^423
        have hw : |(5247173959/10000000000 : ℝ)|=(5247173959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s5_2 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1069392213/2000000000 : ℝ)*x 0 + (81987089/156250000 : ℝ)*x 1 + (-1018679663/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069392213/2000000000 : ℝ)^551 ≤ (44241727649003/100000000000000 : ℝ)^423 := by
    have hnat : (1069392213 : ℕ)^551*100000000000000^423 ≤ 44241727649003^423*2000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069392213 2000000000 44241727649003 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81987089/156250000 : ℝ)^551 ≤ (43169274177391/100000000000000 : ℝ)^423 := by
    have hnat : (81987089 : ℕ)^551*100000000000000^423 ≤ 43169274177391^423*156250000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81987089 156250000 43169274177391 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1018679663/5000000000 : ℝ)^551 ≤ (1573624770717/12500000000000 : ℝ)^423 := by
    have hnat : (1018679663 : ℕ)^551*12500000000000^423 ≤ 1573624770717^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018679663 5000000000 1573624770717 12500000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069392213/2000000000 : ℝ), (81987089/156250000 : ℝ), (-1018679663/5000000000 : ℝ)] ![(44241727649003/100000000000000 : ℝ), (43169274177391/100000000000000 : ℝ), (1573624770717/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069392213/2000000000 : ℝ)|^551 ≤ (44241727649003/100000000000000 : ℝ)^423
        have hw : |(1069392213/2000000000 : ℝ)|=(1069392213/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(81987089/156250000 : ℝ)|^551 ≤ (43169274177391/100000000000000 : ℝ)^423
        have hw : |(81987089/156250000 : ℝ)|=(81987089/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1018679663/5000000000 : ℝ)|^551 ≤ (1573624770717/12500000000000 : ℝ)^423
        have hw : |(-1018679663/5000000000 : ℝ)|=(1018679663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s5_3 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1074908659/2500000000 : ℝ)*x 0 + (2064141093/5000000000 : ℝ)*x 1 + (2238653077/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074908659/2500000000 : ℝ)^551 ≤ (33304871875013/100000000000000 : ℝ)^423 := by
    have hnat : (1074908659 : ℕ)^551*100000000000000^423 ≤ 33304871875013^423*2500000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074908659 2500000000 33304871875013 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2064141093/5000000000 : ℝ)^551 ≤ (15793231858871/50000000000000 : ℝ)^423 := by
    have hnat : (2064141093 : ℕ)^551*50000000000000^423 ≤ 15793231858871^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064141093 5000000000 15793231858871 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2238653077/5000000000 : ℝ)^551 ≤ (35108664393739/100000000000000 : ℝ)^423 := by
    have hnat : (2238653077 : ℕ)^551*100000000000000^423 ≤ 35108664393739^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238653077 5000000000 35108664393739 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074908659/2500000000 : ℝ), (2064141093/5000000000 : ℝ), (2238653077/5000000000 : ℝ)] ![(33304871875013/100000000000000 : ℝ), (15793231858871/50000000000000 : ℝ), (35108664393739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074908659/2500000000 : ℝ)|^551 ≤ (33304871875013/100000000000000 : ℝ)^423
        have hw : |(1074908659/2500000000 : ℝ)|=(1074908659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2064141093/5000000000 : ℝ)|^551 ≤ (15793231858871/50000000000000 : ℝ)^423
        have hw : |(2064141093/5000000000 : ℝ)|=(2064141093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2238653077/5000000000 : ℝ)|^551 ≤ (35108664393739/100000000000000 : ℝ)^423
        have hw : |(2238653077/5000000000 : ℝ)|=(2238653077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s5_4 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-391162019/2000000000 : ℝ)*x 0 + (5247753793/10000000000 : ℝ)*x 1 + (5406811/10000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (391162019/2000000000 : ℝ)^551 ≤ (1492078992299/12500000000000 : ℝ)^423 := by
    have hnat : (391162019 : ℕ)^551*12500000000000^423 ≤ 1492078992299^423*2000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      391162019 2000000000 1492078992299 12500000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247753793/10000000000 : ℝ)^551 ≤ (43175490999223/100000000000000 : ℝ)^423 := by
    have hnat : (5247753793 : ℕ)^551*100000000000000^423 ≤ 43175490999223^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247753793 10000000000 43175490999223 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406811/10000000 : ℝ)^551 ≤ (44887877046299/100000000000000 : ℝ)^423 := by
    have hnat : (5406811 : ℕ)^551*100000000000000^423 ≤ 44887877046299^423*10000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406811 10000000 44887877046299 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-391162019/2000000000 : ℝ), (5247753793/10000000000 : ℝ), (5406811/10000000 : ℝ)] ![(1492078992299/12500000000000 : ℝ), (43175490999223/100000000000000 : ℝ), (44887877046299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-391162019/2000000000 : ℝ)|^551 ≤ (1492078992299/12500000000000 : ℝ)^423
        have hw : |(-391162019/2000000000 : ℝ)|=(391162019/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247753793/10000000000 : ℝ)|^551 ≤ (43175490999223/100000000000000 : ℝ)^423
        have hw : |(5247753793/10000000000 : ℝ)|=(5247753793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406811/10000000 : ℝ)|^551 ≤ (44887877046299/100000000000000 : ℝ)^423
        have hw : |(5406811/10000000 : ℝ)|=(5406811/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s5_5 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5305231811/10000000000 : ℝ)*x 0 + (-1877722139/10000000000 : ℝ)*x 1 + (2703405493/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305231811/10000000000 : ℝ)^551 ≤ (43792503742971/100000000000000 : ℝ)^423 := by
    have hnat : (5305231811 : ℕ)^551*100000000000000^423 ≤ 43792503742971^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305231811 10000000000 43792503742971 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1877722139/10000000000 : ℝ)^551 ≤ (5659809674433/50000000000000 : ℝ)^423 := by
    have hnat : (1877722139 : ℕ)^551*50000000000000^423 ≤ 5659809674433^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1877722139 10000000000 5659809674433 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703405493/5000000000 : ℝ)^551 ≤ (22443938447449/50000000000000 : ℝ)^423 := by
    have hnat : (2703405493 : ℕ)^551*50000000000000^423 ≤ 22443938447449^423*5000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703405493 5000000000 22443938447449 50000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305231811/10000000000 : ℝ), (-1877722139/10000000000 : ℝ), (2703405493/5000000000 : ℝ)] ![(43792503742971/100000000000000 : ℝ), (5659809674433/50000000000000 : ℝ), (22443938447449/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305231811/10000000000 : ℝ)|^551 ≤ (43792503742971/100000000000000 : ℝ)^423
        have hw : |(5305231811/10000000000 : ℝ)|=(5305231811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1877722139/10000000000 : ℝ)|^551 ≤ (5659809674433/50000000000000 : ℝ)^423
        have hw : |(-1877722139/10000000000 : ℝ)|=(1877722139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703405493/5000000000 : ℝ)|^551 ≤ (22443938447449/50000000000000 : ℝ)^423
        have hw : |(2703405493/5000000000 : ℝ)|=(2703405493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s5_6 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (331576987/625000000 : ℝ)*x 0 + (5406811021/10000000000 : ℝ)*x 1 + (-1877722117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331576987/625000000 : ℝ)^551 ≤ (1751700141547/4000000000000 : ℝ)^423 := by
    have hnat : (331576987 : ℕ)^551*4000000000000^423 ≤ 1751700141547^423*625000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331576987 625000000 1751700141547 4000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406811021/10000000000 : ℝ)^551 ≤ (224439386367/500000000000 : ℝ)^423 := by
    have hnat : (5406811021 : ℕ)^551*500000000000^423 ≤ 224439386367^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406811021 10000000000 224439386367 500000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1877722117/10000000000 : ℝ)^551 ≤ (1131961917611/10000000000000 : ℝ)^423 := by
    have hnat : (1877722117 : ℕ)^551*10000000000000^423 ≤ 1131961917611^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1877722117 10000000000 1131961917611 10000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331576987/625000000 : ℝ), (5406811021/10000000000 : ℝ), (-1877722117/10000000000 : ℝ)] ![(1751700141547/4000000000000 : ℝ), (224439386367/500000000000 : ℝ), (1131961917611/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331576987/625000000 : ℝ)|^551 ≤ (1751700141547/4000000000000 : ℝ)^423
        have hw : |(331576987/625000000 : ℝ)|=(331576987/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406811021/10000000000 : ℝ)|^551 ≤ (224439386367/500000000000 : ℝ)^423
        have hw : |(5406811021/10000000000 : ℝ)|=(5406811021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1877722117/10000000000 : ℝ)|^551 ≤ (1131961917611/10000000000000 : ℝ)^423
        have hw : |(-1877722117/10000000000 : ℝ)|=(1877722117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1448_s5_7 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ)) (x : Fin 3 → ℝ) :
    (537457387/1250000000 : ℝ)*x 0 + (4476042871/10000000000 : ℝ)*x 1 + (258097/625000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537457387/1250000000 : ℝ)^551 ≤ (33305118674511/100000000000000 : ℝ)^423 := by
    have hnat : (537457387 : ℕ)^551*100000000000000^423 ≤ 33305118674511^423*1250000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537457387 1250000000 33305118674511 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4476042871/10000000000 : ℝ)^551 ≤ (35095761388961/100000000000000 : ℝ)^423 := by
    have hnat : (4476042871 : ℕ)^551*100000000000000^423 ≤ 35095761388961^423*10000000000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4476042871 10000000000 35095761388961 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258097/625000 : ℝ)^551 ≤ (31599119913489/100000000000000 : ℝ)^423 := by
    have hnat : (258097 : ℕ)^551*100000000000000^423 ≤ 31599119913489^423*625000^551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258097 625000 31599119913489 100000000000000 551 423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (551/128 : ℝ)) 551 423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537457387/1250000000 : ℝ), (4476042871/10000000000 : ℝ), (258097/625000 : ℝ)] ![(33305118674511/100000000000000 : ℝ), (35095761388961/100000000000000 : ℝ), (31599119913489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537457387/1250000000 : ℝ)|^551 ≤ (33305118674511/100000000000000 : ℝ)^423
        have hw : |(537457387/1250000000 : ℝ)|=(537457387/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4476042871/10000000000 : ℝ)|^551 ≤ (35095761388961/100000000000000 : ℝ)^423
        have hw : |(4476042871/10000000000 : ℝ)|=(4476042871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(258097/625000 : ℝ)|^551 ≤ (31599119913489/100000000000000 : ℝ)^423
        have hw : |(258097/625000 : ℝ)|=(258097/625000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1448_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79460081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1849/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2271/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (91/800 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1477/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1849/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2271/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1849/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2271/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1849/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2271/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1849/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2271/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1849/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2271/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1849/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2271/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2271/20000 : ℝ) ^ (4407/1024 : ℝ) ≤ (8586151640532809/100000000000000000000 : ℝ) := by
    have hpowers : (2271/20000 : ℝ)^4407 ≤ (8586151640532809/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2271 : ℕ)^4407*100000000000000000000^1024 ≤ 8586151640532809^1024*20000^4407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2271 20000 8586151640532809 100000000000000000000 4407 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2271/20000 : ℝ)) (X := (8586151640532809/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1849/12500 : ℝ) ^ (4407/1024 : ℝ) ≤ (13396942336669097/50000000000000000000 : ℝ) := by
    have hpowers : (1849/12500 : ℝ)^4407 ≤ (13396942336669097/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1849 : ℕ)^4407*50000000000000000000^1024 ≤ 13396942336669097^1024*12500^4407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1849 12500 13396942336669097 50000000000000000000 4407 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1849/12500 : ℝ)) (X := (13396942336669097/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008586151640532809/50000000000000000000 : ℝ) ≤ (5000199492621627/5000000000000000 : ℝ) ^ (4407/1024 : ℝ) := by
    have hpowers : (50008586151640532809/50000000000000000000 : ℝ)^1024 ≤ (5000199492621627/5000000000000000 : ℝ)^4407 := by
      have hnat : (50008586151640532809 : ℕ)^1024*5000000000000000^4407 ≤ 5000199492621627^4407*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008586151640532809 50000000000000000000 5000199492621627 5000000000000000 1024 4407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000199492621627/5000000000000000 : ℝ)) (X := (50008586151640532809/50000000000000000000 : ℝ)) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100035380036313871003/100000000000000000000 : ℝ) ≤ (400032878818637/400000000000000 : ℝ) ^ (4407/1024 : ℝ) := by
    have hpowers : (100035380036313871003/100000000000000000000 : ℝ)^1024 ≤ (400032878818637/400000000000000 : ℝ)^4407 := by
      have hnat : (100035380036313871003 : ℕ)^1024*400000000000000^4407 ≤ 400032878818637^4407*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100035380036313871003 100000000000000000000 400032878818637 400000000000000 1024 4407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400032878818637/400000000000000 : ℝ)) (X := (100035380036313871003/100000000000000000000 : ℝ)) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013396942336669097/25000000000000000000 : ℝ) ≤ (2500311238922149/2500000000000000 : ℝ) ^ (4407/1024 : ℝ) := by
    have hpowers : (25013396942336669097/25000000000000000000 : ℝ)^1024 ≤ (2500311238922149/2500000000000000 : ℝ)^4407 := by
      have hnat : (25013396942336669097 : ℕ)^1024*2500000000000000^4407 ≤ 2500311238922149^4407*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013396942336669097 25000000000000000000 2500311238922149 2500000000000000 1024 4407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500311238922149/2500000000000000 : ℝ)) (X := (25013396942336669097/25000000000000000000 : ℝ)) (by norm_num) 4407 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8586151640532809/100000000000000000000 : ℝ) ≤ ((8590441329468551397/8592500000000000000 : ℝ)+2*(422985222671/343700000000000 : ℝ)*(2271/20000 : ℝ))^(4407/1024 : ℝ) := by
    rw [show (8590441329468551397/8592500000000000000 : ℝ)+2*(422985222671/343700000000000 : ℝ)*(2271/20000 : ℝ)=(5000199492621627/5000000000000000 : ℝ) by norm_num, show 1+2*(8586151640532809/100000000000000000000 : ℝ)=(50008586151640532809/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13396942336669097/50000000000000000000 : ℝ)+(8586151640532809/100000000000000000000 : ℝ) ≤ ((8590441329468551397/8592500000000000000 : ℝ)+(422985222671/343700000000000 : ℝ)*((1849/12500 : ℝ)+(2271/20000 : ℝ)))^(4407/1024 : ℝ) := by
    rw [show (8590441329468551397/8592500000000000000 : ℝ)+(422985222671/343700000000000 : ℝ)*((1849/12500 : ℝ)+(2271/20000 : ℝ))=(400032878818637/400000000000000 : ℝ) by norm_num, show 1+(13396942336669097/50000000000000000000 : ℝ)+(8586151640532809/100000000000000000000 : ℝ)=(100035380036313871003/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13396942336669097/50000000000000000000 : ℝ) ≤ ((8590441329468551397/8592500000000000000 : ℝ)+2*(422985222671/343700000000000 : ℝ)*(1849/12500 : ℝ))^(4407/1024 : ℝ) := by
    rw [show (8590441329468551397/8592500000000000000 : ℝ)+2*(422985222671/343700000000000 : ℝ)*(1849/12500 : ℝ)=(2500311238922149/2500000000000000 : ℝ) by norm_num, show 1+2*(13396942336669097/50000000000000000000 : ℝ)=(25013396942336669097/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8590441329468551397/8592500000000000000 : ℝ)*(X 1 0+X 2 0)+(422985222671/343700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4407/1024 : ℝ)) (lo := (2271/20000 : ℝ)) (hi := (1849/12500 : ℝ)) (c := (8590441329468551397/8592500000000000000 : ℝ)) (alpha := (422985222671/343700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8590441329468551397/8592500000000000000 : ℝ)*(X 0 1+X 2 1)+(422985222671/343700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4407/1024 : ℝ)) (lo := (2271/20000 : ℝ)) (hi := (1849/12500 : ℝ)) (c := (8590441329468551397/8592500000000000000 : ℝ)) (alpha := (422985222671/343700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8590441329468551397/8592500000000000000 : ℝ)*(X 0 2+X 1 2)+(422985222671/343700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4407/1024 : ℝ)) (lo := (2271/20000 : ℝ)) (hi := (1849/12500 : ℝ)) (c := (8590441329468551397/8592500000000000000 : ℝ)) (alpha := (422985222671/343700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-977899419/5000000000 : ℝ)*X 0 0+(2703696959/5000000000 : ℝ)*X 0 1+(1311793479/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673480403/5000000000 : ℝ)*X 1 0+(-1018679661/5000000000 : ℝ)*X 1 1+(5247173959/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069392213/2000000000 : ℝ)*X 2 0+(81987089/156250000 : ℝ)*X 2 1+(-1018679663/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1074908659/2500000000 : ℝ)*X 0 0+(2064141093/5000000000 : ℝ)*X 0 1+(2238653077/5000000000 : ℝ)*X 0 2+(1074908659/2500000000 : ℝ)*X 1 0+(2064141093/5000000000 : ℝ)*X 1 1+(2238653077/5000000000 : ℝ)*X 1 2+(1074908659/2500000000 : ℝ)*X 2 0+(2064141093/5000000000 : ℝ)*X 2 1+(2238653077/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-391162019/2000000000 : ℝ)*X 0 0+(5247753793/10000000000 : ℝ)*X 0 1+(5406811/10000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305231811/10000000000 : ℝ)*X 1 0+(-1877722139/10000000000 : ℝ)*X 1 1+(2703405493/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((331576987/625000000 : ℝ)*X 2 0+(5406811021/10000000000 : ℝ)*X 2 1+(-1877722117/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((537457387/1250000000 : ℝ)*X 0 0+(4476042871/10000000000 : ℝ)*X 0 1+(258097/625000 : ℝ)*X 0 2+(537457387/1250000000 : ℝ)*X 1 0+(4476042871/10000000000 : ℝ)*X 1 1+(258097/625000 : ℝ)*X 1 2+(537457387/1250000000 : ℝ)*X 2 0+(4476042871/10000000000 : ℝ)*X 2 1+(258097/625000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1448_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2220253863267226249361641167/214812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1653667977/100000000000000 : ℝ)*(base19) + (222673311/12500000000000 : ℝ)*(base23) + (11670493/12500000000000 : ℝ)*(lower2) + (114618131/50000000000000 : ℝ)*(upper3) + (147878867/100000000000000 : ℝ)*(upper5) + (2276664277162137/50000000000000 : ℝ)*(major0) + (2276664277162137/50000000000000 : ℝ)*(major1) + (2276664277162137/50000000000000 : ℝ)*(major2) + (6241452883682307/100000000000000 : ℝ)*(sp0) + (6241487785540777/100000000000000 : ℝ)*(sp1) + (3120743828911133/50000000000000 : ℝ)*(sp2) + (358143558090511/12500000000000 : ℝ)*(sp3) + (36555526447/100000000000000 : ℝ)*(sp4) + (3772037967/20000000000000 : ℝ)*(sp7) + (716291831228481/25000000000000 : ℝ)*(f.failure) + (3120744719604377/50000000000000 : ℝ)*(f.sum) + (109897013178409/17185000000000000000000000000 : ℝ)*base65 + (3423093583541280389/429625000000000000000000000000000 : ℝ)*base67 + (192627758798469611/429625000000000000000000000000000 : ℝ)*base70 + (2393600339743719611/429625000000000000000000000000000 : ℝ)*base72 + (132188019312939/17185000000000000000000000000 : ℝ)*base73 + (1934931102279344611/429625000000000000000000000000000 : ℝ)*base76 + (1533908095851780389/429625000000000000000000000000000 : ℝ)*base77 + (3934768496164094611/429625000000000000000000000000000 : ℝ)*base80 + (28192789654597/8592500000000000000000000000 : ℝ)*base81 + (4766961/1250000000000000000000 : ℝ)*base89 + (4766961/1250000000000000000000 : ℝ)*base91 + (4766961/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (406718557590076831480682211/42962500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1614498783/100000000000000 : ℝ)*(base19) + (880276177/50000000000000 : ℝ)*(base23) + (20351599/10000000000000 : ℝ)*(upper3) + (17476981/25000000000000 : ℝ)*(lower4) + (171884473/100000000000000 : ℝ)*(upper5) + (917312243716221/20000000000000 : ℝ)*(major0) + (917312243716221/20000000000000 : ℝ)*(major1) + (917312243716221/20000000000000 : ℝ)*(major2) + (33153458589/100000000000000 : ℝ)*(sp1) + (37831550719/100000000000000 : ℝ)*(sp2) + (6287043249758029/100000000000000 : ℝ)*(sp4) + (392938030112541/6250000000000 : ℝ)*(sp5) + (1571750914413739/25000000000000 : ℝ)*(sp6) + (115443154873731/4000000000000 : ℝ)*(sp7) + (115443154873731/4000000000000 : ℝ)*(f.failure) + (6287043249758029/100000000000000 : ℝ)*(f.sum) + (4625188008713/1718500000000000000000000000 : ℝ)*base65 + (666416462327314263/171850000000000000000000000000000 : ℝ)*base68 + (569617220171614263/171850000000000000000000000000000 : ℝ)*base70 + (220825560700885737/171850000000000000000000000000000 : ℝ)*base71 + (273398928759/171850000000000000000000000 : ℝ)*base74 + (290012401145564263/171850000000000000000000000000000 : ℝ)*base76 + (862583196942564263/171850000000000000000000000000000 : ℝ)*base78 + (1650395794317864263/171850000000000000000000000000000 : ℝ)*base80 + (1979037820793/3437000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (32211/200000000000000000000 : ℝ)*base89 + (32211/200000000000000000000 : ℝ)*base91 + (32211/200000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1448_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79460081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1849/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2271/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (91/800 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1448_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1448_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79460081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15743/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10467/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (91/800 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1448_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1448_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1448_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (551/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79460081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15743/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10467/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (91/800 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1448_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

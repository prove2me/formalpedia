-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1332_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:02:33.637989+00:00
-- url     : https://prove2.me/submissions/4d6321ba-d557-4d1f-bfe3-249d0e548047

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
theorem support_rectangle_w1332_s6_0 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-5131587/25000000 : ℝ)*x 0 + (16916381/31250000 : ℝ)*x 1 + (5244281353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5131587/25000000 : ℝ)^1073 ≤ (3124427225863/25000000000000 : ℝ)^817 := by
    have hnat : (5131587 : ℕ)^1073*25000000000000^817 ≤ 3124427225863^817*25000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5131587 25000000 3124427225863 25000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16916381/31250000 : ℝ)^1073 ≤ (44662043621541/100000000000000 : ℝ)^817 := by
    have hnat : (16916381 : ℕ)^1073*100000000000000^817 ≤ 44662043621541^817*31250000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16916381 31250000 44662043621541 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244281353/10000000000 : ℝ)^1073 ≤ (21420123727373/50000000000000 : ℝ)^817 := by
    have hnat : (5244281353 : ℕ)^1073*50000000000000^817 ≤ 21420123727373^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244281353 10000000000 21420123727373 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5131587/25000000 : ℝ), (16916381/31250000 : ℝ), (5244281353/10000000000 : ℝ)] ![(3124427225863/25000000000000 : ℝ), (44662043621541/100000000000000 : ℝ), (21420123727373/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5131587/25000000 : ℝ)|^1073 ≤ (3124427225863/25000000000000 : ℝ)^817
        have hw : |(-5131587/25000000 : ℝ)|=(5131587/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(16916381/31250000 : ℝ)|^1073 ≤ (44662043621541/100000000000000 : ℝ)^817
        have hw : |(16916381/31250000 : ℝ)|=(16916381/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244281353/10000000000 : ℝ)|^1073 ≤ (21420123727373/50000000000000 : ℝ)^817
        have hw : |(5244281353/10000000000 : ℝ)|=(5244281353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s6_1 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5349173869/10000000000 : ℝ)*x 0 + (-1069364867/5000000000 : ℝ)*x 1 + (2622140699/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349173869/10000000000 : ℝ)^1073 ≤ (687017332343/1562500000000 : ℝ)^817 := by
    have hnat : (5349173869 : ℕ)^1073*1562500000000^817 ≤ 687017332343^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349173869 10000000000 687017332343 1562500000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1069364867/5000000000 : ℝ)^1073 ≤ (6595321387373/50000000000000 : ℝ)^817 := by
    have hnat : (1069364867 : ℕ)^1073*50000000000000^817 ≤ 6595321387373^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069364867 5000000000 6595321387373 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622140699/5000000000 : ℝ)^1073 ≤ (21420123968767/50000000000000 : ℝ)^817 := by
    have hnat : (2622140699 : ℕ)^1073*50000000000000^817 ≤ 21420123968767^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622140699 5000000000 21420123968767 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349173869/10000000000 : ℝ), (-1069364867/5000000000 : ℝ), (2622140699/5000000000 : ℝ)] ![(687017332343/1562500000000 : ℝ), (6595321387373/50000000000000 : ℝ), (21420123968767/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349173869/10000000000 : ℝ)|^1073 ≤ (687017332343/1562500000000 : ℝ)^817
        have hw : |(5349173869/10000000000 : ℝ)|=(5349173869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1069364867/5000000000 : ℝ)|^1073 ≤ (6595321387373/50000000000000 : ℝ)^817
        have hw : |(-1069364867/5000000000 : ℝ)|=(1069364867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622140699/5000000000 : ℝ)|^1073 ≤ (21420123968767/50000000000000 : ℝ)^817
        have hw : |(2622140699/5000000000 : ℝ)|=(2622140699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s6_2 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (267458693/500000000 : ℝ)*x 0 + (5244281387/10000000000 : ℝ)*x 1 + (-2138729761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267458693/500000000 : ℝ)^1073 ≤ (43969109172793/100000000000000 : ℝ)^817 := by
    have hnat : (267458693 : ℕ)^1073*100000000000000^817 ≤ 43969109172793^817*500000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267458693 500000000 43969109172793 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244281387/10000000000 : ℝ)^1073 ≤ (42840247819519/100000000000000 : ℝ)^817 := by
    have hnat : (5244281387 : ℕ)^1073*100000000000000^817 ≤ 42840247819519^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244281387 10000000000 42840247819519 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2138729761/10000000000 : ℝ)^1073 ≤ (13190642993447/100000000000000 : ℝ)^817 := by
    have hnat : (2138729761 : ℕ)^1073*100000000000000^817 ≤ 13190642993447^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138729761 10000000000 13190642993447 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267458693/500000000 : ℝ), (5244281387/10000000000 : ℝ), (-2138729761/10000000000 : ℝ)] ![(43969109172793/100000000000000 : ℝ), (42840247819519/100000000000000 : ℝ), (13190642993447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267458693/500000000 : ℝ)|^1073 ≤ (43969109172793/100000000000000 : ℝ)^817
        have hw : |(267458693/500000000 : ℝ)|=(267458693/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244281387/10000000000 : ℝ)|^1073 ≤ (42840247819519/100000000000000 : ℝ)^817
        have hw : |(5244281387/10000000000 : ℝ)|=(5244281387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2138729761/10000000000 : ℝ)|^1073 ≤ (13190642993447/100000000000000 : ℝ)^817
        have hw : |(-2138729761/10000000000 : ℝ)|=(2138729761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s6_3 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (865847779/2000000000 : ℝ)*x 0 + (64942559/156250000 : ℝ)*x 1 + (2254446371/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (865847779/2000000000 : ℝ)^1073 ≤ (33303064941227/100000000000000 : ℝ)^817 := by
    have hnat : (865847779 : ℕ)^1073*100000000000000^817 ≤ 33303064941227^817*2000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865847779 2000000000 33303064941227 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (64942559/156250000 : ℝ)^1073 ≤ (31567137116859/100000000000000 : ℝ)^817 := by
    have hnat : (64942559 : ℕ)^1073*100000000000000^817 ≤ 31567137116859^817*156250000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64942559 156250000 31567137116859 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2254446371/5000000000 : ℝ)^1073 ≤ (109780618523/312500000000 : ℝ)^817 := by
    have hnat : (2254446371 : ℕ)^1073*312500000000^817 ≤ 109780618523^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254446371 5000000000 109780618523 312500000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(865847779/2000000000 : ℝ), (64942559/156250000 : ℝ), (2254446371/5000000000 : ℝ)] ![(33303064941227/100000000000000 : ℝ), (31567137116859/100000000000000 : ℝ), (109780618523/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(865847779/2000000000 : ℝ)|^1073 ≤ (33303064941227/100000000000000 : ℝ)^817
        have hw : |(865847779/2000000000 : ℝ)|=(865847779/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(64942559/156250000 : ℝ)|^1073 ≤ (31567137116859/100000000000000 : ℝ)^817
        have hw : |(64942559/156250000 : ℝ)|=(64942559/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2254446371/5000000000 : ℝ)|^1073 ≤ (109780618523/312500000000 : ℝ)^817
        have hw : |(2254446371/5000000000 : ℝ)|=(2254446371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s6_4 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2052647081/10000000000 : ℝ)*x 0 + (2622442991/5000000000 : ℝ)*x 1 + (1082526837/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2052647081/10000000000 : ℝ)^1073 ≤ (3124451776939/25000000000000 : ℝ)^817 := by
    have hnat : (2052647081 : ℕ)^1073*25000000000000^817 ≤ 3124451776939^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2052647081 10000000000 3124451776939 25000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622442991/5000000000 : ℝ)^1073 ≤ (10711683600889/25000000000000 : ℝ)^817 := by
    have hnat : (2622442991 : ℕ)^1073*25000000000000^817 ≤ 10711683600889^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622442991 5000000000 10711683600889 25000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082526837/2000000000 : ℝ)^1073 ≤ (11163864618803/25000000000000 : ℝ)^817 := by
    have hnat : (1082526837 : ℕ)^1073*25000000000000^817 ≤ 11163864618803^817*2000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082526837 2000000000 11163864618803 25000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2052647081/10000000000 : ℝ), (2622442991/5000000000 : ℝ), (1082526837/2000000000 : ℝ)] ![(3124451776939/25000000000000 : ℝ), (10711683600889/25000000000000 : ℝ), (11163864618803/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2052647081/10000000000 : ℝ)|^1073 ≤ (3124451776939/25000000000000 : ℝ)^817
        have hw : |(-2052647081/10000000000 : ℝ)|=(2052647081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622442991/5000000000 : ℝ)|^1073 ≤ (10711683600889/25000000000000 : ℝ)^817
        have hw : |(2622442991/5000000000 : ℝ)|=(2622442991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082526837/2000000000 : ℝ)|^1073 ≤ (11163864618803/25000000000000 : ℝ)^817
        have hw : |(1082526837/2000000000 : ℝ)|=(1082526837/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s6_5 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2652852019/5000000000 : ℝ)*x 0 + (-246297119/1250000000 : ℝ)*x 1 + (1082526837/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652852019/5000000000 : ℝ)^1073 ≤ (21750216885339/50000000000000 : ℝ)^817 := by
    have hnat : (2652852019 : ℕ)^1073*50000000000000^817 ≤ 21750216885339^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652852019 5000000000 21750216885339 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (246297119/1250000000 : ℝ)^1073 ≤ (11844107730139/100000000000000 : ℝ)^817 := by
    have hnat : (246297119 : ℕ)^1073*100000000000000^817 ≤ 11844107730139^817*1250000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246297119 1250000000 11844107730139 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082526837/2000000000 : ℝ)^1073 ≤ (11163864618803/25000000000000 : ℝ)^817 := by
    have hnat : (1082526837 : ℕ)^1073*25000000000000^817 ≤ 11163864618803^817*2000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082526837 2000000000 11163864618803 25000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652852019/5000000000 : ℝ), (-246297119/1250000000 : ℝ), (1082526837/2000000000 : ℝ)] ![(21750216885339/50000000000000 : ℝ), (11844107730139/100000000000000 : ℝ), (11163864618803/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652852019/5000000000 : ℝ)|^1073 ≤ (21750216885339/50000000000000 : ℝ)^817
        have hw : |(2652852019/5000000000 : ℝ)|=(2652852019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-246297119/1250000000 : ℝ)|^1073 ≤ (11844107730139/100000000000000 : ℝ)^817
        have hw : |(-246297119/1250000000 : ℝ)|=(246297119/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082526837/2000000000 : ℝ)|^1073 ≤ (11163864618803/25000000000000 : ℝ)^817
        have hw : |(1082526837/2000000000 : ℝ)|=(1082526837/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s6_6 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2652852019/5000000000 : ℝ)*x 0 + (1082526837/2000000000 : ℝ)*x 1 + (-1970376953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652852019/5000000000 : ℝ)^1073 ≤ (21750216885339/50000000000000 : ℝ)^817 := by
    have hnat : (2652852019 : ℕ)^1073*50000000000000^817 ≤ 21750216885339^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652852019 5000000000 21750216885339 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082526837/2000000000 : ℝ)^1073 ≤ (11163864618803/25000000000000 : ℝ)^817 := by
    have hnat : (1082526837 : ℕ)^1073*25000000000000^817 ≤ 11163864618803^817*2000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082526837 2000000000 11163864618803 25000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1970376953/10000000000 : ℝ)^1073 ≤ (5922053869017/50000000000000 : ℝ)^817 := by
    have hnat : (1970376953 : ℕ)^1073*50000000000000^817 ≤ 5922053869017^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1970376953 10000000000 5922053869017 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652852019/5000000000 : ℝ), (1082526837/2000000000 : ℝ), (-1970376953/10000000000 : ℝ)] ![(21750216885339/50000000000000 : ℝ), (11163864618803/25000000000000 : ℝ), (5922053869017/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652852019/5000000000 : ℝ)|^1073 ≤ (21750216885339/50000000000000 : ℝ)^817
        have hw : |(2652852019/5000000000 : ℝ)|=(2652852019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082526837/2000000000 : ℝ)|^1073 ≤ (11163864618803/25000000000000 : ℝ)^817
        have hw : |(1082526837/2000000000 : ℝ)|=(1082526837/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1970376953/10000000000 : ℝ)|^1073 ≤ (5922053869017/50000000000000 : ℝ)^817
        have hw : |(-1970376953/10000000000 : ℝ)|=(1970376953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s6_7 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (108231613/250000000 : ℝ)*x 0 + (4507631141/10000000000 : ℝ)*x 1 + (831518381/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108231613/250000000 : ℝ)^1073 ≤ (33303323830821/100000000000000 : ℝ)^817 := by
    have hnat : (108231613 : ℕ)^1073*100000000000000^817 ≤ 33303323830821^817*250000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108231613 250000000 33303323830821 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4507631141/10000000000 : ℝ)^1073 ≤ (17558444555873/50000000000000 : ℝ)^817 := by
    have hnat : (4507631141 : ℕ)^1073*50000000000000^817 ≤ 17558444555873^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507631141 10000000000 17558444555873 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (831518381/2000000000 : ℝ)^1073 ≤ (15789893517029/50000000000000 : ℝ)^817 := by
    have hnat : (831518381 : ℕ)^1073*50000000000000^817 ≤ 15789893517029^817*2000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      831518381 2000000000 15789893517029 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(108231613/250000000 : ℝ), (4507631141/10000000000 : ℝ), (831518381/2000000000 : ℝ)] ![(33303323830821/100000000000000 : ℝ), (17558444555873/50000000000000 : ℝ), (15789893517029/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(108231613/250000000 : ℝ)|^1073 ≤ (33303323830821/100000000000000 : ℝ)^817
        have hw : |(108231613/250000000 : ℝ)|=(108231613/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4507631141/10000000000 : ℝ)|^1073 ≤ (17558444555873/50000000000000 : ℝ)^817
        have hw : |(4507631141/10000000000 : ℝ)|=(4507631141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(831518381/2000000000 : ℝ)|^1073 ≤ (15789893517029/50000000000000 : ℝ)^817
        have hw : |(831518381/2000000000 : ℝ)|=(831518381/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1332_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (120574/78125 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1471/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11117/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (89/800 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14701/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1471/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11117/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1471/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11117/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1471/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11117/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1471/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11117/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1471/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11117/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1471/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11117/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11117/100000 : ℝ) ^ (4291/1024 : ℝ) ≤ (502629697355657/5000000000000000000 : ℝ) := by
    have hpowers : (11117/100000 : ℝ)^4291 ≤ (502629697355657/5000000000000000000 : ℝ)^1024 := by
      have hnat : (11117 : ℕ)^4291*5000000000000000000^1024 ≤ 502629697355657^1024*100000^4291 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11117 100000 502629697355657 5000000000000000000 4291 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11117/100000 : ℝ)) (X := (502629697355657/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1471/10000 : ℝ) ^ (4291/1024 : ℝ) ≤ (32504196312900497/100000000000000000000 : ℝ) := by
    have hpowers : (1471/10000 : ℝ)^4291 ≤ (32504196312900497/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1471 : ℕ)^4291*100000000000000000000^1024 ≤ 32504196312900497^1024*10000^4291 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1471 10000 32504196312900497 100000000000000000000 4291 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1471/10000 : ℝ)) (X := (32504196312900497/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500502629697355657/2500000000000000000 : ℝ) ≤ (2000095950300059/2000000000000000 : ℝ) ^ (4291/1024 : ℝ) := by
    have hpowers : (2500502629697355657/2500000000000000000 : ℝ)^1024 ≤ (2000095950300059/2000000000000000 : ℝ)^4291 := by
      have hnat : (2500502629697355657 : ℕ)^1024*2000000000000000^4291 ≤ 2000095950300059^4291*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500502629697355657 2500000000000000000 2000095950300059 2000000000000000 1024 4291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000095950300059/2000000000000000 : ℝ)) (X := (2500502629697355657/2500000000000000000 : ℝ)) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100042556790260013637/100000000000000000000 : ℝ) ≤ (2500253851637693/2500000000000000 : ℝ) ^ (4291/1024 : ℝ) := by
    have hpowers : (100042556790260013637/100000000000000000000 : ℝ)^1024 ≤ (2500253851637693/2500000000000000 : ℝ)^4291 := by
      have hnat : (100042556790260013637 : ℕ)^1024*2500000000000000^4291 ≤ 2500253851637693^4291*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100042556790260013637 100000000000000000000 2500253851637693 2500000000000000 1024 4291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500253851637693/2500000000000000 : ℝ)) (X := (100042556790260013637/100000000000000000000 : ℝ)) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032504196312900497/50000000000000000000 : ℝ) ≤ (10001551061601249/10000000000000000 : ℝ) ^ (4291/1024 : ℝ) := by
    have hpowers : (50032504196312900497/50000000000000000000 : ℝ)^1024 ≤ (10001551061601249/10000000000000000 : ℝ)^4291 := by
      have hnat : (50032504196312900497 : ℕ)^1024*10000000000000000^4291 ≤ 10001551061601249^4291*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032504196312900497 50000000000000000000 10001551061601249 10000000000000000 1024 4291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001551061601249/10000000000000000 : ℝ)) (X := (50032504196312900497/50000000000000000000 : ℝ)) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(502629697355657/5000000000000000000 : ℝ) ≤ ((35919813992748254317/35930000000000000000 : ℝ)+2*(535655050477/359300000000000 : ℝ)*(11117/100000 : ℝ))^(4291/1024 : ℝ) := by
    rw [show (35919813992748254317/35930000000000000000 : ℝ)+2*(535655050477/359300000000000 : ℝ)*(11117/100000 : ℝ)=(2000095950300059/2000000000000000 : ℝ) by norm_num, show 1+2*(502629697355657/5000000000000000000 : ℝ)=(2500502629697355657/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32504196312900497/100000000000000000000 : ℝ)+(502629697355657/5000000000000000000 : ℝ) ≤ ((35919813992748254317/35930000000000000000 : ℝ)+(535655050477/359300000000000 : ℝ)*((1471/10000 : ℝ)+(11117/100000 : ℝ)))^(4291/1024 : ℝ) := by
    rw [show (35919813992748254317/35930000000000000000 : ℝ)+(535655050477/359300000000000 : ℝ)*((1471/10000 : ℝ)+(11117/100000 : ℝ))=(2500253851637693/2500000000000000 : ℝ) by norm_num, show 1+(32504196312900497/100000000000000000000 : ℝ)+(502629697355657/5000000000000000000 : ℝ)=(100042556790260013637/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32504196312900497/100000000000000000000 : ℝ) ≤ ((35919813992748254317/35930000000000000000 : ℝ)+2*(535655050477/359300000000000 : ℝ)*(1471/10000 : ℝ))^(4291/1024 : ℝ) := by
    rw [show (35919813992748254317/35930000000000000000 : ℝ)+2*(535655050477/359300000000000 : ℝ)*(1471/10000 : ℝ)=(10001551061601249/10000000000000000 : ℝ) by norm_num, show 1+2*(32504196312900497/100000000000000000000 : ℝ)=(50032504196312900497/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (35919813992748254317/35930000000000000000 : ℝ)*(X 1 0+X 2 0)+(535655050477/359300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4291/1024 : ℝ)) (lo := (11117/100000 : ℝ)) (hi := (1471/10000 : ℝ)) (c := (35919813992748254317/35930000000000000000 : ℝ)) (alpha := (535655050477/359300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (35919813992748254317/35930000000000000000 : ℝ)*(X 0 1+X 2 1)+(535655050477/359300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4291/1024 : ℝ)) (lo := (11117/100000 : ℝ)) (hi := (1471/10000 : ℝ)) (c := (35919813992748254317/35930000000000000000 : ℝ)) (alpha := (535655050477/359300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (35919813992748254317/35930000000000000000 : ℝ)*(X 0 2+X 1 2)+(535655050477/359300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4291/1024 : ℝ)) (lo := (11117/100000 : ℝ)) (hi := (1471/10000 : ℝ)) (c := (35919813992748254317/35930000000000000000 : ℝ)) (alpha := (535655050477/359300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-5131587/25000000 : ℝ)*X 0 0+(16916381/31250000 : ℝ)*X 0 1+(5244281353/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349173869/10000000000 : ℝ)*X 1 0+(-1069364867/5000000000 : ℝ)*X 1 1+(2622140699/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267458693/500000000 : ℝ)*X 2 0+(5244281387/10000000000 : ℝ)*X 2 1+(-2138729761/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((865847779/2000000000 : ℝ)*X 0 0+(64942559/156250000 : ℝ)*X 0 1+(2254446371/5000000000 : ℝ)*X 0 2+(865847779/2000000000 : ℝ)*X 1 0+(64942559/156250000 : ℝ)*X 1 1+(2254446371/5000000000 : ℝ)*X 1 2+(865847779/2000000000 : ℝ)*X 2 0+(64942559/156250000 : ℝ)*X 2 1+(2254446371/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2052647081/10000000000 : ℝ)*X 0 0+(2622442991/5000000000 : ℝ)*X 0 1+(1082526837/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652852019/5000000000 : ℝ)*X 1 0+(-246297119/1250000000 : ℝ)*X 1 1+(1082526837/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652852019/5000000000 : ℝ)*X 2 0+(1082526837/2000000000 : ℝ)*X 2 1+(-1970376953/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((108231613/250000000 : ℝ)*X 0 0+(4507631141/10000000000 : ℝ)*X 0 1+(831518381/2000000000 : ℝ)*X 0 2+(108231613/250000000 : ℝ)*X 1 0+(4507631141/10000000000 : ℝ)*X 1 1+(831518381/2000000000 : ℝ)*X 1 2+(108231613/250000000 : ℝ)*X 2 0+(4507631141/10000000000 : ℝ)*X 2 1+(831518381/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3299864299184334651100436631/898250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (730696799/100000000000000 : ℝ)*(base19) + (673242543/100000000000000 : ℝ)*(base23) + (5081313/20000000000000 : ℝ)*(lower2) + (23593601/20000000000000 : ℝ)*(upper3) + (24233347/50000000000000 : ℝ)*(upper5) + (4377456292332319/100000000000000 : ℝ)*(major0) + (4377456292332319/100000000000000 : ℝ)*(major1) + (4377456292332319/100000000000000 : ℝ)*(major2) + (2959278981102869/50000000000000 : ℝ)*(sp0) + (739821555929273/12500000000000 : ℝ)*(sp1) + (5918572504888439/100000000000000 : ℝ)*(sp2) + (1418165641982533/50000000000000 : ℝ)*(sp3) + (3043185049/20000000000000 : ℝ)*(sp4) + (12500177/156250000000 : ℝ)*(sp7) + (1418169642039173/50000000000000 : ℝ)*(f.failure) + (5918573178130983/100000000000000 : ℝ)*(f.sum) + (10649921103019/8982500000000000000000000000 : ℝ)*base65 + (21497861380428671123/3593000000000000000000000000000000 : ℝ)*base67 + (755524120816328877/3593000000000000000000000000000000 : ℝ)*base70 + (15258648067668671123/3593000000000000000000000000000000 : ℝ)*base71 + (2139258841437/17965000000000000000000000000 : ℝ)*base74 + (13810478502134671123/3593000000000000000000000000000000 : ℝ)*base75 + (26163882215776671123/3593000000000000000000000000000000 : ℝ)*base77 + (21883633372029671123/3593000000000000000000000000000000 : ℝ)*base79 + (37985743118791/8982500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (68729/7812500000000000000 : ℝ)*base89 + (68729/7812500000000000000 : ℝ)*base91 + (68729/7812500000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3376700778888594564982749321/898250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (165344253/25000000000000 : ℝ)*(base19) + (358721083/50000000000000 : ℝ)*(base23) + (19232739/25000000000000 : ℝ)*(upper3) + (127541/500000000000 : ℝ)*(lower4) + (38761667/50000000000000 : ℝ)*(upper5) + (2204534435130129/50000000000000 : ℝ)*(major0) + (2204534435130129/50000000000000 : ℝ)*(major1) + (2204534435130129/50000000000000 : ℝ)*(major2) + (13451922953/100000000000000 : ℝ)*(sp1) + (1442692669/10000000000000 : ℝ)*(sp2) + (5961315203341631/100000000000000 : ℝ)*(sp4) + (5961301090041667/100000000000000 : ℝ)*(sp5) + (238452002358911/4000000000000 : ℝ)*(sp6) + (2856822411872233/100000000000000 : ℝ)*(sp7) + (2856822411872233/100000000000000 : ℝ)*(f.failure) + (5961315203341631/100000000000000 : ℝ)*(f.sum) + (37448100797219/17965000000000000000000000000 : ℝ)*base66 + (744257240366816893/1796500000000000000000000000000000 : ℝ)*base67 + (3438722530765683107/1796500000000000000000000000000000 : ℝ)*base70 + (4369207691054816893/1796500000000000000000000000000000 : ℝ)*base71 + (115905213810089/17965000000000000000000000000 : ℝ)*base74 + (41958303541626683107/1796500000000000000000000000000000 : ℝ)*base76 + (6965469344669316893/1796500000000000000000000000000000 : ℝ)*base77 + (18815402072137316893/1796500000000000000000000000000000 : ℝ)*base79 + (6599958309967/8982500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (8627/1953125000000000000 : ℝ)*base90 + (8627/1953125000000000000 : ℝ)*base92 + (8627/1953125000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1332_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (120574/78125 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1471/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11117/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (89/800 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14701/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1332_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1332_s7_0 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-410528887/2000000000 : ℝ)*x 0 + (5413169109/10000000000 : ℝ)*x 1 + (524434771/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (410528887/2000000000 : ℝ)^1073 ≤ (2499557189831/20000000000000 : ℝ)^817 := by
    have hnat : (410528887 : ℕ)^1073*20000000000000^817 ≤ 2499557189831^817*2000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410528887 2000000000 2499557189831 20000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413169109/10000000000 : ℝ)^1073 ≤ (44661254661693/100000000000000 : ℝ)^817 := by
    have hnat : (5413169109 : ℕ)^1073*100000000000000^817 ≤ 44661254661693^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413169109 10000000000 44661254661693 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524434771/1000000000 : ℝ)^1073 ≤ (856819187497/2000000000000 : ℝ)^817 := by
    have hnat : (524434771 : ℕ)^1073*2000000000000^817 ≤ 856819187497^817*1000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524434771 1000000000 856819187497 2000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-410528887/2000000000 : ℝ), (5413169109/10000000000 : ℝ), (524434771/1000000000 : ℝ)] ![(2499557189831/20000000000000 : ℝ), (44661254661693/100000000000000 : ℝ), (856819187497/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-410528887/2000000000 : ℝ)|^1073 ≤ (2499557189831/20000000000000 : ℝ)^817
        have hw : |(-410528887/2000000000 : ℝ)|=(410528887/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413169109/10000000000 : ℝ)|^1073 ≤ (44661254661693/100000000000000 : ℝ)^817
        have hw : |(5413169109/10000000000 : ℝ)|=(5413169109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524434771/1000000000 : ℝ)|^1073 ≤ (856819187497/2000000000000 : ℝ)^817
        have hw : |(524434771/1000000000 : ℝ)|=(524434771/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s7_1 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5349154901/10000000000 : ℝ)*x 0 + (-1069333593/5000000000 : ℝ)*x 1 + (5244347707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349154901/10000000000 : ℝ)^1073 ≤ (1758756180119/4000000000000 : ℝ)^817 := by
    have hnat : (5349154901 : ℕ)^1073*4000000000000^817 ≤ 1758756180119^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349154901 10000000000 1758756180119 4000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1069333593/5000000000 : ℝ)^1073 ≤ (164876701689/1250000000000 : ℝ)^817 := by
    have hnat : (1069333593 : ℕ)^1073*1250000000000^817 ≤ 164876701689^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069333593 5000000000 164876701689 1250000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244347707/10000000000 : ℝ)^1073 ≤ (5355119917833/12500000000000 : ℝ)^817 := by
    have hnat : (5244347707 : ℕ)^1073*12500000000000^817 ≤ 5355119917833^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244347707 10000000000 5355119917833 12500000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349154901/10000000000 : ℝ), (-1069333593/5000000000 : ℝ), (5244347707/10000000000 : ℝ)] ![(1758756180119/4000000000000 : ℝ), (164876701689/1250000000000 : ℝ), (5355119917833/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349154901/10000000000 : ℝ)|^1073 ≤ (1758756180119/4000000000000 : ℝ)^817
        have hw : |(5349154901/10000000000 : ℝ)|=(5349154901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1069333593/5000000000 : ℝ)|^1073 ≤ (164876701689/1250000000000 : ℝ)^817
        have hw : |(-1069333593/5000000000 : ℝ)|=(1069333593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244347707/10000000000 : ℝ)|^1073 ≤ (5355119917833/12500000000000 : ℝ)^817
        have hw : |(5244347707/10000000000 : ℝ)|=(5244347707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s7_2 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5349154899/10000000000 : ℝ)*x 0 + (5244347719/10000000000 : ℝ)*x 1 + (-1069333587/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349154899/10000000000 : ℝ)^1073 ≤ (5496113060173/12500000000000 : ℝ)^817 := by
    have hnat : (5349154899 : ℕ)^1073*12500000000000^817 ≤ 5496113060173^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349154899 10000000000 5496113060173 12500000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244347719/10000000000 : ℝ)^1073 ≤ (2677559966963/6250000000000 : ℝ)^817 := by
    have hnat : (5244347719 : ℕ)^1073*6250000000000^817 ≤ 2677559966963^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244347719 10000000000 2677559966963 6250000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1069333587/5000000000 : ℝ)^1073 ≤ (82438350237/625000000000 : ℝ)^817 := by
    have hnat : (1069333587 : ℕ)^1073*625000000000^817 ≤ 82438350237^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069333587 5000000000 82438350237 625000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349154899/10000000000 : ℝ), (5244347719/10000000000 : ℝ), (-1069333587/5000000000 : ℝ)] ![(5496113060173/12500000000000 : ℝ), (2677559966963/6250000000000 : ℝ), (82438350237/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349154899/10000000000 : ℝ)|^1073 ≤ (5496113060173/12500000000000 : ℝ)^817
        have hw : |(5349154899/10000000000 : ℝ)|=(5349154899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244347719/10000000000 : ℝ)|^1073 ≤ (2677559966963/6250000000000 : ℝ)^817
        have hw : |(5244347719/10000000000 : ℝ)|=(5244347719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1069333587/5000000000 : ℝ)|^1073 ≤ (82438350237/625000000000 : ℝ)^817
        have hw : |(-1069333587/5000000000 : ℝ)|=(1069333587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s7_3 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4329243791/10000000000 : ℝ)*x 0 + (207823417/500000000 : ℝ)*x 1 + (563593373/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4329243791/10000000000 : ℝ)^1073 ≤ (416288930069/1250000000000 : ℝ)^817 := by
    have hnat : (4329243791 : ℕ)^1073*1250000000000^817 ≤ 416288930069^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4329243791 10000000000 416288930069 1250000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207823417/500000000 : ℝ)^1073 ≤ (24662952437/78125000000 : ℝ)^817 := by
    have hnat : (207823417 : ℕ)^1073*78125000000^817 ≤ 24662952437^817*500000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207823417 500000000 24662952437 78125000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (563593373/1250000000 : ℝ)^1073 ≤ (109775957689/312500000000 : ℝ)^817 := by
    have hnat : (563593373 : ℕ)^1073*312500000000^817 ≤ 109775957689^817*1250000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563593373 1250000000 109775957689 312500000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4329243791/10000000000 : ℝ), (207823417/500000000 : ℝ), (563593373/1250000000 : ℝ)] ![(416288930069/1250000000000 : ℝ), (24662952437/78125000000 : ℝ), (109775957689/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4329243791/10000000000 : ℝ)|^1073 ≤ (416288930069/1250000000000 : ℝ)^817
        have hw : |(4329243791/10000000000 : ℝ)|=(4329243791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(207823417/500000000 : ℝ)|^1073 ≤ (24662952437/78125000000 : ℝ)^817
        have hw : |(207823417/500000000 : ℝ)|=(207823417/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(563593373/1250000000 : ℝ)|^1073 ≤ (109775957689/312500000000 : ℝ)^817
        have hw : |(563593373/1250000000 : ℝ)|=(563593373/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s7_4 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2052657001/10000000000 : ℝ)*x 0 + (2622475551/5000000000 : ℝ)*x 1 + (5412562383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2052657001/10000000000 : ℝ)^1073 ≤ (2499577286519/20000000000000 : ℝ)^817 := by
    have hnat : (2052657001 : ℕ)^1073*20000000000000^817 ≤ 2499577286519^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2052657001 10000000000 2499577286519 20000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622475551/5000000000 : ℝ)^1073 ≤ (42847433077549/100000000000000 : ℝ)^817 := by
    have hnat : (2622475551 : ℕ)^1073*100000000000000^817 ≤ 42847433077549^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622475551 5000000000 42847433077549 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412562383/10000000000 : ℝ)^1073 ≤ (22327340237979/50000000000000 : ℝ)^817 := by
    have hnat : (5412562383 : ℕ)^1073*50000000000000^817 ≤ 22327340237979^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412562383 10000000000 22327340237979 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2052657001/10000000000 : ℝ), (2622475551/5000000000 : ℝ), (5412562383/10000000000 : ℝ)] ![(2499577286519/20000000000000 : ℝ), (42847433077549/100000000000000 : ℝ), (22327340237979/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2052657001/10000000000 : ℝ)|^1073 ≤ (2499577286519/20000000000000 : ℝ)^817
        have hw : |(-2052657001/10000000000 : ℝ)|=(2052657001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622475551/5000000000 : ℝ)|^1073 ≤ (42847433077549/100000000000000 : ℝ)^817
        have hw : |(2622475551/5000000000 : ℝ)|=(2622475551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412562383/10000000000 : ℝ)|^1073 ≤ (22327340237979/50000000000000 : ℝ)^817
        have hw : |(5412562383/10000000000 : ℝ)|=(5412562383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s7_5 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305721217/10000000000 : ℝ)*x 0 + (-394090457/2000000000 : ℝ)*x 1 + (2706281113/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305721217/10000000000 : ℝ)^1073 ≤ (43500618751341/100000000000000 : ℝ)^817 := by
    have hnat : (5305721217 : ℕ)^1073*100000000000000^817 ≤ 43500618751341^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305721217 10000000000 43500618751341 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (394090457/2000000000 : ℝ)^1073 ≤ (11844702458377/100000000000000 : ℝ)^817 := by
    have hnat : (394090457 : ℕ)^1073*100000000000000^817 ≤ 11844702458377^817*2000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394090457 2000000000 11844702458377 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706281113/5000000000 : ℝ)^1073 ≤ (44654678774813/100000000000000 : ℝ)^817 := by
    have hnat : (2706281113 : ℕ)^1073*100000000000000^817 ≤ 44654678774813^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706281113 5000000000 44654678774813 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305721217/10000000000 : ℝ), (-394090457/2000000000 : ℝ), (2706281113/5000000000 : ℝ)] ![(43500618751341/100000000000000 : ℝ), (11844702458377/100000000000000 : ℝ), (44654678774813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305721217/10000000000 : ℝ)|^1073 ≤ (43500618751341/100000000000000 : ℝ)^817
        have hw : |(5305721217/10000000000 : ℝ)|=(5305721217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-394090457/2000000000 : ℝ)|^1073 ≤ (11844702458377/100000000000000 : ℝ)^817
        have hw : |(-394090457/2000000000 : ℝ)|=(394090457/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706281113/5000000000 : ℝ)|^1073 ≤ (44654678774813/100000000000000 : ℝ)^817
        have hw : |(2706281113/5000000000 : ℝ)|=(2706281113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s7_6 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1061144243/2000000000 : ℝ)*x 0 + (5412562143/10000000000 : ℝ)*x 1 + (-1970452401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061144243/2000000000 : ℝ)^1073 ≤ (8700123745961/20000000000000 : ℝ)^817 := by
    have hnat : (1061144243 : ℕ)^1073*20000000000000^817 ≤ 8700123745961^817*2000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061144243 2000000000 8700123745961 20000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412562143/10000000000 : ℝ)^1073 ≤ (44654677875481/100000000000000 : ℝ)^817 := by
    have hnat : (5412562143 : ℕ)^1073*100000000000000^817 ≤ 44654677875481^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412562143 10000000000 44654677875481 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1970452401/10000000000 : ℝ)^1073 ≤ (11844703374163/100000000000000 : ℝ)^817 := by
    have hnat : (1970452401 : ℕ)^1073*100000000000000^817 ≤ 11844703374163^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1970452401 10000000000 11844703374163 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061144243/2000000000 : ℝ), (5412562143/10000000000 : ℝ), (-1970452401/10000000000 : ℝ)] ![(8700123745961/20000000000000 : ℝ), (44654677875481/100000000000000 : ℝ), (11844703374163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061144243/2000000000 : ℝ)|^1073 ≤ (8700123745961/20000000000000 : ℝ)^817
        have hw : |(1061144243/2000000000 : ℝ)|=(1061144243/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412562143/10000000000 : ℝ)|^1073 ≤ (44654677875481/100000000000000 : ℝ)^817
        have hw : |(5412562143/10000000000 : ℝ)|=(5412562143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1970452401/10000000000 : ℝ)|^1073 ≤ (11844703374163/100000000000000 : ℝ)^817
        have hw : |(-1970452401/10000000000 : ℝ)|=(1970452401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s7_7 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (21646347/50000000 : ℝ)*x 0 + (4507487607/10000000000 : ℝ)*x 1 + (2078867089/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21646347/50000000 : ℝ)^1073 ≤ (33303373133557/100000000000000 : ℝ)^817 := by
    have hnat : (21646347 : ℕ)^1073*100000000000000^817 ≤ 33303373133557^817*50000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21646347 50000000 33303373133557 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4507487607/10000000000 : ℝ)^1073 ≤ (35115420530587/100000000000000 : ℝ)^817 := by
    have hnat : (4507487607 : ℕ)^1073*100000000000000^817 ≤ 35115420530587^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507487607 10000000000 35115420530587 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2078867089/5000000000 : ℝ)^1073 ≤ (31581206319741/100000000000000 : ℝ)^817 := by
    have hnat : (2078867089 : ℕ)^1073*100000000000000^817 ≤ 31581206319741^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078867089 5000000000 31581206319741 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21646347/50000000 : ℝ), (4507487607/10000000000 : ℝ), (2078867089/5000000000 : ℝ)] ![(33303373133557/100000000000000 : ℝ), (35115420530587/100000000000000 : ℝ), (31581206319741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21646347/50000000 : ℝ)|^1073 ≤ (33303373133557/100000000000000 : ℝ)^817
        have hw : |(21646347/50000000 : ℝ)|=(21646347/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4507487607/10000000000 : ℝ)|^1073 ≤ (35115420530587/100000000000000 : ℝ)^817
        have hw : |(4507487607/10000000000 : ℝ)|=(4507487607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2078867089/5000000000 : ℝ)|^1073 ≤ (31581206319741/100000000000000 : ℝ)^817
        have hw : |(2078867089/5000000000 : ℝ)|=(2078867089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1332_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (120574/78125 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14701/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (89/800 : ℝ)*pair X i i ≤ pair X i h) :
    (5563/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (147/1000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14701/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (89/800 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14701/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (89/800 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14701/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (89/800 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14701/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (89/800 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14701/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (89/800 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14701/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (89/800 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (89/800 : ℝ) ^ (4291/1024 : ℝ) ≤ (10082942473085649/100000000000000000000 : ℝ) := by
    have hpowers : (89/800 : ℝ)^4291 ≤ (10082942473085649/100000000000000000000 : ℝ)^1024 := by
      have hnat : (89 : ℕ)^4291*100000000000000000000^1024 ≤ 10082942473085649^1024*800^4291 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        89 800 10082942473085649 100000000000000000000 4291 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (89/800 : ℝ)) (X := (10082942473085649/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14701/100000 : ℝ) ^ (4291/1024 : ℝ) ≤ (4052617817145947/12500000000000000000 : ℝ) := by
    have hpowers : (14701/100000 : ℝ)^4291 ≤ (4052617817145947/12500000000000000000 : ℝ)^1024 := by
      have hnat : (14701 : ℕ)^4291*12500000000000000000^1024 ≤ 4052617817145947^1024*100000^4291 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14701 100000 4052617817145947 12500000000000000000 4291 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14701/100000 : ℝ)) (X := (4052617817145947/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010082942473085649/50000000000000000000 : ℝ) ≤ (1250060149968341/1250000000000000 : ℝ) ^ (4291/1024 : ℝ) := by
    have hpowers : (50010082942473085649/50000000000000000000 : ℝ)^1024 ≤ (1250060149968341/1250000000000000 : ℝ)^4291 := by
      have hnat : (50010082942473085649 : ℕ)^1024*1250000000000000^4291 ≤ 1250060149968341^4291*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010082942473085649 50000000000000000000 1250060149968341 1250000000000000 1024 4291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250060149968341/1250000000000000 : ℝ)) (X := (50010082942473085649/50000000000000000000 : ℝ)) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001700155400410129/4000000000000000000 : ℝ) ≤ (1250126768054223/1250000000000000 : ℝ) ^ (4291/1024 : ℝ) := by
    have hpowers : (4001700155400410129/4000000000000000000 : ℝ)^1024 ≤ (1250126768054223/1250000000000000 : ℝ)^4291 := by
      have hnat : (4001700155400410129 : ℕ)^1024*1250000000000000^4291 ≤ 1250126768054223^4291*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001700155400410129 4000000000000000000 1250126768054223 1250000000000000 1024 4291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250126768054223/1250000000000000 : ℝ)) (X := (4001700155400410129/4000000000000000000 : ℝ)) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254052617817145947/6250000000000000000 : ℝ) ≤ (250038677228021/250000000000000 : ℝ) ^ (4291/1024 : ℝ) := by
    have hpowers : (6254052617817145947/6250000000000000000 : ℝ)^1024 ≤ (250038677228021/250000000000000 : ℝ)^4291 := by
      have hnat : (6254052617817145947 : ℕ)^1024*250000000000000^4291 ≤ 250038677228021^4291*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254052617817145947 6250000000000000000 250038677228021 250000000000000 1024 4291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250038677228021/250000000000000 : ℝ)) (X := (6254052617817145947/6250000000000000000 : ℝ)) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10082942473085649/100000000000000000000 : ℝ) ≤ ((1117183210968978229/1117500000000000000 : ℝ)+2*(33309042941/22350000000000 : ℝ)*(89/800 : ℝ))^(4291/1024 : ℝ) := by
    rw [show (1117183210968978229/1117500000000000000 : ℝ)+2*(33309042941/22350000000000 : ℝ)*(89/800 : ℝ)=(1250060149968341/1250000000000000 : ℝ) by norm_num, show 1+2*(10082942473085649/100000000000000000000 : ℝ)=(50010082942473085649/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4052617817145947/12500000000000000000 : ℝ)+(10082942473085649/100000000000000000000 : ℝ) ≤ ((1117183210968978229/1117500000000000000 : ℝ)+(33309042941/22350000000000 : ℝ)*((14701/100000 : ℝ)+(89/800 : ℝ)))^(4291/1024 : ℝ) := by
    rw [show (1117183210968978229/1117500000000000000 : ℝ)+(33309042941/22350000000000 : ℝ)*((14701/100000 : ℝ)+(89/800 : ℝ))=(1250126768054223/1250000000000000 : ℝ) by norm_num, show 1+(4052617817145947/12500000000000000000 : ℝ)+(10082942473085649/100000000000000000000 : ℝ)=(4001700155400410129/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4052617817145947/12500000000000000000 : ℝ) ≤ ((1117183210968978229/1117500000000000000 : ℝ)+2*(33309042941/22350000000000 : ℝ)*(14701/100000 : ℝ))^(4291/1024 : ℝ) := by
    rw [show (1117183210968978229/1117500000000000000 : ℝ)+2*(33309042941/22350000000000 : ℝ)*(14701/100000 : ℝ)=(250038677228021/250000000000000 : ℝ) by norm_num, show 1+2*(4052617817145947/12500000000000000000 : ℝ)=(6254052617817145947/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1117183210968978229/1117500000000000000 : ℝ)*(X 1 0+X 2 0)+(33309042941/22350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4291/1024 : ℝ)) (lo := (89/800 : ℝ)) (hi := (14701/100000 : ℝ)) (c := (1117183210968978229/1117500000000000000 : ℝ)) (alpha := (33309042941/22350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1117183210968978229/1117500000000000000 : ℝ)*(X 0 1+X 2 1)+(33309042941/22350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4291/1024 : ℝ)) (lo := (89/800 : ℝ)) (hi := (14701/100000 : ℝ)) (c := (1117183210968978229/1117500000000000000 : ℝ)) (alpha := (33309042941/22350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1117183210968978229/1117500000000000000 : ℝ)*(X 0 2+X 1 2)+(33309042941/22350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4291/1024 : ℝ)) (lo := (89/800 : ℝ)) (hi := (14701/100000 : ℝ)) (c := (1117183210968978229/1117500000000000000 : ℝ)) (alpha := (33309042941/22350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-410528887/2000000000 : ℝ)*X 0 0+(5413169109/10000000000 : ℝ)*X 0 1+(524434771/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349154901/10000000000 : ℝ)*X 1 0+(-1069333593/5000000000 : ℝ)*X 1 1+(5244347707/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349154899/10000000000 : ℝ)*X 2 0+(5244347719/10000000000 : ℝ)*X 2 1+(-1069333587/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4329243791/10000000000 : ℝ)*X 0 0+(207823417/500000000 : ℝ)*X 0 1+(563593373/1250000000 : ℝ)*X 0 2+(4329243791/10000000000 : ℝ)*X 1 0+(207823417/500000000 : ℝ)*X 1 1+(563593373/1250000000 : ℝ)*X 1 2+(4329243791/10000000000 : ℝ)*X 2 0+(207823417/500000000 : ℝ)*X 2 1+(563593373/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2052657001/10000000000 : ℝ)*X 0 0+(2622475551/5000000000 : ℝ)*X 0 1+(5412562383/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305721217/10000000000 : ℝ)*X 1 0+(-394090457/2000000000 : ℝ)*X 1 1+(2706281113/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061144243/2000000000 : ℝ)*X 2 0+(5412562143/10000000000 : ℝ)*X 2 1+(-1970452401/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((21646347/50000000 : ℝ)*X 0 0+(4507487607/10000000000 : ℝ)*X 0 1+(2078867089/5000000000 : ℝ)*X 0 2+(21646347/50000000 : ℝ)*X 1 0+(4507487607/10000000000 : ℝ)*X 1 1+(2078867089/5000000000 : ℝ)*X 1 2+(21646347/50000000 : ℝ)*X 2 0+(4507487607/10000000000 : ℝ)*X 2 1+(2078867089/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (72086483914327849859733361/9312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1467587149/100000000000000 : ℝ)*(base19) + (1377291823/100000000000000 : ℝ)*(base23) + (5889459/12500000000000 : ℝ)*(lower2) + (46254313/25000000000000 : ℝ)*(upper3) + (134847249/100000000000000 : ℝ)*(upper5) + (2190543178763291/50000000000000 : ℝ)*(major0) + (2190543178763291/50000000000000 : ℝ)*(major1) + (2190543178763291/50000000000000 : ℝ)*(major2) + (2961725356941007/50000000000000 : ℝ)*(sp0) + (578464807853/9765625000 : ℝ)*(sp1) + (2961739861355023/50000000000000 : ℝ)*(sp2) + (2838676084705793/100000000000000 : ℝ)*(sp3) + (15193059927/50000000000000 : ℝ)*(sp4) + (15272317813/100000000000000 : ℝ)*(sp7) + (1419345678511803/50000000000000 : ℝ)*(f.failure) + (5923481100001869/100000000000000 : ℝ)*(f.sum) + (20368067799641/2235000000000000000000000000 : ℝ)*base66 + (70423753063066639/55875000000000000000000000000000 : ℝ)*base67 + (553362033257941639/55875000000000000000000000000000 : ℝ)*base69 + (302767400089816639/55875000000000000000000000000000 : ℝ)*base71 + (238865876561/2235000000000000000000000000 : ℝ)*base74 + (412387446372808361/55875000000000000000000000000000 : ℝ)*base76 + (41694858334933361/55875000000000000000000000000000 : ℝ)*base78 + (470399328478066639/55875000000000000000000000000000 : ℝ)*base79 + (2194237015577/1117500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (25547/3906250000000000000 : ℝ)*base89 + (25547/3906250000000000000 : ℝ)*base91 + (25547/3906250000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (56025594322898393509367681/9312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2285530847/100000000000000 : ℝ)*(base19) + (2546702039/100000000000000 : ℝ)*(base23) + (375655097/50000000000000 : ℝ)*(lower1) + (139821391/100000000000000 : ℝ)*(upper2) + (203269809/100000000000000 : ℝ)*(upper3) + (60325561/25000000000000 : ℝ)*(upper5) + (2206318250719211/50000000000000 : ℝ)*(major0) + (2206318250719211/50000000000000 : ℝ)*(major1) + (2206318250719211/50000000000000 : ℝ)*(major2) + (3339049/25000000000000 : ℝ)*(sp1) + (93220918299421/1562500000000 : ℝ)*(sp4) + (2983068236137951/50000000000000 : ℝ)*(sp5) + (1193227244892181/20000000000000 : ℝ)*(sp6) + (2859134031174853/100000000000000 : ℝ)*(sp7) + (2859134031174853/100000000000000 : ℝ)*(f.failure) + (93220918299421/1562500000000 : ℝ)*(f.sum) + (861613660261/558750000000000000000000000 : ℝ)*base65 + (133708059393017681/55875000000000000000000000000000 : ℝ)*base68 + (794719303585857319/55875000000000000000000000000000 : ℝ)*base69 + (11744820289857319/55875000000000000000000000000000 : ℝ)*base71 + (3542114900629/2235000000000000000000000000 : ℝ)*base73 + (514107026137142681/55875000000000000000000000000000 : ℝ)*base76 + (638367845350482319/55875000000000000000000000000000 : ℝ)*base77 + (646745272885857319/55875000000000000000000000000000 : ℝ)*base79 + (13737924111889/2235000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (859/976562500000000000 : ℝ)*base89 + (859/976562500000000000 : ℝ)*base91 + (859/976562500000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1332_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (120574/78125 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14701/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (89/800 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5563/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (147/1000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1332_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1332_box_0 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1884584623/10000000000 : ℝ)*x 0 + (673794959/1250000000 : ℝ)*x 1 + (269517977/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1884584623/10000000000 : ℝ)^1073 ≤ (558573894837/5000000000000 : ℝ)^817 := by
    have hnat : (1884584623 : ℕ)^1073*5000000000000^817 ≤ 558573894837^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1884584623 10000000000 558573894837 5000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (673794959/1250000000 : ℝ)^1073 ≤ (44414261756117/100000000000000 : ℝ)^817 := by
    have hnat : (673794959 : ℕ)^1073*100000000000000^817 ≤ 44414261756117^817*1250000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673794959 1250000000 44414261756117 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269517977/500000000 : ℝ)^1073 ≤ (2775891270481/6250000000000 : ℝ)^817 := by
    have hnat : (269517977 : ℕ)^1073*6250000000000^817 ≤ 2775891270481^817*500000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269517977 500000000 2775891270481 6250000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1884584623/10000000000 : ℝ), (673794959/1250000000 : ℝ), (269517977/500000000 : ℝ)] ![(558573894837/5000000000000 : ℝ), (44414261756117/100000000000000 : ℝ), (2775891270481/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1884584623/10000000000 : ℝ)|^1073 ≤ (558573894837/5000000000000 : ℝ)^817
        have hw : |(-1884584623/10000000000 : ℝ)|=(1884584623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(673794959/1250000000 : ℝ)|^1073 ≤ (44414261756117/100000000000000 : ℝ)^817
        have hw : |(673794959/1250000000 : ℝ)|=(673794959/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269517977/500000000 : ℝ)|^1073 ≤ (2775891270481/6250000000000 : ℝ)^817
        have hw : |(269517977/500000000 : ℝ)|=(269517977/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_box_1 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2642510849/5000000000 : ℝ)*x 0 + (-202885131/1000000000 : ℝ)*x 1 + (2695179851/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642510849/5000000000 : ℝ)^1073 ≤ (10819466490011/25000000000000 : ℝ)^817 := by
    have hnat : (2642510849 : ℕ)^1073*25000000000000^817 ≤ 10819466490011^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642510849 5000000000 10819466490011 25000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (202885131/1000000000 : ℝ)^1073 ≤ (12307871946371/100000000000000 : ℝ)^817 := by
    have hnat : (202885131 : ℕ)^1073*100000000000000^817 ≤ 12307871946371^817*1000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202885131 1000000000 12307871946371 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695179851/5000000000 : ℝ)^1073 ≤ (22207131040379/50000000000000 : ℝ)^817 := by
    have hnat : (2695179851 : ℕ)^1073*50000000000000^817 ≤ 22207131040379^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695179851 5000000000 22207131040379 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642510849/5000000000 : ℝ), (-202885131/1000000000 : ℝ), (2695179851/5000000000 : ℝ)] ![(10819466490011/25000000000000 : ℝ), (12307871946371/100000000000000 : ℝ), (22207131040379/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642510849/5000000000 : ℝ)|^1073 ≤ (10819466490011/25000000000000 : ℝ)^817
        have hw : |(2642510849/5000000000 : ℝ)|=(2642510849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-202885131/1000000000 : ℝ)|^1073 ≤ (12307871946371/100000000000000 : ℝ)^817
        have hw : |(-202885131/1000000000 : ℝ)|=(202885131/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695179851/5000000000 : ℝ)|^1073 ≤ (22207131040379/50000000000000 : ℝ)^817
        have hw : |(2695179851/5000000000 : ℝ)|=(2695179851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_box_2 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (660627683/1250000000 : ℝ)*x 0 + (1078071971/2000000000 : ℝ)*x 1 + (-2028851419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660627683/1250000000 : ℝ)^1073 ≤ (43277863443453/100000000000000 : ℝ)^817 := by
    have hnat : (660627683 : ℕ)^1073*100000000000000^817 ≤ 43277863443453^817*1250000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660627683 1250000000 43277863443453 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078071971/2000000000 : ℝ)^1073 ≤ (11103565934107/25000000000000 : ℝ)^817 := by
    have hnat : (1078071971 : ℕ)^1073*25000000000000^817 ≤ 11103565934107^817*2000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078071971 2000000000 11103565934107 25000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2028851419/10000000000 : ℝ)^1073 ≤ (2461574562961/20000000000000 : ℝ)^817 := by
    have hnat : (2028851419 : ℕ)^1073*20000000000000^817 ≤ 2461574562961^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2028851419 10000000000 2461574562961 20000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660627683/1250000000 : ℝ), (1078071971/2000000000 : ℝ), (-2028851419/10000000000 : ℝ)] ![(43277863443453/100000000000000 : ℝ), (11103565934107/25000000000000 : ℝ), (2461574562961/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660627683/1250000000 : ℝ)|^1073 ≤ (43277863443453/100000000000000 : ℝ)^817
        have hw : |(660627683/1250000000 : ℝ)|=(660627683/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078071971/2000000000 : ℝ)|^1073 ≤ (11103565934107/25000000000000 : ℝ)^817
        have hw : |(1078071971/2000000000 : ℝ)|=(1078071971/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2028851419/10000000000 : ℝ)|^1073 ≤ (2461574562961/20000000000000 : ℝ)^817
        have hw : |(-2028851419/10000000000 : ℝ)|=(2028851419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_box_3 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (279854679/625000000 : ℝ)*x 0 + (851787929/2000000000 : ℝ)*x 1 + (4258939897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (279854679/625000000 : ℝ)^1073 ≤ (34810706824853/100000000000000 : ℝ)^817 := by
    have hnat : (279854679 : ℕ)^1073*100000000000000^817 ≤ 34810706824853^817*625000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279854679 625000000 34810706824853 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (851787929/2000000000 : ℝ)^1073 ≤ (6518929062479/20000000000000 : ℝ)^817 := by
    have hnat : (851787929 : ℕ)^1073*20000000000000^817 ≤ 6518929062479^817*2000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      851787929 2000000000 6518929062479 20000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4258939897/10000000000 : ℝ)^1073 ≤ (32594647845323/100000000000000 : ℝ)^817 := by
    have hnat : (4258939897 : ℕ)^1073*100000000000000^817 ≤ 32594647845323^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4258939897 10000000000 32594647845323 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(279854679/625000000 : ℝ), (851787929/2000000000 : ℝ), (4258939897/10000000000 : ℝ)] ![(34810706824853/100000000000000 : ℝ), (6518929062479/20000000000000 : ℝ), (32594647845323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(279854679/625000000 : ℝ)|^1073 ≤ (34810706824853/100000000000000 : ℝ)^817
        have hw : |(279854679/625000000 : ℝ)|=(279854679/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(851787929/2000000000 : ℝ)|^1073 ≤ (6518929062479/20000000000000 : ℝ)^817
        have hw : |(851787929/2000000000 : ℝ)|=(851787929/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4258939897/10000000000 : ℝ)|^1073 ≤ (32594647845323/100000000000000 : ℝ)^817
        have hw : |(4258939897/10000000000 : ℝ)|=(4258939897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_box_4 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-3557531/16000000 : ℝ)*x 0 + (1052939623/2000000000 : ℝ)*x 1 + (2632348709/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3557531/16000000 : ℝ)^1073 ≤ (13881158450001/100000000000000 : ℝ)^817 := by
    have hnat : (3557531 : ℕ)^1073*100000000000000^817 ≤ 13881158450001^817*16000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3557531 16000000 13881158450001 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052939623/2000000000 : ℝ)^1073 ≤ (21529712257451/50000000000000 : ℝ)^817 := by
    have hnat : (1052939623 : ℕ)^1073*50000000000000^817 ≤ 21529712257451^817*2000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052939623 2000000000 21529712257451 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632348709/5000000000 : ℝ)^1073 ≤ (10764854256987/25000000000000 : ℝ)^817 := by
    have hnat : (2632348709 : ℕ)^1073*25000000000000^817 ≤ 10764854256987^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632348709 5000000000 10764854256987 25000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3557531/16000000 : ℝ), (1052939623/2000000000 : ℝ), (2632348709/5000000000 : ℝ)] ![(13881158450001/100000000000000 : ℝ), (21529712257451/50000000000000 : ℝ), (10764854256987/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3557531/16000000 : ℝ)|^1073 ≤ (13881158450001/100000000000000 : ℝ)^817
        have hw : |(-3557531/16000000 : ℝ)|=(3557531/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052939623/2000000000 : ℝ)|^1073 ≤ (21529712257451/50000000000000 : ℝ)^817
        have hw : |(1052939623/2000000000 : ℝ)|=(1052939623/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632348709/5000000000 : ℝ)|^1073 ≤ (10764854256987/25000000000000 : ℝ)^817
        have hw : |(2632348709/5000000000 : ℝ)|=(2632348709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_box_5 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5373321219/10000000000 : ℝ)*x 0 + (-259900569/1250000000 : ℝ)*x 1 + (1316174529/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5373321219/10000000000 : ℝ)^1073 ≤ (44229973675091/100000000000000 : ℝ)^817 := by
    have hnat : (5373321219 : ℕ)^1073*100000000000000^817 ≤ 44229973675091^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5373321219 10000000000 44229973675091 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (259900569/1250000000 : ℝ)^1073 ≤ (6355300892981/50000000000000 : ℝ)^817 := by
    have hnat : (259900569 : ℕ)^1073*50000000000000^817 ≤ 6355300892981^817*1250000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259900569 1250000000 6355300892981 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316174529/2500000000 : ℝ)^1073 ≤ (10764856131411/25000000000000 : ℝ)^817 := by
    have hnat : (1316174529 : ℕ)^1073*25000000000000^817 ≤ 10764856131411^817*2500000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316174529 2500000000 10764856131411 25000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5373321219/10000000000 : ℝ), (-259900569/1250000000 : ℝ), (1316174529/2500000000 : ℝ)] ![(44229973675091/100000000000000 : ℝ), (6355300892981/50000000000000 : ℝ), (10764856131411/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5373321219/10000000000 : ℝ)|^1073 ≤ (44229973675091/100000000000000 : ℝ)^817
        have hw : |(5373321219/10000000000 : ℝ)|=(5373321219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-259900569/1250000000 : ℝ)|^1073 ≤ (6355300892981/50000000000000 : ℝ)^817
        have hw : |(-259900569/1250000000 : ℝ)|=(259900569/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316174529/2500000000 : ℝ)|^1073 ≤ (10764856131411/25000000000000 : ℝ)^817
        have hw : |(1316174529/2500000000 : ℝ)|=(1316174529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_box_6 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (335832587/625000000 : ℝ)*x 0 + (5264698169/10000000000 : ℝ)*x 1 + (-2079204247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335832587/625000000 : ℝ)^1073 ≤ (44229975545333/100000000000000 : ℝ)^817 := by
    have hnat : (335832587 : ℕ)^1073*100000000000000^817 ≤ 44229975545333^817*625000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335832587 625000000 44229975545333 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264698169/10000000000 : ℝ)^1073 ≤ (43059425094953/100000000000000 : ℝ)^817 := by
    have hnat : (5264698169 : ℕ)^1073*100000000000000^817 ≤ 43059425094953^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264698169 10000000000 43059425094953 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2079204247/10000000000 : ℝ)^1073 ≤ (12710599337201/100000000000000 : ℝ)^817 := by
    have hnat : (2079204247 : ℕ)^1073*100000000000000^817 ≤ 12710599337201^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079204247 10000000000 12710599337201 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335832587/625000000 : ℝ), (5264698169/10000000000 : ℝ), (-2079204247/10000000000 : ℝ)] ![(44229975545333/100000000000000 : ℝ), (43059425094953/100000000000000 : ℝ), (12710599337201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335832587/625000000 : ℝ)|^1073 ≤ (44229975545333/100000000000000 : ℝ)^817
        have hw : |(335832587/625000000 : ℝ)|=(335832587/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264698169/10000000000 : ℝ)|^1073 ≤ (43059425094953/100000000000000 : ℝ)^817
        have hw : |(5264698169/10000000000 : ℝ)|=(5264698169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2079204247/10000000000 : ℝ)|^1073 ≤ (12710599337201/100000000000000 : ℝ)^817
        have hw : |(-2079204247/10000000000 : ℝ)|=(2079204247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_box_7 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2089950177/5000000000 : ℝ)*x 0 + (4407772833/10000000000 : ℝ)*x 1 + (2203886663/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2089950177/5000000000 : ℝ)^1073 ≤ (31802517112749/100000000000000 : ℝ)^817 := by
    have hnat : (2089950177 : ℕ)^1073*100000000000000^817 ≤ 31802517112749^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089950177 5000000000 31802517112749 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4407772833/10000000000 : ℝ)^1073 ≤ (34098738934601/100000000000000 : ℝ)^817 := by
    have hnat : (4407772833 : ℕ)^1073*100000000000000^817 ≤ 34098738934601^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4407772833 10000000000 34098738934601 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2203886663/5000000000 : ℝ)^1073 ≤ (34098743943517/100000000000000 : ℝ)^817 := by
    have hnat : (2203886663 : ℕ)^1073*100000000000000^817 ≤ 34098743943517^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2203886663 5000000000 34098743943517 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2089950177/5000000000 : ℝ), (4407772833/10000000000 : ℝ), (2203886663/5000000000 : ℝ)] ![(31802517112749/100000000000000 : ℝ), (34098738934601/100000000000000 : ℝ), (34098743943517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2089950177/5000000000 : ℝ)|^1073 ≤ (31802517112749/100000000000000 : ℝ)^817
        have hw : |(2089950177/5000000000 : ℝ)|=(2089950177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4407772833/10000000000 : ℝ)|^1073 ≤ (34098738934601/100000000000000 : ℝ)^817
        have hw : |(4407772833/10000000000 : ℝ)|=(4407772833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2203886663/5000000000 : ℝ)|^1073 ≤ (34098743943517/100000000000000 : ℝ)^817
        have hw : |(2203886663/5000000000 : ℝ)|=(2203886663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_box_8 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-67260033/312500000 : ℝ)*x 0 + (2589117891/5000000000 : ℝ)*x 1 + (2702191963/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67260033/312500000 : ℝ)^1073 ≤ (6650421308079/50000000000000 : ℝ)^817 := by
    have hnat : (67260033 : ℕ)^1073*50000000000000^817 ≤ 6650421308079^817*312500000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67260033 312500000 6650421308079 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2589117891/5000000000 : ℝ)^1073 ≤ (21066536049303/50000000000000 : ℝ)^817 := by
    have hnat : (2589117891 : ℕ)^1073*50000000000000^817 ≤ 21066536049303^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589117891 5000000000 21066536049303 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2702191963/5000000000 : ℝ)^1073 ≤ (22283042631919/50000000000000 : ℝ)^817 := by
    have hnat : (2702191963 : ℕ)^1073*50000000000000^817 ≤ 22283042631919^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702191963 5000000000 22283042631919 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-67260033/312500000 : ℝ), (2589117891/5000000000 : ℝ), (2702191963/5000000000 : ℝ)] ![(6650421308079/50000000000000 : ℝ), (21066536049303/50000000000000 : ℝ), (22283042631919/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-67260033/312500000 : ℝ)|^1073 ≤ (6650421308079/50000000000000 : ℝ)^817
        have hw : |(-67260033/312500000 : ℝ)|=(67260033/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2589117891/5000000000 : ℝ)|^1073 ≤ (21066536049303/50000000000000 : ℝ)^817
        have hw : |(2589117891/5000000000 : ℝ)|=(2589117891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2702191963/5000000000 : ℝ)|^1073 ≤ (22283042631919/50000000000000 : ℝ)^817
        have hw : |(2702191963/5000000000 : ℝ)|=(2702191963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_box_9 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (659395229/1250000000 : ℝ)*x 0 + (-2023098639/10000000000 : ℝ)*x 1 + (5404383753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (659395229/1250000000 : ℝ)^1073 ≤ (43171857450433/100000000000000 : ℝ)^817 := by
    have hnat : (659395229 : ℕ)^1073*100000000000000^817 ≤ 43171857450433^817*1250000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659395229 1250000000 43171857450433 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2023098639/10000000000 : ℝ)^1073 ≤ (12262059144119/100000000000000 : ℝ)^817 := by
    have hnat : (2023098639 : ℕ)^1073*100000000000000^817 ≤ 12262059144119^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2023098639 10000000000 12262059144119 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5404383753/10000000000 : ℝ)^1073 ≤ (5570760423777/12500000000000 : ℝ)^817 := by
    have hnat : (5404383753 : ℕ)^1073*12500000000000^817 ≤ 5570760423777^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404383753 10000000000 5570760423777 12500000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(659395229/1250000000 : ℝ), (-2023098639/10000000000 : ℝ), (5404383753/10000000000 : ℝ)] ![(43171857450433/100000000000000 : ℝ), (12262059144119/100000000000000 : ℝ), (5570760423777/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(659395229/1250000000 : ℝ)|^1073 ≤ (43171857450433/100000000000000 : ℝ)^817
        have hw : |(659395229/1250000000 : ℝ)|=(659395229/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2023098639/10000000000 : ℝ)|^1073 ≤ (12262059144119/100000000000000 : ℝ)^817
        have hw : |(-2023098639/10000000000 : ℝ)|=(2023098639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5404383753/10000000000 : ℝ)|^1073 ≤ (5570760423777/12500000000000 : ℝ)^817
        have hw : |(5404383753/10000000000 : ℝ)|=(5404383753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_box_10 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (65939519/125000000 : ℝ)*x 0 + (67554801/125000000 : ℝ)*x 1 + (-252887327/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65939519/125000000 : ℝ)^1073 ≤ (43171854096941/100000000000000 : ℝ)^817 := by
    have hnat : (65939519 : ℕ)^1073*100000000000000^817 ≤ 43171854096941^817*125000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65939519 125000000 43171854096941 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67554801/125000000 : ℝ)^1073 ≤ (44566086931687/100000000000000 : ℝ)^817 := by
    have hnat : (67554801 : ℕ)^1073*100000000000000^817 ≤ 44566086931687^817*125000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67554801 125000000 44566086931687 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (252887327/1250000000 : ℝ)^1073 ≤ (6131029480517/50000000000000 : ℝ)^817 := by
    have hnat : (252887327 : ℕ)^1073*50000000000000^817 ≤ 6131029480517^817*1250000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252887327 1250000000 6131029480517 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(65939519/125000000 : ℝ), (67554801/125000000 : ℝ), (-252887327/1250000000 : ℝ)] ![(43171854096941/100000000000000 : ℝ), (44566086931687/100000000000000 : ℝ), (6131029480517/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(65939519/125000000 : ℝ)|^1073 ≤ (43171854096941/100000000000000 : ℝ)^817
        have hw : |(65939519/125000000 : ℝ)|=(65939519/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(67554801/125000000 : ℝ)|^1073 ≤ (44566086931687/100000000000000 : ℝ)^817
        have hw : |(67554801/125000000 : ℝ)|=(67554801/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-252887327/1250000000 : ℝ)|^1073 ≤ (6131029480517/50000000000000 : ℝ)^817
        have hw : |(-252887327/1250000000 : ℝ)|=(252887327/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_box_11 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4510348777/10000000000 : ℝ)*x 0 + (4242315223/10000000000 : ℝ)*x 1 + (4242315367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4510348777/10000000000 : ℝ)^1073 ≤ (702893952323/2000000000000 : ℝ)^817 := by
    have hnat : (4510348777 : ℕ)^1073*2000000000000^817 ≤ 702893952323^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4510348777 10000000000 702893952323 2000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4242315223/10000000000 : ℝ)^1073 ≤ (8106912615263/25000000000000 : ℝ)^817 := by
    have hnat : (4242315223 : ℕ)^1073*25000000000000^817 ≤ 8106912615263^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242315223 10000000000 8106912615263 25000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4242315367/10000000000 : ℝ)^1073 ≤ (32427651906667/100000000000000 : ℝ)^817 := by
    have hnat : (4242315367 : ℕ)^1073*100000000000000^817 ≤ 32427651906667^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242315367 10000000000 32427651906667 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4510348777/10000000000 : ℝ), (4242315223/10000000000 : ℝ), (4242315367/10000000000 : ℝ)] ![(702893952323/2000000000000 : ℝ), (8106912615263/25000000000000 : ℝ), (32427651906667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4510348777/10000000000 : ℝ)|^1073 ≤ (702893952323/2000000000000 : ℝ)^817
        have hw : |(4510348777/10000000000 : ℝ)|=(4510348777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4242315223/10000000000 : ℝ)|^1073 ≤ (8106912615263/25000000000000 : ℝ)^817
        have hw : |(4242315223/10000000000 : ℝ)|=(4242315223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4242315367/10000000000 : ℝ)|^1073 ≤ (32427651906667/100000000000000 : ℝ)^817
        have hw : |(4242315367/10000000000 : ℝ)|=(4242315367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_box_12 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1956077453/10000000000 : ℝ)*x 0 + (5474593339/10000000000 : ℝ)*x 1 + (10507273/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1956077453/10000000000 : ℝ)^1073 ≤ (5865673663353/50000000000000 : ℝ)^817 := by
    have hnat : (1956077453 : ℕ)^1073*50000000000000^817 ≤ 5865673663353^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1956077453 10000000000 5865673663353 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5474593339/10000000000 : ℝ)^1073 ≤ (22664004699441/50000000000000 : ℝ)^817 := by
    have hnat : (5474593339 : ℕ)^1073*50000000000000^817 ≤ 22664004699441^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5474593339 10000000000 22664004699441 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10507273/20000000 : ℝ)^1073 ≤ (42940643262807/100000000000000 : ℝ)^817 := by
    have hnat : (10507273 : ℕ)^1073*100000000000000^817 ≤ 42940643262807^817*20000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10507273 20000000 42940643262807 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1956077453/10000000000 : ℝ), (5474593339/10000000000 : ℝ), (10507273/20000000 : ℝ)] ![(5865673663353/50000000000000 : ℝ), (22664004699441/50000000000000 : ℝ), (42940643262807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1956077453/10000000000 : ℝ)|^1073 ≤ (5865673663353/50000000000000 : ℝ)^817
        have hw : |(-1956077453/10000000000 : ℝ)|=(1956077453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5474593339/10000000000 : ℝ)|^1073 ≤ (22664004699441/50000000000000 : ℝ)^817
        have hw : |(5474593339/10000000000 : ℝ)|=(5474593339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(10507273/20000000 : ℝ)|^1073 ≤ (42940643262807/100000000000000 : ℝ)^817
        have hw : |(10507273/20000000 : ℝ)|=(10507273/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_box_13 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5381091517/10000000000 : ℝ)*x 0 + (-1041766193/5000000000 : ℝ)*x 1 + (5253636687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5381091517/10000000000 : ℝ)^1073 ≤ (11078498655297/25000000000000 : ℝ)^817 := by
    have hnat : (5381091517 : ℕ)^1073*25000000000000^817 ≤ 11078498655297^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5381091517 10000000000 11078498655297 25000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1041766193/5000000000 : ℝ)^1073 ≤ (3186340024781/25000000000000 : ℝ)^817 := by
    have hnat : (1041766193 : ℕ)^1073*25000000000000^817 ≤ 3186340024781^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041766193 5000000000 3186340024781 25000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5253636687/10000000000 : ℝ)^1073 ≤ (42940645270179/100000000000000 : ℝ)^817 := by
    have hnat : (5253636687 : ℕ)^1073*100000000000000^817 ≤ 42940645270179^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253636687 10000000000 42940645270179 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5381091517/10000000000 : ℝ), (-1041766193/5000000000 : ℝ), (5253636687/10000000000 : ℝ)] ![(11078498655297/25000000000000 : ℝ), (3186340024781/25000000000000 : ℝ), (42940645270179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5381091517/10000000000 : ℝ)|^1073 ≤ (11078498655297/25000000000000 : ℝ)^817
        have hw : |(5381091517/10000000000 : ℝ)|=(5381091517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1041766193/5000000000 : ℝ)|^1073 ≤ (3186340024781/25000000000000 : ℝ)^817
        have hw : |(-1041766193/5000000000 : ℝ)|=(1041766193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5253636687/10000000000 : ℝ)|^1073 ≤ (42940645270179/100000000000000 : ℝ)^817
        have hw : |(5253636687/10000000000 : ℝ)|=(5253636687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_box_14 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2690545737/5000000000 : ℝ)*x 0 + (1313409133/2500000000 : ℝ)*x 1 + (-2083532651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2690545737/5000000000 : ℝ)^1073 ≤ (1107849853903/2500000000000 : ℝ)^817 := by
    have hnat : (2690545737 : ℕ)^1073*2500000000000^817 ≤ 1107849853903^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2690545737 5000000000 1107849853903 2500000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1313409133/2500000000 : ℝ)^1073 ≤ (8588128721263/20000000000000 : ℝ)^817 := by
    have hnat : (1313409133 : ℕ)^1073*20000000000000^817 ≤ 8588128721263^817*2500000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313409133 2500000000 8588128721263 20000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2083532651/10000000000 : ℝ)^1073 ≤ (12745362228123/100000000000000 : ℝ)^817 := by
    have hnat : (2083532651 : ℕ)^1073*100000000000000^817 ≤ 12745362228123^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083532651 10000000000 12745362228123 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2690545737/5000000000 : ℝ), (1313409133/2500000000 : ℝ), (-2083532651/10000000000 : ℝ)] ![(1107849853903/2500000000000 : ℝ), (8588128721263/20000000000000 : ℝ), (12745362228123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2690545737/5000000000 : ℝ)|^1073 ≤ (1107849853903/2500000000000 : ℝ)^817
        have hw : |(2690545737/5000000000 : ℝ)|=(2690545737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1313409133/2500000000 : ℝ)|^1073 ≤ (8588128721263/20000000000000 : ℝ)^817
        have hw : |(1313409133/2500000000 : ℝ)|=(1313409133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2083532651/10000000000 : ℝ)|^1073 ≤ (12745362228123/100000000000000 : ℝ)^817
        have hw : |(-2083532651/10000000000 : ℝ)|=(2083532651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_box_15 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4153241697/10000000000 : ℝ)*x 0 + (4420863323/10000000000 : ℝ)*x 1 + (4420863341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4153241697/10000000000 : ℝ)^1073 ≤ (31536397617493/100000000000000 : ℝ)^817 := by
    have hnat : (4153241697 : ℕ)^1073*100000000000000^817 ≤ 31536397617493^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4153241697 10000000000 31536397617493 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4420863323/10000000000 : ℝ)^1073 ≤ (2139487568467/6250000000000 : ℝ)^817 := by
    have hnat : (4420863323 : ℕ)^1073*6250000000000^817 ≤ 2139487568467^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4420863323 10000000000 2139487568467 6250000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4420863341/10000000000 : ℝ)^1073 ≤ (34231801278523/100000000000000 : ℝ)^817 := by
    have hnat : (4420863341 : ℕ)^1073*100000000000000^817 ≤ 34231801278523^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4420863341 10000000000 34231801278523 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4153241697/10000000000 : ℝ), (4420863323/10000000000 : ℝ), (4420863341/10000000000 : ℝ)] ![(31536397617493/100000000000000 : ℝ), (2139487568467/6250000000000 : ℝ), (34231801278523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4153241697/10000000000 : ℝ)|^1073 ≤ (31536397617493/100000000000000 : ℝ)^817
        have hw : |(4153241697/10000000000 : ℝ)|=(4153241697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4420863323/10000000000 : ℝ)|^1073 ≤ (2139487568467/6250000000000 : ℝ)^817
        have hw : |(4420863323/10000000000 : ℝ)|=(4420863323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4420863341/10000000000 : ℝ)|^1073 ≤ (34231801278523/100000000000000 : ℝ)^817
        have hw : |(4420863341/10000000000 : ℝ)|=(4420863341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1332_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (120574/78125 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (147/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5563/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(15713/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29461/50000 : ℝ) ∧ (9987/12500 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84313/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (147/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5563/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (147/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5563/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (147/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5563/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (147/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5563/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (147/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5563/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (147/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5563/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5563/50000 : ℝ) ^ (4291/1024 : ℝ) ≤ (10086740937838259/100000000000000000000 : ℝ) := by
    have hpowers : (5563/50000 : ℝ)^4291 ≤ (10086740937838259/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5563 : ℕ)^4291*100000000000000000000^1024 ≤ 10086740937838259^1024*50000^4291 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5563 50000 10086740937838259 100000000000000000000 4291 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5563/50000 : ℝ)) (X := (10086740937838259/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (147/1000 : ℝ) ^ (4291/1024 : ℝ) ≤ (32411702149518197/100000000000000000000 : ℝ) := by
    have hpowers : (147/1000 : ℝ)^4291 ≤ (32411702149518197/100000000000000000000 : ℝ)^1024 := by
      have hnat : (147 : ℕ)^4291*100000000000000000000^1024 ≤ 32411702149518197^1024*1000^4291 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        147 1000 32411702149518197 100000000000000000000 4291 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (147/1000 : ℝ)) (X := (32411702149518197/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010086740937838259/50000000000000000000 : ℝ) ≤ (2500120345252817/2500000000000000 : ℝ) ^ (4291/1024 : ℝ) := by
    have hpowers : (50010086740937838259/50000000000000000000 : ℝ)^1024 ≤ (2500120345252817/2500000000000000 : ℝ)^4291 := by
      have hnat : (50010086740937838259 : ℕ)^1024*2500000000000000^4291 ≤ 2500120345252817^4291*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010086740937838259 50000000000000000000 2500120345252817 2500000000000000 1024 4291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500120345252817/2500000000000000 : ℝ)) (X := (50010086740937838259/50000000000000000000 : ℝ)) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505312305385919557/12500000000000000000 : ℝ) ≤ (10001014014610281/10000000000000000 : ℝ) ^ (4291/1024 : ℝ) := by
    have hpowers : (12505312305385919557/12500000000000000000 : ℝ)^1024 ≤ (10001014014610281/10000000000000000 : ℝ)^4291 := by
      have hnat : (12505312305385919557 : ℕ)^1024*10000000000000000^4291 ≤ 10001014014610281^4291*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505312305385919557 12500000000000000000 10001014014610281 10000000000000000 1024 4291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001014014610281/10000000000000000 : ℝ)) (X := (12505312305385919557/12500000000000000000 : ℝ)) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032411702149518197/50000000000000000000 : ℝ) ≤ (5000773324104647/5000000000000000 : ℝ) ^ (4291/1024 : ℝ) := by
    have hpowers : (50032411702149518197/50000000000000000000 : ℝ)^1024 ≤ (5000773324104647/5000000000000000 : ℝ)^4291 := by
      have hnat : (50032411702149518197 : ℕ)^1024*5000000000000000^4291 ≤ 5000773324104647^4291*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032411702149518197 50000000000000000000 5000773324104647 5000000000000000 1024 4291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000773324104647/5000000000000000 : ℝ)) (X := (50032411702149518197/50000000000000000000 : ℝ)) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10086740937838259/100000000000000000000 : ℝ) ≤ ((8932467073222258639/8935000000000000000 : ℝ)+2*(532633599013/357400000000000 : ℝ)*(5563/50000 : ℝ))^(4291/1024 : ℝ) := by
    rw [show (8932467073222258639/8935000000000000000 : ℝ)+2*(532633599013/357400000000000 : ℝ)*(5563/50000 : ℝ)=(2500120345252817/2500000000000000 : ℝ) by norm_num, show 1+2*(10086740937838259/100000000000000000000 : ℝ)=(50010086740937838259/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32411702149518197/100000000000000000000 : ℝ)+(10086740937838259/100000000000000000000 : ℝ) ≤ ((8932467073222258639/8935000000000000000 : ℝ)+(532633599013/357400000000000 : ℝ)*((147/1000 : ℝ)+(5563/50000 : ℝ)))^(4291/1024 : ℝ) := by
    rw [show (8932467073222258639/8935000000000000000 : ℝ)+(532633599013/357400000000000 : ℝ)*((147/1000 : ℝ)+(5563/50000 : ℝ))=(10001014014610281/10000000000000000 : ℝ) by norm_num, show 1+(32411702149518197/100000000000000000000 : ℝ)+(10086740937838259/100000000000000000000 : ℝ)=(12505312305385919557/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32411702149518197/100000000000000000000 : ℝ) ≤ ((8932467073222258639/8935000000000000000 : ℝ)+2*(532633599013/357400000000000 : ℝ)*(147/1000 : ℝ))^(4291/1024 : ℝ) := by
    rw [show (8932467073222258639/8935000000000000000 : ℝ)+2*(532633599013/357400000000000 : ℝ)*(147/1000 : ℝ)=(5000773324104647/5000000000000000 : ℝ) by norm_num, show 1+2*(32411702149518197/100000000000000000000 : ℝ)=(50032411702149518197/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8932467073222258639/8935000000000000000 : ℝ)*(X 1 0+X 2 0)+(532633599013/357400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4291/1024 : ℝ)) (lo := (5563/50000 : ℝ)) (hi := (147/1000 : ℝ)) (c := (8932467073222258639/8935000000000000000 : ℝ)) (alpha := (532633599013/357400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8932467073222258639/8935000000000000000 : ℝ)*(X 0 1+X 2 1)+(532633599013/357400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4291/1024 : ℝ)) (lo := (5563/50000 : ℝ)) (hi := (147/1000 : ℝ)) (c := (8932467073222258639/8935000000000000000 : ℝ)) (alpha := (532633599013/357400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8932467073222258639/8935000000000000000 : ℝ)*(X 0 2+X 1 2)+(532633599013/357400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4291/1024 : ℝ)) (lo := (5563/50000 : ℝ)) (hi := (147/1000 : ℝ)) (c := (8932467073222258639/8935000000000000000 : ℝ)) (alpha := (532633599013/357400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1884584623/10000000000 : ℝ)*X 0 0+(673794959/1250000000 : ℝ)*X 0 1+(269517977/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2642510849/5000000000 : ℝ)*X 1 0+(-202885131/1000000000 : ℝ)*X 1 1+(2695179851/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((660627683/1250000000 : ℝ)*X 2 0+(1078071971/2000000000 : ℝ)*X 2 1+(-2028851419/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((279854679/625000000 : ℝ)*X 0 0+(851787929/2000000000 : ℝ)*X 0 1+(4258939897/10000000000 : ℝ)*X 0 2+(279854679/625000000 : ℝ)*X 1 0+(851787929/2000000000 : ℝ)*X 1 1+(4258939897/10000000000 : ℝ)*X 1 2+(279854679/625000000 : ℝ)*X 2 0+(851787929/2000000000 : ℝ)*X 2 1+(4258939897/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-3557531/16000000 : ℝ)*X 0 0+(1052939623/2000000000 : ℝ)*X 0 1+(2632348709/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5373321219/10000000000 : ℝ)*X 1 0+(-259900569/1250000000 : ℝ)*X 1 1+(1316174529/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((335832587/625000000 : ℝ)*X 2 0+(5264698169/10000000000 : ℝ)*X 2 1+(-2079204247/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2089950177/5000000000 : ℝ)*X 0 0+(4407772833/10000000000 : ℝ)*X 0 1+(2203886663/5000000000 : ℝ)*X 0 2+(2089950177/5000000000 : ℝ)*X 1 0+(4407772833/10000000000 : ℝ)*X 1 1+(2203886663/5000000000 : ℝ)*X 1 2+(2089950177/5000000000 : ℝ)*X 2 0+(4407772833/10000000000 : ℝ)*X 2 1+(2203886663/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-67260033/312500000 : ℝ)*X 0 0+(2589117891/5000000000 : ℝ)*X 0 1+(2702191963/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((659395229/1250000000 : ℝ)*X 1 0+(-2023098639/10000000000 : ℝ)*X 1 1+(5404383753/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((65939519/125000000 : ℝ)*X 2 0+(67554801/125000000 : ℝ)*X 2 1+(-252887327/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4510348777/10000000000 : ℝ)*X 0 0+(4242315223/10000000000 : ℝ)*X 0 1+(4242315367/10000000000 : ℝ)*X 0 2+(4510348777/10000000000 : ℝ)*X 1 0+(4242315223/10000000000 : ℝ)*X 1 1+(4242315367/10000000000 : ℝ)*X 1 2+(4510348777/10000000000 : ℝ)*X 2 0+(4242315223/10000000000 : ℝ)*X 2 1+(4242315367/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1956077453/10000000000 : ℝ)*X 0 0+(5474593339/10000000000 : ℝ)*X 0 1+(10507273/20000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5381091517/10000000000 : ℝ)*X 1 0+(-1041766193/5000000000 : ℝ)*X 1 1+(5253636687/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2690545737/5000000000 : ℝ)*X 2 0+(1313409133/2500000000 : ℝ)*X 2 1+(-2083532651/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4153241697/10000000000 : ℝ)*X 0 0+(4420863323/10000000000 : ℝ)*X 0 1+(4420863341/10000000000 : ℝ)*X 0 2+(4153241697/10000000000 : ℝ)*X 1 0+(4420863323/10000000000 : ℝ)*X 1 1+(4420863341/10000000000 : ℝ)*X 1 2+(4153241697/10000000000 : ℝ)*X 2 0+(4420863323/10000000000 : ℝ)*X 2 1+(4420863341/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15713/25000 : ℝ) ≤ (-28077820198883347222580744295363/44675000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (123784009/100000000000000 : ℝ)*(upper0) + (45304371/100000000000000 : ℝ)*(lower1) + (148208383/100000000000000 : ℝ)*(lower2) + (290931023153839/10000000000000 : ℝ)*(major0) + (290931023153839/10000000000000 : ℝ)*(major1) + (290931023153839/10000000000000 : ℝ)*(major2) + (6012140817/100000000000000 : ℝ)*(sp3) + (3954496057646269/100000000000000 : ℝ)*(sp4) + (1977203755234689/50000000000000 : ℝ)*(sp5) + (494288101500049/12500000000000 : ℝ)*(sp6) + (117816204639407/6250000000000 : ℝ)*(sp7) + (4403849257/50000000000000 : ℝ)*(sp8) + (48677437703/50000000000000 : ℝ)*(sp13) + (25006668049/12500000000000 : ℝ)*(sp14) + (188506528637133/10000000000000 : ℝ)*(f.failure) + (247156554084049/6250000000000 : ℝ)*(f.sum) + (85133198531/55843750000000000000000000 : ℝ)*base66 + (1233965082680040121/89350000000000000000000000000000 : ℝ)*base67 + (340238417544990121/89350000000000000000000000000000 : ℝ)*base69 + (611302224049440121/89350000000000000000000000000000 : ℝ)*base71 + (1606300089973/55843750000000000000000000 : ℝ)*base74 + (319634989821590121/89350000000000000000000000000000 : ℝ)*base75 + (134523382958359879/89350000000000000000000000000000 : ℝ)*base78 + (2659380744189109879/89350000000000000000000000000000 : ℝ)*base80 + (1403327737449/223375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (2467/781250000000000000 : ℝ)*base89 + (2467/781250000000000000 : ℝ)*base91 + (2467/781250000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (29461/50000 : ℝ) ≤ (263243939345355638329897655367189/446750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1252799/20000000000000 : ℝ)*(lower1) + (45002439/50000000000000 : ℝ)*(upper2) + (215479/6250000000000 : ℝ)*(lower5) + (2977664860329817/100000000000000 : ℝ)*(major0) + (2977664860329817/100000000000000 : ℝ)*(major1) + (2977664860329817/100000000000000 : ℝ)*(major2) + (4006332591123111/100000000000000 : ℝ)*(sp0) + (4006327873747381/100000000000000 : ℝ)*(sp1) + (1001581862459911/25000000000000 : ℝ)*(sp2) + (964672434394093/50000000000000 : ℝ)*(sp3) + (5296584643/100000000000000 : ℝ)*(sp5) + (286024619/5000000000000 : ℝ)*(sp6) + (82207043/800000000000 : ℝ)*(sp11) + (36200557/6250000000000 : ℝ)*(sp12) + (24116939308357/1250000000000 : ℝ)*(f.failure) + (500791646291503/12500000000000 : ℝ)*(f.sum) + (576142326679/17870000000000000000000000000 : ℝ)*base66 + (1025165439290564063/893500000000000000000000000000000 : ℝ)*base67 + (4649740173328564063/893500000000000000000000000000000 : ℝ)*base69 + (6468906302195935937/893500000000000000000000000000000 : ℝ)*base72 + (21204818699991/17870000000000000000000000000 : ℝ)*base73 + (358556160956435937/893500000000000000000000000000000 : ℝ)*base76 + (3348803427459435937/893500000000000000000000000000000 : ℝ)*base78 + (5875627306689435937/893500000000000000000000000000000 : ℝ)*base80 + (12051479072851/17870000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (63/1562500000000000000 : ℝ)*base89 + (63/1562500000000000000 : ℝ)*base91 + (63/1562500000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (9987/12500 : ℝ) ≤ (1784723789505347321245299603/2233750000000000000000000000 : ℝ) := by norm_num
    linear_combination (1618023/2500000000000 : ℝ)*(upper2) + (5445587/100000000000000 : ℝ)*(lower3) + (1827317/25000000000000 : ℝ)*(lower5) + (822546487655467/25000000000000 : ℝ)*(major0) + (822546487655467/25000000000000 : ℝ)*(major1) + (822546487655467/25000000000000 : ℝ)*(major2) + (186675919/20000000000000 : ℝ)*(sp0) + (74282367223/100000000000000 : ℝ)*(sp2) + (46949230141/100000000000000 : ℝ)*(sp3) + (884376569923711/20000000000000 : ℝ)*(sp8) + (2210944204774887/50000000000000 : ℝ)*(sp9) + (552726765897819/12500000000000 : ℝ)*(sp10) + (426360768550199/20000000000000 : ℝ)*(sp11) + (578318953/12500000000000 : ℝ)*(sp12) + (133240674498821/6250000000000 : ℝ)*(f.failure) + (2210944204774887/50000000000000 : ℝ)*(f.sum) + (6359944154443/2233750000000000000000000000 : ℝ)*base65 + (2025645178624104413/223375000000000000000000000000000 : ℝ)*base67 + (1970139248465104413/223375000000000000000000000000000 : ℝ)*base69 + (233767859353020587/223375000000000000000000000000000 : ℝ)*base72 + (8169222481501/4467500000000000000000000000 : ℝ)*base73 + (2093707485727104413/223375000000000000000000000000000 : ℝ)*base75 + (792618054494020587/223375000000000000000000000000000 : ℝ)*base78 + (1349940735437520587/223375000000000000000000000000000 : ℝ)*base80 + (7840286682387/8935000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (13641/1953125000000000000 : ℝ)*base89 + (13641/1953125000000000000 : ℝ)*base91 + (13641/1953125000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-84313/100000 : ℝ) ≤ (-18832867961703408100115763724311/22337500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (44729043/100000000000000 : ℝ)*(lower0) + (235219/1250000000000 : ℝ)*(upper3) + (56856483/50000000000000 : ℝ)*(lower4) + (332654332744683/10000000000000 : ℝ)*(major0) + (332654332744683/10000000000000 : ℝ)*(major1) + (332654332744683/10000000000000 : ℝ)*(major2) + (170216723/25000000000000 : ℝ)*(sp4) + (121301300777/100000000000000 : ℝ)*(sp6) + (59329096131/100000000000000 : ℝ)*(sp7) + (2157963869/50000000000000 : ℝ)*(sp8) + (1131444224292713/25000000000000 : ℝ)*(sp12) + (2262890946982741/50000000000000 : ℝ)*(sp13) + (905132118532941/20000000000000 : ℝ)*(sp14) + (2155348946790739/100000000000000 : ℝ)*(sp15) + (215540827588687/10000000000000 : ℝ)*(f.failure) + (2262890946982741/50000000000000 : ℝ)*(f.sum) + (5257425721193/446750000000000000000000000 : ℝ)*base66 + (1224973742938641437/89350000000000000000000000000000 : ℝ)*base67 + (851493994831891437/89350000000000000000000000000000 : ℝ)*base69 + (244765074341808563/89350000000000000000000000000000 : ℝ)*base72 + (1864546212537/1787000000000000000000000000 : ℝ)*base74 + (493672630060391437/89350000000000000000000000000000 : ℝ)*base75 + (1111967270122191437/89350000000000000000000000000000 : ℝ)*base77 + (261352233830491437/89350000000000000000000000000000 : ℝ)*base79 + (4541180066941/893500000000000000000000000 : ℝ)*base81 + (13037/781250000000000000 : ℝ)*base90 + (13037/781250000000000000 : ℝ)*base92 + (13037/781250000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1332_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (120574/78125 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (147/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5563/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15713/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(29461/50000 : ℝ) else (9987/12500 : ℝ) ≤ X j i ∧ X j i ≤ (84313/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1332_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1332_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (120574/78125 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1471/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11117/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15713/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(29461/50000 : ℝ) else (9987/12500 : ℝ) ≤ X j i ∧ X j i ≤ (84313/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1332_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1332_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1332_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (120574/78125 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1471/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11117/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15713/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(29461/50000 : ℝ) else (9987/12500 : ℝ) ≤ X j i ∧ X j i ≤ (84313/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1332_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

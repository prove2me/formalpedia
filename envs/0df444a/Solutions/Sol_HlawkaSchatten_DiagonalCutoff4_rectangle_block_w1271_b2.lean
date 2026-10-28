-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1271_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:20:16.919963+00:00
-- url     : https://prove2.me/submissions/313c237d-d77f-4a5a-b2a9-2feed219451a

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
theorem support_rectangle_w1271_s6_0 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2106210579/10000000000 : ℝ)*x 0 + (673849649/1250000000 : ℝ)*x 1 + (1316863423/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2106210579/10000000000 : ℝ)^8465 ≤ (6405689256659/50000000000000 : ℝ)^6417 := by
    have hnat : (2106210579 : ℕ)^8465*50000000000000^6417 ≤ 6405689256659^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106210579 10000000000 6405689256659 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (673849649/1250000000 : ℝ)^8465 ≤ (44259799485963/100000000000000 : ℝ)^6417 := by
    have hnat : (673849649 : ℕ)^8465*100000000000000^6417 ≤ 44259799485963^6417*1250000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673849649 1250000000 44259799485963 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316863423/2500000000 : ℝ)^8465 ≤ (10732205496947/25000000000000 : ℝ)^6417 := by
    have hnat : (1316863423 : ℕ)^8465*25000000000000^6417 ≤ 10732205496947^6417*2500000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316863423 2500000000 10732205496947 25000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2106210579/10000000000 : ℝ), (673849649/1250000000 : ℝ), (1316863423/2500000000 : ℝ)] ![(6405689256659/50000000000000 : ℝ), (44259799485963/100000000000000 : ℝ), (10732205496947/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2106210579/10000000000 : ℝ)|^8465 ≤ (6405689256659/50000000000000 : ℝ)^6417
        have hw : |(-2106210579/10000000000 : ℝ)|=(2106210579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(673849649/1250000000 : ℝ)|^8465 ≤ (44259799485963/100000000000000 : ℝ)^6417
        have hw : |(673849649/1250000000 : ℝ)|=(673849649/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316863423/2500000000 : ℝ)|^8465 ≤ (10732205496947/25000000000000 : ℝ)^6417
        have hw : |(1316863423/2500000000 : ℝ)|=(1316863423/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s6_1 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (66802323/125000000 : ℝ)*x 0 + (-86749771/400000000 : ℝ)*x 1 + (2633726847/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66802323/125000000 : ℝ)^8465 ≤ (10938917456357/25000000000000 : ℝ)^6417 := by
    have hnat : (66802323 : ℕ)^8465*25000000000000^6417 ≤ 10938917456357^6417*125000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66802323 125000000 10938917456357 25000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (86749771/400000000 : ℝ)^8465 ≤ (832219258847/6250000000000 : ℝ)^6417 := by
    have hnat : (86749771 : ℕ)^8465*6250000000000^6417 ≤ 832219258847^6417*400000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86749771 400000000 832219258847 6250000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633726847/5000000000 : ℝ)^8465 ≤ (42928822009289/100000000000000 : ℝ)^6417 := by
    have hnat : (2633726847 : ℕ)^8465*100000000000000^6417 ≤ 42928822009289^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633726847 5000000000 42928822009289 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66802323/125000000 : ℝ), (-86749771/400000000 : ℝ), (2633726847/5000000000 : ℝ)] ![(10938917456357/25000000000000 : ℝ), (832219258847/6250000000000 : ℝ), (42928822009289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66802323/125000000 : ℝ)|^8465 ≤ (10938917456357/25000000000000 : ℝ)^6417
        have hw : |(66802323/125000000 : ℝ)|=(66802323/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-86749771/400000000 : ℝ)|^8465 ≤ (832219258847/6250000000000 : ℝ)^6417
        have hw : |(-86749771/400000000 : ℝ)|=(86749771/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633726847/5000000000 : ℝ)|^8465 ≤ (42928822009289/100000000000000 : ℝ)^6417
        have hw : |(2633726847/5000000000 : ℝ)|=(2633726847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s6_2 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336046461/2500000000 : ℝ)*x 0 + (5267453689/10000000000 : ℝ)*x 1 + (-2168744277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336046461/2500000000 : ℝ)^8465 ≤ (4375566986863/10000000000000 : ℝ)^6417 := by
    have hnat : (1336046461 : ℕ)^8465*10000000000000^6417 ≤ 4375566986863^6417*2500000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336046461 2500000000 4375566986863 10000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267453689/10000000000 : ℝ)^8465 ≤ (8585764391107/20000000000000 : ℝ)^6417 := by
    have hnat : (5267453689 : ℕ)^8465*20000000000000^6417 ≤ 8585764391107^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267453689 10000000000 8585764391107 20000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2168744277/10000000000 : ℝ)^8465 ≤ (53262032631/400000000000 : ℝ)^6417 := by
    have hnat : (2168744277 : ℕ)^8465*400000000000^6417 ≤ 53262032631^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168744277 10000000000 53262032631 400000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336046461/2500000000 : ℝ), (5267453689/10000000000 : ℝ), (-2168744277/10000000000 : ℝ)] ![(4375566986863/10000000000000 : ℝ), (8585764391107/20000000000000 : ℝ), (53262032631/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336046461/2500000000 : ℝ)|^8465 ≤ (4375566986863/10000000000000 : ℝ)^6417
        have hw : |(1336046461/2500000000 : ℝ)|=(1336046461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267453689/10000000000 : ℝ)|^8465 ≤ (8585764391107/20000000000000 : ℝ)^6417
        have hw : |(5267453689/10000000000 : ℝ)|=(5267453689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2168744277/10000000000 : ℝ)|^8465 ≤ (53262032631/400000000000 : ℝ)^6417
        have hw : |(-2168744277/10000000000 : ℝ)|=(2168744277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s6_3 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (869333443/2000000000 : ℝ)*x 0 + (4222595277/10000000000 : ℝ)*x 1 + (2237128223/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (869333443/2000000000 : ℝ)^8465 ≤ (16658780018961/50000000000000 : ℝ)^6417 := by
    have hnat : (869333443 : ℕ)^8465*50000000000000^6417 ≤ 16658780018961^6417*2000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869333443 2000000000 16658780018961 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4222595277/10000000000 : ℝ)^8465 ≤ (32068769668981/100000000000000 : ℝ)^6417 := by
    have hnat : (4222595277 : ℕ)^8465*100000000000000^6417 ≤ 32068769668981^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4222595277 10000000000 32068769668981 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2237128223/5000000000 : ℝ)^8465 ≤ (34613670278319/100000000000000 : ℝ)^6417 := by
    have hnat : (2237128223 : ℕ)^8465*100000000000000^6417 ≤ 34613670278319^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237128223 5000000000 34613670278319 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(869333443/2000000000 : ℝ), (4222595277/10000000000 : ℝ), (2237128223/5000000000 : ℝ)] ![(16658780018961/50000000000000 : ℝ), (32068769668981/100000000000000 : ℝ), (34613670278319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(869333443/2000000000 : ℝ)|^8465 ≤ (16658780018961/50000000000000 : ℝ)^6417
        have hw : |(869333443/2000000000 : ℝ)|=(869333443/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4222595277/10000000000 : ℝ)|^8465 ≤ (32068769668981/100000000000000 : ℝ)^6417
        have hw : |(4222595277/10000000000 : ℝ)|=(4222595277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2237128223/5000000000 : ℝ)|^8465 ≤ (34613670278319/100000000000000 : ℝ)^6417
        have hw : |(2237128223/5000000000 : ℝ)|=(2237128223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s6_4 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2106215203/10000000000 : ℝ)*x 0 + (5267765823/10000000000 : ℝ)*x 1 + (5390483927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2106215203/10000000000 : ℝ)^8465 ≤ (6405707808071/50000000000000 : ℝ)^6417 := by
    have hnat : (2106215203 : ℕ)^8465*50000000000000^6417 ≤ 6405707808071^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106215203 10000000000 6405707808071 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267765823/10000000000 : ℝ)^8465 ≤ (1341630552997/3125000000000 : ℝ)^6417 := by
    have hnat : (5267765823 : ℕ)^8465*3125000000000^6417 ≤ 1341630552997^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267765823 10000000000 1341630552997 3125000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390483927/10000000000 : ℝ)^8465 ≤ (2212820333923/5000000000000 : ℝ)^6417 := by
    have hnat : (5390483927 : ℕ)^8465*5000000000000^6417 ≤ 2212820333923^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390483927 10000000000 2212820333923 5000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2106215203/10000000000 : ℝ), (5267765823/10000000000 : ℝ), (5390483927/10000000000 : ℝ)] ![(6405707808071/50000000000000 : ℝ), (1341630552997/3125000000000 : ℝ), (2212820333923/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2106215203/10000000000 : ℝ)|^8465 ≤ (6405707808071/50000000000000 : ℝ)^6417
        have hw : |(-2106215203/10000000000 : ℝ)|=(2106215203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267765823/10000000000 : ℝ)|^8465 ≤ (1341630552997/3125000000000 : ℝ)^6417
        have hw : |(5267765823/10000000000 : ℝ)|=(5267765823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390483927/10000000000 : ℝ)|^8465 ≤ (2212820333923/5000000000000 : ℝ)^6417
        have hw : |(5390483927/10000000000 : ℝ)|=(5390483927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s6_5 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312651137/10000000000 : ℝ)*x 0 + (-2045714043/10000000000 : ℝ)*x 1 + (673810489/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312651137/10000000000 : ℝ)^8465 ≤ (2170769869449/5000000000000 : ℝ)^6417 := by
    have hnat : (5312651137 : ℕ)^8465*5000000000000^6417 ≤ 2170769869449^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312651137 10000000000 2170769869449 5000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2045714043/10000000000 : ℝ)^8465 ≤ (12328196069203/100000000000000 : ℝ)^6417 := by
    have hnat : (2045714043 : ℕ)^8465*100000000000000^6417 ≤ 12328196069203^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2045714043 10000000000 12328196069203 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673810489/1250000000 : ℝ)^8465 ≤ (8851281303201/20000000000000 : ℝ)^6417 := by
    have hnat : (673810489 : ℕ)^8465*20000000000000^6417 ≤ 8851281303201^6417*1250000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673810489 1250000000 8851281303201 20000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312651137/10000000000 : ℝ), (-2045714043/10000000000 : ℝ), (673810489/1250000000 : ℝ)] ![(2170769869449/5000000000000 : ℝ), (12328196069203/100000000000000 : ℝ), (8851281303201/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312651137/10000000000 : ℝ)|^8465 ≤ (2170769869449/5000000000000 : ℝ)^6417
        have hw : |(5312651137/10000000000 : ℝ)|=(5312651137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2045714043/10000000000 : ℝ)|^8465 ≤ (12328196069203/100000000000000 : ℝ)^6417
        have hw : |(-2045714043/10000000000 : ℝ)|=(2045714043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673810489/1250000000 : ℝ)|^8465 ≤ (8851281303201/20000000000000 : ℝ)^6417
        have hw : |(673810489/1250000000 : ℝ)|=(673810489/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s6_6 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312651137/10000000000 : ℝ)*x 0 + (5390483909/10000000000 : ℝ)*x 1 + (-15982141/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312651137/10000000000 : ℝ)^8465 ≤ (2170769869449/5000000000000 : ℝ)^6417 := by
    have hnat : (5312651137 : ℕ)^8465*5000000000000^6417 ≤ 2170769869449^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312651137 10000000000 2170769869449 5000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390483909/10000000000 : ℝ)^8465 ≤ (22128203241757/50000000000000 : ℝ)^6417 := by
    have hnat : (5390483909 : ℕ)^8465*50000000000000^6417 ≤ 22128203241757^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390483909 10000000000 22128203241757 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (15982141/78125000 : ℝ)^8465 ≤ (12328196108951/100000000000000 : ℝ)^6417 := by
    have hnat : (15982141 : ℕ)^8465*100000000000000^6417 ≤ 12328196108951^6417*78125000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15982141 78125000 12328196108951 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312651137/10000000000 : ℝ), (5390483909/10000000000 : ℝ), (-15982141/78125000 : ℝ)] ![(2170769869449/5000000000000 : ℝ), (22128203241757/50000000000000 : ℝ), (12328196108951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312651137/10000000000 : ℝ)|^8465 ≤ (2170769869449/5000000000000 : ℝ)^6417
        have hw : |(5312651137/10000000000 : ℝ)|=(5312651137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390483909/10000000000 : ℝ)|^8465 ≤ (22128203241757/50000000000000 : ℝ)^6417
        have hw : |(5390483909/10000000000 : ℝ)|=(5390483909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-15982141/78125000 : ℝ)|^8465 ≤ (12328196108951/100000000000000 : ℝ)^6417
        have hw : |(-15982141/78125000 : ℝ)|=(15982141/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s6_7 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (543334581/1250000000 : ℝ)*x 0 + (447361959/1000000000 : ℝ)*x 1 + (2111617229/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543334581/1250000000 : ℝ)^8465 ≤ (6663531083777/20000000000000 : ℝ)^6417 := by
    have hnat : (543334581 : ℕ)^8465*20000000000000^6417 ≤ 6663531083777^6417*1250000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543334581 1250000000 6663531083777 20000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (447361959/1000000000 : ℝ)^8465 ≤ (34607171180361/100000000000000 : ℝ)^6417 := by
    have hnat : (447361959 : ℕ)^8465*100000000000000^6417 ≤ 34607171180361^6417*1000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447361959 1000000000 34607171180361 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2111617229/5000000000 : ℝ)^8465 ≤ (16037586692843/50000000000000 : ℝ)^6417 := by
    have hnat : (2111617229 : ℕ)^8465*50000000000000^6417 ≤ 16037586692843^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111617229 5000000000 16037586692843 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(543334581/1250000000 : ℝ), (447361959/1000000000 : ℝ), (2111617229/5000000000 : ℝ)] ![(6663531083777/20000000000000 : ℝ), (34607171180361/100000000000000 : ℝ), (16037586692843/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(543334581/1250000000 : ℝ)|^8465 ≤ (6663531083777/20000000000000 : ℝ)^6417
        have hw : |(543334581/1250000000 : ℝ)|=(543334581/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(447361959/1000000000 : ℝ)|^8465 ≤ (34607171180361/100000000000000 : ℝ)^6417
        have hw : |(447361959/1000000000 : ℝ)|=(447361959/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2111617229/5000000000 : ℝ)|^8465 ≤ (16037586692843/50000000000000 : ℝ)^6417
        have hw : |(2111617229/5000000000 : ℝ)|=(2111617229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1271_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152016389/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14143/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11493/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11511/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3531/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14143/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11493/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14143/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11493/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14143/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11493/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14143/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11493/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14143/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11493/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14143/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11493/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11493/100000 : ℝ) ^ (529/128 : ℝ) ≤ (13090234862173147/100000000000000000000 : ℝ) := by
    have hpowers : (11493/100000 : ℝ)^529 ≤ (13090234862173147/100000000000000000000 : ℝ)^128 := by
      have hnat : (11493 : ℕ)^529*100000000000000000000^128 ≤ 13090234862173147^128*100000^529 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11493 100000 13090234862173147 100000000000000000000 529 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11493/100000 : ℝ)) (X := (13090234862173147/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hpowhi : (14143/100000 : ℝ) ^ (529/128 : ℝ) ≤ (30856556890937149/100000000000000000000 : ℝ) := by
    have hpowers : (14143/100000 : ℝ)^529 ≤ (30856556890937149/100000000000000000000 : ℝ)^128 := by
      have hnat : (14143 : ℕ)^529*100000000000000000000^128 ≤ 30856556890937149^128*100000^529 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14143 100000 30856556890937149 100000000000000000000 529 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14143/100000 : ℝ)) (X := (30856556890937149/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013090234862173147/50000000000000000000 : ℝ) ≤ (1000063341543503/1000000000000000 : ℝ) ^ (529/128 : ℝ) := by
    have hpowers : (50013090234862173147/50000000000000000000 : ℝ)^128 ≤ (1000063341543503/1000000000000000 : ℝ)^529 := by
      have hnat : (50013090234862173147 : ℕ)^128*1000000000000000^529 ≤ 1000063341543503^529*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013090234862173147 50000000000000000000 1000063341543503 1000000000000000 128 529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000063341543503/1000000000000000 : ℝ)) (X := (50013090234862173147/50000000000000000000 : ℝ)) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505493348969138787/12500000000000000000 : ℝ) ≤ (10001063185750731/10000000000000000 : ℝ) ^ (529/128 : ℝ) := by
    have hpowers : (12505493348969138787/12500000000000000000 : ℝ)^128 ≤ (10001063185750731/10000000000000000 : ℝ)^529 := by
      have hnat : (12505493348969138787 : ℕ)^128*10000000000000000^529 ≤ 10001063185750731^529*12500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505493348969138787 12500000000000000000 10001063185750731 10000000000000000 128 529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001063185750731/10000000000000000 : ℝ)) (X := (12505493348969138787/12500000000000000000 : ℝ)) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030856556890937149/50000000000000000000 : ℝ) ≤ (78136663719269/78125000000000 : ℝ) ^ (529/128 : ℝ) := by
    have hpowers : (50030856556890937149/50000000000000000000 : ℝ)^128 ≤ (78136663719269/78125000000000 : ℝ)^529 := by
      have hnat : (50030856556890937149 : ℕ)^128*78125000000000^529 ≤ 78136663719269^529*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030856556890937149 50000000000000000000 78136663719269 78125000000000 128 529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78136663719269/78125000000000 : ℝ)) (X := (50030856556890937149/50000000000000000000 : ℝ)) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13090234862173147/100000000000000000000 : ℝ) ≤ ((13245899925213063157/13250000000000000000 : ℝ)+2*(429770315701/265000000000000 : ℝ)*(11493/100000 : ℝ))^(529/128 : ℝ) := by
    rw [show (13245899925213063157/13250000000000000000 : ℝ)+2*(429770315701/265000000000000 : ℝ)*(11493/100000 : ℝ)=(1000063341543503/1000000000000000 : ℝ) by norm_num, show 1+2*(13090234862173147/100000000000000000000 : ℝ)=(50013090234862173147/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30856556890937149/100000000000000000000 : ℝ)+(13090234862173147/100000000000000000000 : ℝ) ≤ ((13245899925213063157/13250000000000000000 : ℝ)+(429770315701/265000000000000 : ℝ)*((14143/100000 : ℝ)+(11493/100000 : ℝ)))^(529/128 : ℝ) := by
    rw [show (13245899925213063157/13250000000000000000 : ℝ)+(429770315701/265000000000000 : ℝ)*((14143/100000 : ℝ)+(11493/100000 : ℝ))=(10001063185750731/10000000000000000 : ℝ) by norm_num, show 1+(30856556890937149/100000000000000000000 : ℝ)+(13090234862173147/100000000000000000000 : ℝ)=(12505493348969138787/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30856556890937149/100000000000000000000 : ℝ) ≤ ((13245899925213063157/13250000000000000000 : ℝ)+2*(429770315701/265000000000000 : ℝ)*(14143/100000 : ℝ))^(529/128 : ℝ) := by
    rw [show (13245899925213063157/13250000000000000000 : ℝ)+2*(429770315701/265000000000000 : ℝ)*(14143/100000 : ℝ)=(78136663719269/78125000000000 : ℝ) by norm_num, show 1+2*(30856556890937149/100000000000000000000 : ℝ)=(50030856556890937149/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13245899925213063157/13250000000000000000 : ℝ)*(X 1 0+X 2 0)+(429770315701/265000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (529/128 : ℝ)) (lo := (11493/100000 : ℝ)) (hi := (14143/100000 : ℝ)) (c := (13245899925213063157/13250000000000000000 : ℝ)) (alpha := (429770315701/265000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13245899925213063157/13250000000000000000 : ℝ)*(X 0 1+X 2 1)+(429770315701/265000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (529/128 : ℝ)) (lo := (11493/100000 : ℝ)) (hi := (14143/100000 : ℝ)) (c := (13245899925213063157/13250000000000000000 : ℝ)) (alpha := (429770315701/265000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13245899925213063157/13250000000000000000 : ℝ)*(X 0 2+X 1 2)+(429770315701/265000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (529/128 : ℝ)) (lo := (11493/100000 : ℝ)) (hi := (14143/100000 : ℝ)) (c := (13245899925213063157/13250000000000000000 : ℝ)) (alpha := (429770315701/265000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2106210579/10000000000 : ℝ)*X 0 0+(673849649/1250000000 : ℝ)*X 0 1+(1316863423/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((66802323/125000000 : ℝ)*X 1 0+(-86749771/400000000 : ℝ)*X 1 1+(2633726847/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336046461/2500000000 : ℝ)*X 2 0+(5267453689/10000000000 : ℝ)*X 2 1+(-2168744277/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((869333443/2000000000 : ℝ)*X 0 0+(4222595277/10000000000 : ℝ)*X 0 1+(2237128223/5000000000 : ℝ)*X 0 2+(869333443/2000000000 : ℝ)*X 1 0+(4222595277/10000000000 : ℝ)*X 1 1+(2237128223/5000000000 : ℝ)*X 1 2+(869333443/2000000000 : ℝ)*X 2 0+(4222595277/10000000000 : ℝ)*X 2 1+(2237128223/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2106215203/10000000000 : ℝ)*X 0 0+(5267765823/10000000000 : ℝ)*X 0 1+(5390483927/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312651137/10000000000 : ℝ)*X 1 0+(-2045714043/10000000000 : ℝ)*X 1 1+(673810489/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312651137/10000000000 : ℝ)*X 2 0+(5390483909/10000000000 : ℝ)*X 2 1+(-15982141/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((543334581/1250000000 : ℝ)*X 0 0+(447361959/1000000000 : ℝ)*X 0 1+(2111617229/5000000000 : ℝ)*X 0 2+(543334581/1250000000 : ℝ)*X 1 0+(447361959/1000000000 : ℝ)*X 1 1+(2111617229/5000000000 : ℝ)*X 1 2+(543334581/1250000000 : ℝ)*X 2 0+(447361959/1000000000 : ℝ)*X 2 1+(2111617229/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1017935889570230390372060901/331250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3533291/625000000000 : ℝ)*(base19) + (67206439/12500000000000 : ℝ)*(base23) + (18033049/100000000000000 : ℝ)*(lower2) + (38132129/50000000000000 : ℝ)*(upper3) + (24911281/50000000000000 : ℝ)*(upper5) + (6040542202448669/100000000000000 : ℝ)*(major0) + (6040542202448669/100000000000000 : ℝ)*(major1) + (6040542202448669/100000000000000 : ℝ)*(major2) + (8107456144982991/100000000000000 : ℝ)*(sp0) + (8107471258781973/100000000000000 : ℝ)*(sp1) + (4053735643228511/50000000000000 : ℝ)*(sp2) + (99340105322669/2500000000000 : ℝ)*(sp3) + (7839562771/50000000000000 : ℝ)*(sp4) + (4132724117/50000000000000 : ℝ)*(sp7) + (1986806239177497/50000000000000 : ℝ)*(f.failure) + (4053735912054267/50000000000000 : ℝ)*(f.sum) + (50008502623281/13250000000000000000000000000 : ℝ)*base66 + (12939191317796038033/1325000000000000000000000000000000 : ℝ)*base67 + (18314163703961967/1325000000000000000000000000000000 : ℝ)*base70 + (5337816792746038033/1325000000000000000000000000000000 : ℝ)*base71 + (59244560685719/13250000000000000000000000000 : ℝ)*base73 + (17427772612096038033/1325000000000000000000000000000000 : ℝ)*base75 + (5161678914146038033/1325000000000000000000000000000000 : ℝ)*base77 + (14490313406296038033/1325000000000000000000000000000000 : ℝ)*base79 + (24870905001531/13250000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (26001667/5000000000000000000000 : ℝ)*base90 + (26001667/5000000000000000000000 : ℝ)*base92 + (26001667/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (704453909824971556901124381/82812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (761721131/50000000000000 : ℝ)*(base19) + (1641583341/100000000000000 : ℝ)*(base23) + (82369711/50000000000000 : ℝ)*(upper3) + (27786461/50000000000000 : ℝ)*(lower4) + (17592901/10000000000000 : ℝ)*(upper5) + (1517825346413711/25000000000000 : ℝ)*(major0) + (1517825346413711/25000000000000 : ℝ)*(major1) + (1517825346413711/25000000000000 : ℝ)*(major2) + (42694438309/100000000000000 : ℝ)*(sp1) + (44974876583/100000000000000 : ℝ)*(sp2) + (203718897158777/2500000000000 : ℝ)*(sp4) + (8148711668470509/100000000000000 : ℝ)*(sp5) + (1629741853978231/20000000000000 : ℝ)*(sp6) + (3993846601404829/100000000000000 : ℝ)*(sp7) + (3993846601404829/100000000000000 : ℝ)*(f.failure) + (203718897158777/2500000000000 : ℝ)*(f.sum) + (3098811864589/3312500000000000000000000000 : ℝ)*base66 + (2175237829473204373/331250000000000000000000000000000 : ℝ)*base68 + (1313636268801795627/331250000000000000000000000000000 : ℝ)*base69 + (1249843762941954373/331250000000000000000000000000000 : ℝ)*base72 + (4716543967411/3312500000000000000000000000 : ℝ)*base73 + (338977763585704373/331250000000000000000000000000000 : ℝ)*base76 + (1445785092204454373/331250000000000000000000000000000 : ℝ)*base78 + (1263919637760704373/331250000000000000000000000000000 : ℝ)*base80 + (4759312727447/6625000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (31742481/10000000000000000000000 : ℝ)*base89 + (31742481/10000000000000000000000 : ℝ)*base91 + (31742481/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1271_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152016389/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14143/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11493/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11511/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3531/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1271_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1271_s7_0 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2106225491/10000000000 : ℝ)*x 0 + (5390627137/10000000000 : ℝ)*x 1 + (1316903469/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2106225491/10000000000 : ℝ)^8465 ≤ (12811498166811/100000000000000 : ℝ)^6417 := by
    have hnat : (2106225491 : ℕ)^8465*100000000000000^6417 ≤ 12811498166811^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106225491 10000000000 12811498166811 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390627137/10000000000 : ℝ)^8465 ≤ (22128978851203/50000000000000 : ℝ)^6417 := by
    have hnat : (5390627137 : ℕ)^8465*50000000000000^6417 ≤ 22128978851203^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390627137 10000000000 22128978851203 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316903469/2500000000 : ℝ)^8465 ≤ (42930544111751/100000000000000 : ℝ)^6417 := by
    have hnat : (1316903469 : ℕ)^8465*100000000000000^6417 ≤ 42930544111751^6417*2500000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316903469 2500000000 42930544111751 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2106225491/10000000000 : ℝ), (5390627137/10000000000 : ℝ), (1316903469/2500000000 : ℝ)] ![(12811498166811/100000000000000 : ℝ), (22128978851203/50000000000000 : ℝ), (42930544111751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2106225491/10000000000 : ℝ)|^8465 ≤ (12811498166811/100000000000000 : ℝ)^6417
        have hw : |(-2106225491/10000000000 : ℝ)|=(2106225491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390627137/10000000000 : ℝ)|^8465 ≤ (22128978851203/50000000000000 : ℝ)^6417
        have hw : |(5390627137/10000000000 : ℝ)|=(5390627137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316903469/2500000000 : ℝ)|^8465 ≤ (42930544111751/100000000000000 : ℝ)^6417
        have hw : |(1316903469/2500000000 : ℝ)|=(1316903469/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s7_1 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (66801781/125000000 : ℝ)*x 0 + (-2168589441/10000000000 : ℝ)*x 1 + (5267613899/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66801781/125000000 : ℝ)^8465 ≤ (21877600756103/50000000000000 : ℝ)^6417 := by
    have hnat : (66801781 : ℕ)^8465*50000000000000^6417 ≤ 21877600756103^6417*125000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66801781 125000000 21877600756103 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2168589441/10000000000 : ℝ)^8465 ≤ (6657127058979/50000000000000 : ℝ)^6417 := by
    have hnat : (2168589441 : ℕ)^8465*50000000000000^6417 ≤ 6657127058979^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168589441 10000000000 6657127058979 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267613899/10000000000 : ℝ)^8465 ≤ (42930544359023/100000000000000 : ℝ)^6417 := by
    have hnat : (5267613899 : ℕ)^8465*100000000000000^6417 ≤ 42930544359023^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267613899 10000000000 42930544359023 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66801781/125000000 : ℝ), (-2168589441/10000000000 : ℝ), (5267613899/10000000000 : ℝ)] ![(21877600756103/50000000000000 : ℝ), (6657127058979/50000000000000 : ℝ), (42930544359023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66801781/125000000 : ℝ)|^8465 ≤ (21877600756103/50000000000000 : ℝ)^6417
        have hw : |(66801781/125000000 : ℝ)|=(66801781/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2168589441/10000000000 : ℝ)|^8465 ≤ (6657127058979/50000000000000 : ℝ)^6417
        have hw : |(-2168589441/10000000000 : ℝ)|=(2168589441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267613899/10000000000 : ℝ)|^8465 ≤ (42930544359023/100000000000000 : ℝ)^6417
        have hw : |(5267613899/10000000000 : ℝ)|=(5267613899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s7_2 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672071247/5000000000 : ℝ)*x 0 + (1053522777/2000000000 : ℝ)*x 1 + (-3388421/15625000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672071247/5000000000 : ℝ)^8465 ≤ (21877600831707/50000000000000 : ℝ)^6417 := by
    have hnat : (2672071247 : ℕ)^8465*50000000000000^6417 ≤ 21877600831707^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672071247 5000000000 21877600831707 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053522777/2000000000 : ℝ)^8465 ≤ (42930544208509/100000000000000 : ℝ)^6417 := by
    have hnat : (1053522777 : ℕ)^8465*100000000000000^6417 ≤ 42930544208509^6417*2000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053522777 2000000000 42930544208509 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3388421/15625000 : ℝ)^8465 ≤ (13314254109859/100000000000000 : ℝ)^6417 := by
    have hnat : (3388421 : ℕ)^8465*100000000000000^6417 ≤ 13314254109859^6417*15625000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3388421 15625000 13314254109859 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672071247/5000000000 : ℝ), (1053522777/2000000000 : ℝ), (-3388421/15625000 : ℝ)] ![(21877600831707/50000000000000 : ℝ), (42930544208509/100000000000000 : ℝ), (13314254109859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672071247/5000000000 : ℝ)|^8465 ≤ (21877600831707/50000000000000 : ℝ)^6417
        have hw : |(2672071247/5000000000 : ℝ)|=(2672071247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053522777/2000000000 : ℝ)|^8465 ≤ (42930544208509/100000000000000 : ℝ)^6417
        have hw : |(1053522777/2000000000 : ℝ)|=(1053522777/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3388421/15625000 : ℝ)|^8465 ≤ (13314254109859/100000000000000 : ℝ)^6417
        have hw : |(-3388421/15625000 : ℝ)|=(3388421/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s7_3 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2173337791/5000000000 : ℝ)*x 0 + (4222931103/10000000000 : ℝ)*x 1 + (447391847/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173337791/5000000000 : ℝ)^8465 ≤ (6663528928023/20000000000000 : ℝ)^6417 := by
    have hnat : (2173337791 : ℕ)^8465*20000000000000^6417 ≤ 6663528928023^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173337791 5000000000 6663528928023 20000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4222931103/10000000000 : ℝ)^8465 ≤ (32072134146201/100000000000000 : ℝ)^6417 := by
    have hnat : (4222931103 : ℕ)^8465*100000000000000^6417 ≤ 32072134146201^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4222931103 10000000000 32072134146201 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (447391847/1000000000 : ℝ)^8465 ≤ (3461022120577/10000000000000 : ℝ)^6417 := by
    have hnat : (447391847 : ℕ)^8465*10000000000000^6417 ≤ 3461022120577^6417*1000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447391847 1000000000 3461022120577 10000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2173337791/5000000000 : ℝ), (4222931103/10000000000 : ℝ), (447391847/1000000000 : ℝ)] ![(6663528928023/20000000000000 : ℝ), (32072134146201/100000000000000 : ℝ), (3461022120577/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2173337791/5000000000 : ℝ)|^8465 ≤ (6663528928023/20000000000000 : ℝ)^6417
        have hw : |(2173337791/5000000000 : ℝ)|=(2173337791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4222931103/10000000000 : ℝ)|^8465 ≤ (32072134146201/100000000000000 : ℝ)^6417
        have hw : |(4222931103/10000000000 : ℝ)|=(4222931103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(447391847/1000000000 : ℝ)|^8465 ≤ (3461022120577/10000000000000 : ℝ)^6417
        have hw : |(447391847/1000000000 : ℝ)|=(447391847/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s7_4 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-263278759/1250000000 : ℝ)*x 0 + (2633962211/5000000000 : ℝ)*x 1 + (539031547/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263278759/1250000000 : ℝ)^8465 ≤ (800720932793/6250000000000 : ℝ)^6417 := by
    have hnat : (263278759 : ℕ)^8465*6250000000000^6417 ≤ 800720932793^6417*1250000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263278759 1250000000 800720932793 6250000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633962211/5000000000 : ℝ)^8465 ≤ (10733470702959/25000000000000 : ℝ)^6417 := by
    have hnat : (2633962211 : ℕ)^8465*25000000000000^6417 ≤ 10733470702959^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633962211 5000000000 10733470702959 25000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539031547/1000000000 : ℝ)^8465 ≤ (22127291117911/50000000000000 : ℝ)^6417 := by
    have hnat : (539031547 : ℕ)^8465*50000000000000^6417 ≤ 22127291117911^6417*1000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539031547 1000000000 22127291117911 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-263278759/1250000000 : ℝ), (2633962211/5000000000 : ℝ), (539031547/1000000000 : ℝ)] ![(800720932793/6250000000000 : ℝ), (10733470702959/25000000000000 : ℝ), (22127291117911/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-263278759/1250000000 : ℝ)|^8465 ≤ (800720932793/6250000000000 : ℝ)^6417
        have hw : |(-263278759/1250000000 : ℝ)|=(263278759/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633962211/5000000000 : ℝ)|^8465 ≤ (10733470702959/25000000000000 : ℝ)^6417
        have hw : |(2633962211/5000000000 : ℝ)|=(2633962211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539031547/1000000000 : ℝ)|^8465 ≤ (22127291117911/50000000000000 : ℝ)^6417
        have hw : |(539031547/1000000000 : ℝ)|=(539031547/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s7_5 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656346093/5000000000 : ℝ)*x 0 + (-409177571/2000000000 : ℝ)*x 1 + (539031547/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656346093/5000000000 : ℝ)^8465 ≤ (21707919953277/50000000000000 : ℝ)^6417 := by
    have hnat : (2656346093 : ℕ)^8465*50000000000000^6417 ≤ 21707919953277^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656346093 5000000000 21707919953277 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (409177571/2000000000 : ℝ)^8465 ≤ (6164788918671/50000000000000 : ℝ)^6417 := by
    have hnat : (409177571 : ℕ)^8465*50000000000000^6417 ≤ 6164788918671^6417*2000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409177571 2000000000 6164788918671 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539031547/1000000000 : ℝ)^8465 ≤ (22127291117911/50000000000000 : ℝ)^6417 := by
    have hnat : (539031547 : ℕ)^8465*50000000000000^6417 ≤ 22127291117911^6417*1000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539031547 1000000000 22127291117911 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656346093/5000000000 : ℝ), (-409177571/2000000000 : ℝ), (539031547/1000000000 : ℝ)] ![(21707919953277/50000000000000 : ℝ), (6164788918671/50000000000000 : ℝ), (22127291117911/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656346093/5000000000 : ℝ)|^8465 ≤ (21707919953277/50000000000000 : ℝ)^6417
        have hw : |(2656346093/5000000000 : ℝ)|=(2656346093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-409177571/2000000000 : ℝ)|^8465 ≤ (6164788918671/50000000000000 : ℝ)^6417
        have hw : |(-409177571/2000000000 : ℝ)|=(409177571/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539031547/1000000000 : ℝ)|^8465 ≤ (22127291117911/50000000000000 : ℝ)^6417
        have hw : |(539031547/1000000000 : ℝ)|=(539031547/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s7_6 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312692187/10000000000 : ℝ)*x 0 + (5390315471/10000000000 : ℝ)*x 1 + (-2045887853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312692187/10000000000 : ℝ)^8465 ≤ (21707919958667/50000000000000 : ℝ)^6417 := by
    have hnat : (5312692187 : ℕ)^8465*50000000000000^6417 ≤ 21707919958667^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312692187 10000000000 21707919958667 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390315471/10000000000 : ℝ)^8465 ≤ (11063645561663/25000000000000 : ℝ)^6417 := by
    have hnat : (5390315471 : ℕ)^8465*25000000000000^6417 ≤ 11063645561663^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390315471 10000000000 11063645561663 25000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2045887853/10000000000 : ℝ)^8465 ≤ (12329577821443/100000000000000 : ℝ)^6417 := by
    have hnat : (2045887853 : ℕ)^8465*100000000000000^6417 ≤ 12329577821443^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2045887853 10000000000 12329577821443 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312692187/10000000000 : ℝ), (5390315471/10000000000 : ℝ), (-2045887853/10000000000 : ℝ)] ![(21707919958667/50000000000000 : ℝ), (11063645561663/25000000000000 : ℝ), (12329577821443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312692187/10000000000 : ℝ)|^8465 ≤ (21707919958667/50000000000000 : ℝ)^6417
        have hw : |(5312692187/10000000000 : ℝ)|=(5312692187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390315471/10000000000 : ℝ)|^8465 ≤ (11063645561663/25000000000000 : ℝ)^6417
        have hw : |(5390315471/10000000000 : ℝ)|=(5390315471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2045887853/10000000000 : ℝ)|^8465 ≤ (12329577821443/100000000000000 : ℝ)^6417
        have hw : |(-2045887853/10000000000 : ℝ)|=(2045887853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s7_7 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4346684919/10000000000 : ℝ)*x 0 + (1118321221/2500000000 : ℝ)*x 1 + (2111783509/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4346684919/10000000000 : ℝ)^8465 ≤ (33317739050441/100000000000000 : ℝ)^6417 := by
    have hnat : (4346684919 : ℕ)^8465*100000000000000^6417 ≤ 33317739050441^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4346684919 10000000000 33317739050441 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1118321221/2500000000 : ℝ)^8465 ≤ (4325469454151/12500000000000 : ℝ)^6417 := by
    have hnat : (1118321221 : ℕ)^8465*12500000000000^6417 ≤ 4325469454151^6417*2500000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118321221 2500000000 4325469454151 12500000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2111783509/5000000000 : ℝ)^8465 ≤ (1283140212119/4000000000000 : ℝ)^6417 := by
    have hnat : (2111783509 : ℕ)^8465*4000000000000^6417 ≤ 1283140212119^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111783509 5000000000 1283140212119 4000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4346684919/10000000000 : ℝ), (1118321221/2500000000 : ℝ), (2111783509/5000000000 : ℝ)] ![(33317739050441/100000000000000 : ℝ), (4325469454151/12500000000000 : ℝ), (1283140212119/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4346684919/10000000000 : ℝ)|^8465 ≤ (33317739050441/100000000000000 : ℝ)^6417
        have hw : |(4346684919/10000000000 : ℝ)|=(4346684919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1118321221/2500000000 : ℝ)|^8465 ≤ (4325469454151/12500000000000 : ℝ)^6417
        have hw : |(1118321221/2500000000 : ℝ)|=(1118321221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2111783509/5000000000 : ℝ)|^8465 ≤ (1283140212119/4000000000000 : ℝ)^6417
        have hw : |(2111783509/5000000000 : ℝ)|=(2111783509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1271_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152016389/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3531/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11511/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5757/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (353/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3531/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11511/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3531/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11511/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3531/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11511/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3531/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11511/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3531/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11511/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3531/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11511/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11511/100000 : ℝ) ^ (529/128 : ℝ) ≤ (3293792996746353/25000000000000000000 : ℝ) := by
    have hpowers : (11511/100000 : ℝ)^529 ≤ (3293792996746353/25000000000000000000 : ℝ)^128 := by
      have hnat : (11511 : ℕ)^529*25000000000000000000^128 ≤ 3293792996746353^128*100000^529 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11511 100000 3293792996746353 25000000000000000000 529 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11511/100000 : ℝ)) (X := (3293792996746353/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hpowhi : (3531/25000 : ℝ) ^ (529/128 : ℝ) ≤ (6137119636123193/20000000000000000000 : ℝ) := by
    have hpowers : (3531/25000 : ℝ)^529 ≤ (6137119636123193/20000000000000000000 : ℝ)^128 := by
      have hnat : (3531 : ℕ)^529*20000000000000000000^128 ≤ 6137119636123193^128*25000^529 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3531 25000 6137119636123193 20000000000000000000 529 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3531/25000 : ℝ)) (X := (6137119636123193/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503293792996746353/12500000000000000000 : ℝ) ≤ (5000318762497829/5000000000000000 : ℝ) ^ (529/128 : ℝ) := by
    have hpowers : (12503293792996746353/12500000000000000000 : ℝ)^128 ≤ (5000318762497829/5000000000000000 : ℝ)^529 := by
      have hnat : (12503293792996746353 : ℕ)^128*5000000000000000^529 ≤ 5000318762497829^529*12500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503293792996746353 12500000000000000000 5000318762497829 5000000000000000 128 529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000318762497829/5000000000000000 : ℝ)) (X := (12503293792996746353/12500000000000000000 : ℝ)) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100043860770167601377/100000000000000000000 : ℝ) ≤ (10001061105013507/10000000000000000 : ℝ) ^ (529/128 : ℝ) := by
    have hpowers : (100043860770167601377/100000000000000000000 : ℝ)^128 ≤ (10001061105013507/10000000000000000 : ℝ)^529 := by
      have hnat : (100043860770167601377 : ℕ)^128*10000000000000000^529 ≤ 10001061105013507^529*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100043860770167601377 100000000000000000000 10001061105013507 10000000000000000 128 529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001061105013507/10000000000000000 : ℝ)) (X := (100043860770167601377/100000000000000000000 : ℝ)) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006137119636123193/10000000000000000000 : ℝ) ≤ (2500371171257839/2500000000000000 : ℝ) ^ (529/128 : ℝ) := by
    have hpowers : (10006137119636123193/10000000000000000000 : ℝ)^128 ≤ (2500371171257839/2500000000000000 : ℝ)^529 := by
      have hnat : (10006137119636123193 : ℕ)^128*2500000000000000^529 ≤ 2500371171257839^529*10000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006137119636123193 10000000000000000000 2500371171257839 2500000000000000 128 529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500371171257839/2500000000000000 : ℝ)) (X := (10006137119636123193/10000000000000000000 : ℝ)) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3293792996746353/25000000000000000000 : ℝ) ≤ ((2176826182803561223/2177500000000000000 : ℝ)+2*(141193339283/87100000000000 : ℝ)*(11511/100000 : ℝ))^(529/128 : ℝ) := by
    rw [show (2176826182803561223/2177500000000000000 : ℝ)+2*(141193339283/87100000000000 : ℝ)*(11511/100000 : ℝ)=(5000318762497829/5000000000000000 : ℝ) by norm_num, show 1+2*(3293792996746353/25000000000000000000 : ℝ)=(12503293792996746353/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6137119636123193/20000000000000000000 : ℝ)+(3293792996746353/25000000000000000000 : ℝ) ≤ ((2176826182803561223/2177500000000000000 : ℝ)+(141193339283/87100000000000 : ℝ)*((3531/25000 : ℝ)+(11511/100000 : ℝ)))^(529/128 : ℝ) := by
    rw [show (2176826182803561223/2177500000000000000 : ℝ)+(141193339283/87100000000000 : ℝ)*((3531/25000 : ℝ)+(11511/100000 : ℝ))=(10001061105013507/10000000000000000 : ℝ) by norm_num, show 1+(6137119636123193/20000000000000000000 : ℝ)+(3293792996746353/25000000000000000000 : ℝ)=(100043860770167601377/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6137119636123193/20000000000000000000 : ℝ) ≤ ((2176826182803561223/2177500000000000000 : ℝ)+2*(141193339283/87100000000000 : ℝ)*(3531/25000 : ℝ))^(529/128 : ℝ) := by
    rw [show (2176826182803561223/2177500000000000000 : ℝ)+2*(141193339283/87100000000000 : ℝ)*(3531/25000 : ℝ)=(2500371171257839/2500000000000000 : ℝ) by norm_num, show 1+2*(6137119636123193/20000000000000000000 : ℝ)=(10006137119636123193/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2176826182803561223/2177500000000000000 : ℝ)*(X 1 0+X 2 0)+(141193339283/87100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (529/128 : ℝ)) (lo := (11511/100000 : ℝ)) (hi := (3531/25000 : ℝ)) (c := (2176826182803561223/2177500000000000000 : ℝ)) (alpha := (141193339283/87100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2176826182803561223/2177500000000000000 : ℝ)*(X 0 1+X 2 1)+(141193339283/87100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (529/128 : ℝ)) (lo := (11511/100000 : ℝ)) (hi := (3531/25000 : ℝ)) (c := (2176826182803561223/2177500000000000000 : ℝ)) (alpha := (141193339283/87100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2176826182803561223/2177500000000000000 : ℝ)*(X 0 2+X 1 2)+(141193339283/87100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (529/128 : ℝ)) (lo := (11511/100000 : ℝ)) (hi := (3531/25000 : ℝ)) (c := (2176826182803561223/2177500000000000000 : ℝ)) (alpha := (141193339283/87100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2106225491/10000000000 : ℝ)*X 0 0+(5390627137/10000000000 : ℝ)*X 0 1+(1316903469/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((66801781/125000000 : ℝ)*X 1 0+(-2168589441/10000000000 : ℝ)*X 1 1+(5267613899/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672071247/5000000000 : ℝ)*X 2 0+(1053522777/2000000000 : ℝ)*X 2 1+(-3388421/15625000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2173337791/5000000000 : ℝ)*X 0 0+(4222931103/10000000000 : ℝ)*X 0 1+(447391847/1000000000 : ℝ)*X 0 2+(2173337791/5000000000 : ℝ)*X 1 0+(4222931103/10000000000 : ℝ)*X 1 1+(447391847/1000000000 : ℝ)*X 1 2+(2173337791/5000000000 : ℝ)*X 2 0+(4222931103/10000000000 : ℝ)*X 2 1+(447391847/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-263278759/1250000000 : ℝ)*X 0 0+(2633962211/5000000000 : ℝ)*X 0 1+(539031547/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656346093/5000000000 : ℝ)*X 1 0+(-409177571/2000000000 : ℝ)*X 1 1+(539031547/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312692187/10000000000 : ℝ)*X 2 0+(5390315471/10000000000 : ℝ)*X 2 1+(-2045887853/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4346684919/10000000000 : ℝ)*X 0 0+(1118321221/2500000000 : ℝ)*X 0 1+(2111783509/5000000000 : ℝ)*X 0 2+(4346684919/10000000000 : ℝ)*X 1 0+(1118321221/2500000000 : ℝ)*X 1 1+(2111783509/5000000000 : ℝ)*X 1 2+(4346684919/10000000000 : ℝ)*X 2 0+(1118321221/2500000000 : ℝ)*X 2 1+(2111783509/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (377084674088939484405215481/54437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1347890701/100000000000000 : ℝ)*(base19) + (254341941/20000000000000 : ℝ)*(base23) + (13023301/25000000000000 : ℝ)*(lower2) + (183070429/100000000000000 : ℝ)*(upper3) + (23305609/20000000000000 : ℝ)*(upper5) + (6056793204960349/100000000000000 : ℝ)*(major0) + (6056793204960349/100000000000000 : ℝ)*(major1) + (6056793204960349/100000000000000 : ℝ)*(major2) + (406462240733783/5000000000000 : ℝ)*(sp0) + (8129282056409609/100000000000000 : ℝ)*(sp1) + (1625856426518121/20000000000000 : ℝ)*(sp2) + (62254413455653/1562500000000 : ℝ)*(sp3) + (771792493/2000000000000 : ℝ)*(sp4) + (5078390243/25000000000000 : ℝ)*(sp7) + (3984302774722763/100000000000000 : ℝ)*(f.failure) + (812928340430031/10000000000000 : ℝ)*(f.sum) + (21147686543193/4355000000000000000000000000 : ℝ)*base66 + (505108525752878173/217750000000000000000000000000000 : ℝ)*base68 + (1905189169025878173/217750000000000000000000000000000 : ℝ)*base70 + (927518046389878173/217750000000000000000000000000000 : ℝ)*base72 + (12660334447879/2177500000000000000000000000 : ℝ)*base74 + (62887192273871827/217750000000000000000000000000000 : ℝ)*base75 + (2397021025652378173/217750000000000000000000000000000 : ℝ)*base78 + (1315348154766628173/217750000000000000000000000000000 : ℝ)*base80 + (24225313584513/4355000000000000000000000000 : ℝ)*base82 + (7362807/10000000000000000000000 : ℝ)*base89 + (7362807/10000000000000000000000 : ℝ)*base91 + (7362807/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1868971172343159307647/435500000000000000000000000 : ℝ) := by norm_num
    linear_combination (771954777/100000000000000 : ℝ)*(base19) + (168137573/20000000000000 : ℝ)*(base23) + (88246397/100000000000000 : ℝ)*(upper3) + (29706189/100000000000000 : ℝ)*(lower4) + (21484789/25000000000000 : ℝ)*(upper5) + (608752522446797/10000000000000 : ℝ)*(major0) + (608752522446797/10000000000000 : ℝ)*(major1) + (608752522446797/10000000000000 : ℝ)*(major2) + (21809044449/100000000000000 : ℝ)*(sp1) + (5928608013/25000000000000 : ℝ)*(sp2) + (8170531277039223/100000000000000 : ℝ)*(sp4) + (8170508696039997/100000000000000 : ℝ)*(sp5) + (1634101344383861/20000000000000 : ℝ)*(sp6) + (1001129757211239/25000000000000 : ℝ)*(sp7) + (1001129757211239/25000000000000 : ℝ)*(f.failure) + (8170531277039223/100000000000000 : ℝ)*(f.sum) + (291988986683/435500000000000000000000000 : ℝ)*base66 + (22954376265777731/21775000000000000000000000000000 : ℝ)*base67 + (93088775353422269/21775000000000000000000000000000 : ℝ)*base70 + (288942586765122269/21775000000000000000000000000000 : ℝ)*base72 + (1671888658379/435500000000000000000000000 : ℝ)*base74 + (256300466488447269/21775000000000000000000000000000 : ℝ)*base76 + (55704910914102731/21775000000000000000000000000000 : ℝ)*base77 + (112978637500802731/21775000000000000000000000000000 : ℝ)*base79 + (6383552076871/871000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (12995971/2500000000000000000000 : ℝ)*base89 + (12995971/2500000000000000000000 : ℝ)*base91 + (12995971/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1271_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152016389/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3531/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11511/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5757/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (353/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1271_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1271_s8_0 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1053115297/5000000000 : ℝ)*x 0 + (5390594133/10000000000 : ℝ)*x 1 + (1053528663/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053115297/5000000000 : ℝ)^8465 ≤ (1281153911321/10000000000000 : ℝ)^6417 := by
    have hnat : (1053115297 : ℕ)^8465*10000000000000^6417 ≤ 1281153911321^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053115297 5000000000 1281153911321 10000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390594133/10000000000 : ℝ)^8465 ≤ (22128800127087/50000000000000 : ℝ)^6417 := by
    have hnat : (5390594133 : ℕ)^8465*50000000000000^6417 ≤ 22128800127087^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390594133 10000000000 22128800127087 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053528663/2000000000 : ℝ)^8465 ≤ (10732715152411/25000000000000 : ℝ)^6417 := by
    have hnat : (1053528663 : ℕ)^8465*25000000000000^6417 ≤ 10732715152411^6417*2000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053528663 2000000000 10732715152411 25000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1053115297/5000000000 : ℝ), (5390594133/10000000000 : ℝ), (1053528663/2000000000 : ℝ)] ![(1281153911321/10000000000000 : ℝ), (22128800127087/50000000000000 : ℝ), (10732715152411/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1053115297/5000000000 : ℝ)|^8465 ≤ (1281153911321/10000000000000 : ℝ)^6417
        have hw : |(-1053115297/5000000000 : ℝ)|=(1053115297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390594133/10000000000 : ℝ)|^8465 ≤ (22128800127087/50000000000000 : ℝ)^6417
        have hw : |(5390594133/10000000000 : ℝ)|=(5390594133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053528663/2000000000 : ℝ)|^8465 ≤ (10732715152411/25000000000000 : ℝ)^6417
        have hw : |(1053528663/2000000000 : ℝ)|=(1053528663/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s8_1 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534413337/1000000000 : ℝ)*x 0 + (-1084281251/5000000000 : ℝ)*x 1 + (329227709/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534413337/1000000000 : ℝ)^8465 ≤ (43755103119061/100000000000000 : ℝ)^6417 := by
    have hnat : (534413337 : ℕ)^8465*100000000000000^6417 ≤ 43755103119061^6417*1000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534413337 1000000000 43755103119061 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1084281251/5000000000 : ℝ)^8465 ≤ (13314035937909/100000000000000 : ℝ)^6417 := by
    have hnat : (1084281251 : ℕ)^8465*100000000000000^6417 ≤ 13314035937909^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084281251 5000000000 13314035937909 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329227709/625000000 : ℝ)^8465 ≤ (42930860921423/100000000000000 : ℝ)^6417 := by
    have hnat : (329227709 : ℕ)^8465*100000000000000^6417 ≤ 42930860921423^6417*625000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329227709 625000000 42930860921423 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534413337/1000000000 : ℝ), (-1084281251/5000000000 : ℝ), (329227709/625000000 : ℝ)] ![(43755103119061/100000000000000 : ℝ), (13314035937909/100000000000000 : ℝ), (42930860921423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534413337/1000000000 : ℝ)|^8465 ≤ (43755103119061/100000000000000 : ℝ)^6417
        have hw : |(534413337/1000000000 : ℝ)|=(534413337/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1084281251/5000000000 : ℝ)|^8465 ≤ (13314035937909/100000000000000 : ℝ)^6417
        have hw : |(-1084281251/5000000000 : ℝ)|=(1084281251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329227709/625000000 : ℝ)|^8465 ≤ (42930860921423/100000000000000 : ℝ)^6417
        have hw : |(329227709/625000000 : ℝ)|=(329227709/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s8_2 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336033347/2500000000 : ℝ)*x 0 + (329227711/625000000 : ℝ)*x 1 + (-2168562437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336033347/2500000000 : ℝ)^8465 ≤ (43755103313471/100000000000000 : ℝ)^6417 := by
    have hnat : (1336033347 : ℕ)^8465*100000000000000^6417 ≤ 43755103313471^6417*2500000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336033347 2500000000 43755103313471 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329227711/625000000 : ℝ)^8465 ≤ (21465430632727/50000000000000 : ℝ)^6417 := by
    have hnat : (329227711 : ℕ)^8465*50000000000000^6417 ≤ 21465430632727^6417*625000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329227711 625000000 21465430632727 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2168562437/10000000000 : ℝ)^8465 ≤ (832127213217/6250000000000 : ℝ)^6417 := by
    have hnat : (2168562437 : ℕ)^8465*6250000000000^6417 ≤ 832127213217^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168562437 10000000000 832127213217 6250000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336033347/2500000000 : ℝ), (329227711/625000000 : ℝ), (-2168562437/10000000000 : ℝ)] ![(43755103313471/100000000000000 : ℝ), (21465430632727/50000000000000 : ℝ), (832127213217/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336033347/2500000000 : ℝ)|^8465 ≤ (43755103313471/100000000000000 : ℝ)^6417
        have hw : |(1336033347/2500000000 : ℝ)|=(1336033347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329227711/625000000 : ℝ)|^8465 ≤ (21465430632727/50000000000000 : ℝ)^6417
        have hw : |(329227711/625000000 : ℝ)|=(329227711/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2168562437/10000000000 : ℝ)|^8465 ≤ (832127213217/6250000000000 : ℝ)^6417
        have hw : |(-2168562437/10000000000 : ℝ)|=(2168562437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s8_3 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2173338591/5000000000 : ℝ)*x 0 + (4222994723/10000000000 : ℝ)*x 1 + (178954177/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173338591/5000000000 : ℝ)^8465 ≤ (16658830409191/50000000000000 : ℝ)^6417 := by
    have hnat : (2173338591 : ℕ)^8465*50000000000000^6417 ≤ 16658830409191^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173338591 5000000000 16658830409191 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4222994723/10000000000 : ℝ)^8465 ≤ (32072771533633/100000000000000 : ℝ)^6417 := by
    have hnat : (4222994723 : ℕ)^8465*100000000000000^6417 ≤ 32072771533633^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4222994723 10000000000 32072771533633 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (178954177/400000000 : ℝ)^8465 ≤ (34609567630711/100000000000000 : ℝ)^6417 := by
    have hnat : (178954177 : ℕ)^8465*100000000000000^6417 ≤ 34609567630711^6417*400000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      178954177 400000000 34609567630711 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2173338591/5000000000 : ℝ), (4222994723/10000000000 : ℝ), (178954177/400000000 : ℝ)] ![(16658830409191/50000000000000 : ℝ), (32072771533633/100000000000000 : ℝ), (34609567630711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2173338591/5000000000 : ℝ)|^8465 ≤ (16658830409191/50000000000000 : ℝ)^6417
        have hw : |(2173338591/5000000000 : ℝ)|=(2173338591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4222994723/10000000000 : ℝ)|^8465 ≤ (32072771533633/100000000000000 : ℝ)^6417
        have hw : |(4222994723/10000000000 : ℝ)|=(4222994723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(178954177/400000000 : ℝ)|^8465 ≤ (34609567630711/100000000000000 : ℝ)^6417
        have hw : |(178954177/400000000 : ℝ)|=(178954177/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s8_4 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-131639707/625000000 : ℝ)*x 0 + (1053590707/2000000000 : ℝ)*x 1 + (84223167/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131639707/625000000 : ℝ)^8465 ≤ (6405788485201/50000000000000 : ℝ)^6417 := by
    have hnat : (131639707 : ℕ)^8465*50000000000000^6417 ≤ 6405788485201^6417*625000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131639707 625000000 6405788485201 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053590707/2000000000 : ℝ)^8465 ≤ (21467097905399/50000000000000 : ℝ)^6417 := by
    have hnat : (1053590707 : ℕ)^8465*50000000000000^6417 ≤ 21467097905399^6417*2000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053590707 2000000000 21467097905399 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84223167/156250000 : ℝ)^8465 ≤ (44254227198499/100000000000000 : ℝ)^6417 := by
    have hnat : (84223167 : ℕ)^8465*100000000000000^6417 ≤ 44254227198499^6417*156250000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84223167 156250000 44254227198499 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-131639707/625000000 : ℝ), (1053590707/2000000000 : ℝ), (84223167/156250000 : ℝ)] ![(6405788485201/50000000000000 : ℝ), (21467097905399/50000000000000 : ℝ), (44254227198499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-131639707/625000000 : ℝ)|^8465 ≤ (6405788485201/50000000000000 : ℝ)^6417
        have hw : |(-131639707/625000000 : ℝ)|=(131639707/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053590707/2000000000 : ℝ)|^8465 ≤ (21467097905399/50000000000000 : ℝ)^6417
        have hw : |(1053590707/2000000000 : ℝ)|=(1053590707/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84223167/156250000 : ℝ)|^8465 ≤ (44254227198499/100000000000000 : ℝ)^6417
        have hw : |(84223167/156250000 : ℝ)|=(84223167/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s8_5 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1086671591/2500000000 : ℝ)*x 0 + (4473221593/10000000000 : ℝ)*x 1 + (4223630021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086671591/2500000000 : ℝ)^8465 ≤ (4164719207681/12500000000000 : ℝ)^6417 := by
    have hnat : (1086671591 : ℕ)^8465*12500000000000^6417 ≤ 4164719207681^6417*2500000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086671591 2500000000 4164719207681 12500000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4473221593/10000000000 : ℝ)^8465 ≤ (34603109781847/100000000000000 : ℝ)^6417 := by
    have hnat : (4473221593 : ℕ)^8465*100000000000000^6417 ≤ 34603109781847^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4473221593 10000000000 34603109781847 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4223630021/10000000000 : ℝ)^8465 ≤ (3207913653921/10000000000000 : ℝ)^6417 := by
    have hnat : (4223630021 : ℕ)^8465*10000000000000^6417 ≤ 3207913653921^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4223630021 10000000000 3207913653921 10000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1086671591/2500000000 : ℝ), (4473221593/10000000000 : ℝ), (4223630021/10000000000 : ℝ)] ![(4164719207681/12500000000000 : ℝ), (34603109781847/100000000000000 : ℝ), (3207913653921/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1086671591/2500000000 : ℝ)|^8465 ≤ (4164719207681/12500000000000 : ℝ)^6417
        have hw : |(1086671591/2500000000 : ℝ)|=(1086671591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4473221593/10000000000 : ℝ)|^8465 ≤ (34603109781847/100000000000000 : ℝ)^6417
        have hw : |(4473221593/10000000000 : ℝ)|=(4473221593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4223630021/10000000000 : ℝ)|^8465 ≤ (3207913653921/10000000000000 : ℝ)^6417
        have hw : |(4223630021/10000000000 : ℝ)|=(4223630021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1271_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152016389/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (353/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5757/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2303/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (353/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (353/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5757/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (353/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5757/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (353/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5757/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (353/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5757/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (353/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5757/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (353/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5757/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5757/50000 : ℝ) ^ (529/128 : ℝ) ≤ (6594684344851059/50000000000000000000 : ℝ) := by
    have hpowers : (5757/50000 : ℝ)^529 ≤ (6594684344851059/50000000000000000000 : ℝ)^128 := by
      have hnat : (5757 : ℕ)^529*50000000000000000000^128 ≤ 6594684344851059^128*50000^529 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5757 50000 6594684344851059 50000000000000000000 529 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5757/50000 : ℝ)) (X := (6594684344851059/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hpowhi : (353/2500 : ℝ) ^ (529/128 : ℝ) ≤ (15324849277690073/50000000000000000000 : ℝ) := by
    have hpowers : (353/2500 : ℝ)^529 ≤ (15324849277690073/50000000000000000000 : ℝ)^128 := by
      have hnat : (353 : ℕ)^529*50000000000000000000^128 ≤ 15324849277690073^128*2500^529 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        353 2500 15324849277690073 50000000000000000000 529 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (353/2500 : ℝ)) (X := (15324849277690073/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006594684344851059/25000000000000000000 : ℝ) ≤ (2000127642376437/2000000000000000 : ℝ) ^ (529/128 : ℝ) := by
    have hpowers : (25006594684344851059/25000000000000000000 : ℝ)^128 ≤ (2000127642376437/2000000000000000 : ℝ)^529 := by
      have hnat : (25006594684344851059 : ℕ)^128*2000000000000000^529 ≤ 2000127642376437^529*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006594684344851059 25000000000000000000 2000127642376437 2000000000000000 128 529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000127642376437/2000000000000000 : ℝ)) (X := (25006594684344851059/25000000000000000000 : ℝ)) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505479883405635283/12500000000000000000 : ℝ) ≤ (2500265145012779/2500000000000000 : ℝ) ^ (529/128 : ℝ) := by
    have hpowers : (12505479883405635283/12500000000000000000 : ℝ)^128 ≤ (2500265145012779/2500000000000000 : ℝ)^529 := by
      have hnat : (12505479883405635283 : ℕ)^128*2500000000000000^529 ≤ 2500265145012779^529*12500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505479883405635283 12500000000000000000 2500265145012779 2500000000000000 128 529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500265145012779/2500000000000000 : ℝ)) (X := (12505479883405635283/12500000000000000000 : ℝ)) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015324849277690073/25000000000000000000 : ℝ) ≤ (10001482948220047/10000000000000000 : ℝ) ^ (529/128 : ℝ) := by
    have hpowers : (25015324849277690073/25000000000000000000 : ℝ)^128 ≤ (10001482948220047/10000000000000000 : ℝ)^529 := by
      have hnat : (25015324849277690073 : ℕ)^128*10000000000000000^529 ≤ 10001482948220047^529*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015324849277690073 25000000000000000000 10001482948220047 10000000000000000 128 529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001482948220047/10000000000000000 : ℝ)) (X := (25015324849277690073/25000000000000000000 : ℝ)) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6594684344851059/50000000000000000000 : ℝ) ≤ ((13025968442985415521/13030000000000000000 : ℝ)+2*(422368168931/260600000000000 : ℝ)*(5757/50000 : ℝ))^(529/128 : ℝ) := by
    rw [show (13025968442985415521/13030000000000000000 : ℝ)+2*(422368168931/260600000000000 : ℝ)*(5757/50000 : ℝ)=(2000127642376437/2000000000000000 : ℝ) by norm_num, show 1+2*(6594684344851059/50000000000000000000 : ℝ)=(25006594684344851059/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15324849277690073/50000000000000000000 : ℝ)+(6594684344851059/50000000000000000000 : ℝ) ≤ ((13025968442985415521/13030000000000000000 : ℝ)+(422368168931/260600000000000 : ℝ)*((353/2500 : ℝ)+(5757/50000 : ℝ)))^(529/128 : ℝ) := by
    rw [show (13025968442985415521/13030000000000000000 : ℝ)+(422368168931/260600000000000 : ℝ)*((353/2500 : ℝ)+(5757/50000 : ℝ))=(2500265145012779/2500000000000000 : ℝ) by norm_num, show 1+(15324849277690073/50000000000000000000 : ℝ)+(6594684344851059/50000000000000000000 : ℝ)=(12505479883405635283/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15324849277690073/50000000000000000000 : ℝ) ≤ ((13025968442985415521/13030000000000000000 : ℝ)+2*(422368168931/260600000000000 : ℝ)*(353/2500 : ℝ))^(529/128 : ℝ) := by
    rw [show (13025968442985415521/13030000000000000000 : ℝ)+2*(422368168931/260600000000000 : ℝ)*(353/2500 : ℝ)=(10001482948220047/10000000000000000 : ℝ) by norm_num, show 1+2*(15324849277690073/50000000000000000000 : ℝ)=(25015324849277690073/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13025968442985415521/13030000000000000000 : ℝ)*(X 1 0+X 2 0)+(422368168931/260600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (529/128 : ℝ)) (lo := (5757/50000 : ℝ)) (hi := (353/2500 : ℝ)) (c := (13025968442985415521/13030000000000000000 : ℝ)) (alpha := (422368168931/260600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13025968442985415521/13030000000000000000 : ℝ)*(X 0 1+X 2 1)+(422368168931/260600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (529/128 : ℝ)) (lo := (5757/50000 : ℝ)) (hi := (353/2500 : ℝ)) (c := (13025968442985415521/13030000000000000000 : ℝ)) (alpha := (422368168931/260600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13025968442985415521/13030000000000000000 : ℝ)*(X 0 2+X 1 2)+(422368168931/260600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (529/128 : ℝ)) (lo := (5757/50000 : ℝ)) (hi := (353/2500 : ℝ)) (c := (13025968442985415521/13030000000000000000 : ℝ)) (alpha := (422368168931/260600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1053115297/5000000000 : ℝ)*X 0 0+(5390594133/10000000000 : ℝ)*X 0 1+(1053528663/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534413337/1000000000 : ℝ)*X 1 0+(-1084281251/5000000000 : ℝ)*X 1 1+(329227709/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336033347/2500000000 : ℝ)*X 2 0+(329227711/625000000 : ℝ)*X 2 1+(-2168562437/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2173338591/5000000000 : ℝ)*X 0 0+(4222994723/10000000000 : ℝ)*X 0 1+(178954177/400000000 : ℝ)*X 0 2+(2173338591/5000000000 : ℝ)*X 1 0+(4222994723/10000000000 : ℝ)*X 1 1+(178954177/400000000 : ℝ)*X 1 2+(2173338591/5000000000 : ℝ)*X 2 0+(4222994723/10000000000 : ℝ)*X 2 1+(178954177/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-131639707/625000000 : ℝ)*X 0 0+(1053590707/2000000000 : ℝ)*X 0 1+(84223167/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1086671591/2500000000 : ℝ)*X 0 0+(4473221593/10000000000 : ℝ)*X 0 1+(4223630021/10000000000 : ℝ)*X 0 2+(1086671591/2500000000 : ℝ)*X 1 0+(4473221593/10000000000 : ℝ)*X 1 1+(4223630021/10000000000 : ℝ)*X 1 2+(1086671591/2500000000 : ℝ)*X 2 0+(4473221593/10000000000 : ℝ)*X 2 1+(4223630021/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s8_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2401975881270139410178781571/651500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26568497/4000000000000 : ℝ)*(base19) + (19950413/4000000000000 : ℝ)*(base23) + (103059881/100000000000000 : ℝ)*(lower2) + (14192331/20000000000000 : ℝ)*(upper3) + (21847203/50000000000000 : ℝ)*(upper5) + (6059841480430017/100000000000000 : ℝ)*(major0) + (6059841480430017/100000000000000 : ℝ)*(major1) + (6059841480430017/100000000000000 : ℝ)*(major2) + (1626670613530761/20000000000000 : ℝ)*(sp0) + (4066687085425349/50000000000000 : ℝ)*(sp1) + (4066687168151399/50000000000000 : ℝ)*(sp2) + (1993149525254233/50000000000000 : ℝ)*(sp3) + (21767409317/100000000000000 : ℝ)*(sp4) + (1119049223/12500000000000 : ℝ)*(sp5) + (15945232011609/400000000000 : ℝ)*(f.failure) + (8133374835063123/100000000000000 : ℝ)*(f.sum) + (11318147556407/13030000000000000000000000000 : ℝ)*base65 + (12261579649872556143/1303000000000000000000000000000000 : ℝ)*base68 + (9277194567457556143/1303000000000000000000000000000000 : ℝ)*base70 + (2756066118853443857/1303000000000000000000000000000000 : ℝ)*base71 + (7763507266807/13030000000000000000000000000 : ℝ)*base73 + (9668573399919443857/1303000000000000000000000000000000 : ℝ)*base75 + (19134369536438556143/1303000000000000000000000000000000 : ℝ)*base78 + (22196634617436556143/1303000000000000000000000000000000 : ℝ)*base80 + (4486990625813/13030000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (540099/40000000000000000000 : ℝ)*base90 + (540099/40000000000000000000 : ℝ)*base92 + (540099/40000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1271_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152016389/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (353/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5757/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2303/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (353/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1271_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1271_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152016389/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14143/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11493/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2303/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (353/2500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1271_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1271_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1271_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152016389/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14143/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11493/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2303/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (353/2500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1271_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

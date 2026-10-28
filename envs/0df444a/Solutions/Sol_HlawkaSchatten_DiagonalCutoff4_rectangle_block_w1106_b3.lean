-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1106_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:03:19.114273+00:00
-- url     : https://prove2.me/submissions/27c89bb7-075c-4ea7-953f-587550cd6acf

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
theorem support_rectangle_w1106_s9_0 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1092113397/5000000000 : ℝ)*x 0 + (337101407/625000000 : ℝ)*x 1 + (2632595911/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092113397/5000000000 : ℝ)^8299 ≤ (2653770979537/20000000000000 : ℝ)^6251 := by
    have hnat : (1092113397 : ℕ)^8299*20000000000000^6251 ≤ 2653770979537^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092113397 5000000000 2653770979537 20000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337101407/625000000 : ℝ)^8299 ≤ (22029631118047/50000000000000 : ℝ)^6251 := by
    have hnat : (337101407 : ℕ)^8299*50000000000000^6251 ≤ 22029631118047^6251*625000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337101407 625000000 22029631118047 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632595911/5000000000 : ℝ)^8299 ≤ (42671882852653/100000000000000 : ℝ)^6251 := by
    have hnat : (2632595911 : ℕ)^8299*100000000000000^6251 ≤ 42671882852653^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632595911 5000000000 42671882852653 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1092113397/5000000000 : ℝ), (337101407/625000000 : ℝ), (2632595911/5000000000 : ℝ)] ![(2653770979537/20000000000000 : ℝ), (22029631118047/50000000000000 : ℝ), (42671882852653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1092113397/5000000000 : ℝ)|^8299 ≤ (2653770979537/20000000000000 : ℝ)^6251
        have hw : |(-1092113397/5000000000 : ℝ)|=(1092113397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337101407/625000000 : ℝ)|^8299 ≤ (22029631118047/50000000000000 : ℝ)^6251
        have hw : |(337101407/625000000 : ℝ)|=(337101407/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632595911/5000000000 : ℝ)|^8299 ≤ (42671882852653/100000000000000 : ℝ)^6251
        have hw : |(2632595911/5000000000 : ℝ)|=(2632595911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s9_1 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344864473/10000000000 : ℝ)*x 0 + (-224937753/1000000000 : ℝ)*x 1 + (2632595911/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344864473/10000000000 : ℝ)^8299 ≤ (8706252367629/20000000000000 : ℝ)^6251 := by
    have hnat : (5344864473 : ℕ)^8299*20000000000000^6251 ≤ 8706252367629^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344864473 10000000000 8706252367629 20000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (224937753/1000000000 : ℝ)^8299 ≤ (6898427646947/50000000000000 : ℝ)^6251 := by
    have hnat : (224937753 : ℕ)^8299*50000000000000^6251 ≤ 6898427646947^6251*1000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224937753 1000000000 6898427646947 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632595911/5000000000 : ℝ)^8299 ≤ (42671882852653/100000000000000 : ℝ)^6251 := by
    have hnat : (2632595911 : ℕ)^8299*100000000000000^6251 ≤ 42671882852653^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632595911 5000000000 42671882852653 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344864473/10000000000 : ℝ), (-224937753/1000000000 : ℝ), (2632595911/5000000000 : ℝ)] ![(8706252367629/20000000000000 : ℝ), (6898427646947/50000000000000 : ℝ), (42671882852653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344864473/10000000000 : ℝ)|^8299 ≤ (8706252367629/20000000000000 : ℝ)^6251
        have hw : |(5344864473/10000000000 : ℝ)|=(5344864473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-224937753/1000000000 : ℝ)|^8299 ≤ (6898427646947/50000000000000 : ℝ)^6251
        have hw : |(-224937753/1000000000 : ℝ)|=(224937753/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632595911/5000000000 : ℝ)|^8299 ≤ (42671882852653/100000000000000 : ℝ)^6251
        have hw : |(2632595911/5000000000 : ℝ)|=(2632595911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s9_2 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344864473/10000000000 : ℝ)*x 0 + (2632595911/5000000000 : ℝ)*x 1 + (-224937753/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344864473/10000000000 : ℝ)^8299 ≤ (8706252367629/20000000000000 : ℝ)^6251 := by
    have hnat : (5344864473 : ℕ)^8299*20000000000000^6251 ≤ 8706252367629^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344864473 10000000000 8706252367629 20000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632595911/5000000000 : ℝ)^8299 ≤ (42671882852653/100000000000000 : ℝ)^6251 := by
    have hnat : (2632595911 : ℕ)^8299*100000000000000^6251 ≤ 42671882852653^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632595911 5000000000 42671882852653 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (224937753/1000000000 : ℝ)^8299 ≤ (6898427646947/50000000000000 : ℝ)^6251 := by
    have hnat : (224937753 : ℕ)^8299*50000000000000^6251 ≤ 6898427646947^6251*1000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224937753 1000000000 6898427646947 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344864473/10000000000 : ℝ), (2632595911/5000000000 : ℝ), (-224937753/1000000000 : ℝ)] ![(8706252367629/20000000000000 : ℝ), (42671882852653/100000000000000 : ℝ), (6898427646947/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344864473/10000000000 : ℝ)|^8299 ≤ (8706252367629/20000000000000 : ℝ)^6251
        have hw : |(5344864473/10000000000 : ℝ)|=(5344864473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632595911/5000000000 : ℝ)|^8299 ≤ (42671882852653/100000000000000 : ℝ)^6251
        have hw : |(2632595911/5000000000 : ℝ)|=(2632595911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-224937753/1000000000 : ℝ)|^8299 ≤ (6898427646947/50000000000000 : ℝ)^6251
        have hw : |(-224937753/1000000000 : ℝ)|=(224937753/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s9_3 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4369772259/10000000000 : ℝ)*x 0 + (4244766771/10000000000 : ℝ)*x 1 + (2249236679/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4369772259/10000000000 : ℝ)^8299 ≤ (8329198263481/25000000000000 : ℝ)^6251 := by
    have hnat : (4369772259 : ℕ)^8299*25000000000000^6251 ≤ 8329198263481^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369772259 10000000000 8329198263481 25000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4244766771/10000000000 : ℝ)^8299 ≤ (32057413929831/100000000000000 : ℝ)^6251 := by
    have hnat : (4244766771 : ℕ)^8299*100000000000000^6251 ≤ 32057413929831^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244766771 10000000000 32057413929831 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2249236679/5000000000 : ℝ)^8299 ≤ (4328224125497/12500000000000 : ℝ)^6251 := by
    have hnat : (2249236679 : ℕ)^8299*12500000000000^6251 ≤ 4328224125497^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249236679 5000000000 4328224125497 12500000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4369772259/10000000000 : ℝ), (4244766771/10000000000 : ℝ), (2249236679/5000000000 : ℝ)] ![(8329198263481/25000000000000 : ℝ), (32057413929831/100000000000000 : ℝ), (4328224125497/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4369772259/10000000000 : ℝ)|^8299 ≤ (8329198263481/25000000000000 : ℝ)^6251
        have hw : |(4369772259/10000000000 : ℝ)|=(4369772259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4244766771/10000000000 : ℝ)|^8299 ≤ (32057413929831/100000000000000 : ℝ)^6251
        have hw : |(4244766771/10000000000 : ℝ)|=(4244766771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2249236679/5000000000 : ℝ)|^8299 ≤ (4328224125497/12500000000000 : ℝ)^6251
        have hw : |(2249236679/5000000000 : ℝ)|=(2249236679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s9_4 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2184231887/10000000000 : ℝ)*x 0 + (658189219/1250000000 : ℝ)*x 1 + (134832483/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184231887/10000000000 : ℝ)^8299 ≤ (2653779194693/20000000000000 : ℝ)^6251 := by
    have hnat : (2184231887 : ℕ)^8299*20000000000000^6251 ≤ 2653779194693^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184231887 10000000000 2653779194693 20000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658189219/1250000000 : ℝ)^8299 ≤ (1333604587099/3125000000000 : ℝ)^6251 := by
    have hnat : (658189219 : ℕ)^8299*3125000000000^6251 ≤ 1333604587099^6251*1250000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658189219 1250000000 1333604587099 3125000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (134832483/250000000 : ℝ)^8299 ≤ (11013939306491/25000000000000 : ℝ)^6251 := by
    have hnat : (134832483 : ℕ)^8299*25000000000000^6251 ≤ 11013939306491^6251*250000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134832483 250000000 11013939306491 25000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2184231887/10000000000 : ℝ), (658189219/1250000000 : ℝ), (134832483/250000000 : ℝ)] ![(2653779194693/20000000000000 : ℝ), (1333604587099/3125000000000 : ℝ), (11013939306491/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2184231887/10000000000 : ℝ)|^8299 ≤ (2653779194693/20000000000000 : ℝ)^6251
        have hw : |(-2184231887/10000000000 : ℝ)|=(2184231887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658189219/1250000000 : ℝ)|^8299 ≤ (1333604587099/3125000000000 : ℝ)^6251
        have hw : |(658189219/1250000000 : ℝ)|=(658189219/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(134832483/250000000 : ℝ)|^8299 ≤ (11013939306491/25000000000000 : ℝ)^6251
        have hw : |(134832483/250000000 : ℝ)|=(134832483/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s9_5 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4369782007/10000000000 : ℝ)*x 0 + (1124459337/2500000000 : ℝ)*x 1 + (13266891/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4369782007/10000000000 : ℝ)^8299 ≤ (33316891726469/100000000000000 : ℝ)^6251 := by
    have hnat : (4369782007 : ℕ)^8299*100000000000000^6251 ≤ 33316891726469^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369782007 10000000000 33316891726469 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1124459337/2500000000 : ℝ)^8299 ≤ (8654823432943/25000000000000 : ℝ)^6251 := by
    have hnat : (1124459337 : ℕ)^8299*25000000000000^6251 ≤ 8654823432943^6251*2500000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124459337 2500000000 8654823432943 25000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13266891/31250000 : ℝ)^8299 ≤ (32063814516733/100000000000000 : ℝ)^6251 := by
    have hnat : (13266891 : ℕ)^8299*100000000000000^6251 ≤ 32063814516733^6251*31250000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13266891 31250000 32063814516733 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4369782007/10000000000 : ℝ), (1124459337/2500000000 : ℝ), (13266891/31250000 : ℝ)] ![(33316891726469/100000000000000 : ℝ), (8654823432943/25000000000000 : ℝ), (32063814516733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4369782007/10000000000 : ℝ)|^8299 ≤ (33316891726469/100000000000000 : ℝ)^6251
        have hw : |(4369782007/10000000000 : ℝ)|=(4369782007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1124459337/2500000000 : ℝ)|^8299 ≤ (8654823432943/25000000000000 : ℝ)^6251
        have hw : |(1124459337/2500000000 : ℝ)|=(1124459337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(13266891/31250000 : ℝ)|^8299 ≤ (32063814516733/100000000000000 : ℝ)^6251
        have hw : |(13266891/31250000 : ℝ)|=(13266891/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1106_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148771791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14027/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5653/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11307/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14027/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14027/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5653/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14027/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5653/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14027/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5653/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14027/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5653/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14027/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5653/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14027/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5653/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5653/50000 : ℝ) ^ (4149/1024 : ℝ) ≤ (7298057362484401/50000000000000000000 : ℝ) := by
    have hpowers : (5653/50000 : ℝ)^4149 ≤ (7298057362484401/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5653 : ℕ)^4149*50000000000000000000^1024 ≤ 7298057362484401^1024*50000^4149 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5653 50000 7298057362484401 50000000000000000000 4149 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5653/50000 : ℝ)) (X := (7298057362484401/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14027/100000 : ℝ) ^ (4149/1024 : ℝ) ≤ (109284350006283/312500000000000000 : ℝ) := by
    have hpowers : (14027/100000 : ℝ)^4149 ≤ (109284350006283/312500000000000000 : ℝ)^1024 := by
      have hnat : (14027 : ℕ)^4149*312500000000000000^1024 ≤ 109284350006283^1024*100000^4149 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14027 100000 109284350006283 312500000000000000 4149 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14027/100000 : ℝ)) (X := (109284350006283/312500000000000000 : ℝ)) (by norm_num) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007298057362484401/25000000000000000000 : ℝ) ≤ (2000144080776997/2000000000000000 : ℝ) ^ (4149/1024 : ℝ) := by
    have hpowers : (25007298057362484401/25000000000000000000 : ℝ)^1024 ≤ (2000144080776997/2000000000000000 : ℝ)^4149 := by
      have hnat : (25007298057362484401 : ℕ)^1024*2000000000000000^4149 ≤ 2000144080776997^4149*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007298057362484401 25000000000000000000 2000144080776997 2000000000000000 1024 4149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000144080776997/2000000000000000 : ℝ)) (X := (25007298057362484401/25000000000000000000 : ℝ)) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024783553363489681/50000000000000000000 : ℝ) ≤ (10001223119917351/10000000000000000 : ℝ) ^ (4149/1024 : ℝ) := by
    have hpowers : (50024783553363489681/50000000000000000000 : ℝ)^1024 ≤ (10001223119917351/10000000000000000 : ℝ)^4149 := by
      have hnat : (50024783553363489681 : ℕ)^1024*10000000000000000^4149 ≤ 10001223119917351^4149*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024783553363489681 50000000000000000000 10001223119917351 10000000000000000 1024 4149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001223119917351/10000000000000000 : ℝ)) (X := (50024783553363489681/50000000000000000000 : ℝ)) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (156359284350006283/156250000000000000 : ℝ) ≤ (10001725835949717/10000000000000000 : ℝ) ^ (4149/1024 : ℝ) := by
    have hpowers : (156359284350006283/156250000000000000 : ℝ)^1024 ≤ (10001725835949717/10000000000000000 : ℝ)^4149 := by
      have hnat : (156359284350006283 : ℕ)^1024*10000000000000000^4149 ≤ 10001725835949717^4149*156250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        156359284350006283 156250000000000000 10001725835949717 10000000000000000 1024 4149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001725835949717/10000000000000000 : ℝ)) (X := (156359284350006283/156250000000000000 : ℝ)) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7298057362484401/50000000000000000000 : ℝ) ≤ ((27200592804047184193/27210000000000000000 : ℝ)+2*(251358016183/136050000000000 : ℝ)*(5653/50000 : ℝ))^(4149/1024 : ℝ) := by
    rw [show (27200592804047184193/27210000000000000000 : ℝ)+2*(251358016183/136050000000000 : ℝ)*(5653/50000 : ℝ)=(2000144080776997/2000000000000000 : ℝ) by norm_num, show 1+2*(7298057362484401/50000000000000000000 : ℝ)=(25007298057362484401/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(109284350006283/312500000000000000 : ℝ)+(7298057362484401/50000000000000000000 : ℝ) ≤ ((27200592804047184193/27210000000000000000 : ℝ)+(251358016183/136050000000000 : ℝ)*((14027/100000 : ℝ)+(5653/50000 : ℝ)))^(4149/1024 : ℝ) := by
    rw [show (27200592804047184193/27210000000000000000 : ℝ)+(251358016183/136050000000000 : ℝ)*((14027/100000 : ℝ)+(5653/50000 : ℝ))=(10001223119917351/10000000000000000 : ℝ) by norm_num, show 1+(109284350006283/312500000000000000 : ℝ)+(7298057362484401/50000000000000000000 : ℝ)=(50024783553363489681/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(109284350006283/312500000000000000 : ℝ) ≤ ((27200592804047184193/27210000000000000000 : ℝ)+2*(251358016183/136050000000000 : ℝ)*(14027/100000 : ℝ))^(4149/1024 : ℝ) := by
    rw [show (27200592804047184193/27210000000000000000 : ℝ)+2*(251358016183/136050000000000 : ℝ)*(14027/100000 : ℝ)=(10001725835949717/10000000000000000 : ℝ) by norm_num, show 1+2*(109284350006283/312500000000000000 : ℝ)=(156359284350006283/156250000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27200592804047184193/27210000000000000000 : ℝ)*(X 1 0+X 2 0)+(251358016183/136050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4149/1024 : ℝ)) (lo := (5653/50000 : ℝ)) (hi := (14027/100000 : ℝ)) (c := (27200592804047184193/27210000000000000000 : ℝ)) (alpha := (251358016183/136050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27200592804047184193/27210000000000000000 : ℝ)*(X 0 1+X 2 1)+(251358016183/136050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4149/1024 : ℝ)) (lo := (5653/50000 : ℝ)) (hi := (14027/100000 : ℝ)) (c := (27200592804047184193/27210000000000000000 : ℝ)) (alpha := (251358016183/136050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27200592804047184193/27210000000000000000 : ℝ)*(X 0 2+X 1 2)+(251358016183/136050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4149/1024 : ℝ)) (lo := (5653/50000 : ℝ)) (hi := (14027/100000 : ℝ)) (c := (27200592804047184193/27210000000000000000 : ℝ)) (alpha := (251358016183/136050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1092113397/5000000000 : ℝ)*X 0 0+(337101407/625000000 : ℝ)*X 0 1+(2632595911/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344864473/10000000000 : ℝ)*X 1 0+(-224937753/1000000000 : ℝ)*X 1 1+(2632595911/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344864473/10000000000 : ℝ)*X 2 0+(2632595911/5000000000 : ℝ)*X 2 1+(-224937753/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4369772259/10000000000 : ℝ)*X 0 0+(4244766771/10000000000 : ℝ)*X 0 1+(2249236679/5000000000 : ℝ)*X 0 2+(4369772259/10000000000 : ℝ)*X 1 0+(4244766771/10000000000 : ℝ)*X 1 1+(2249236679/5000000000 : ℝ)*X 1 2+(4369772259/10000000000 : ℝ)*X 2 0+(4244766771/10000000000 : ℝ)*X 2 1+(2249236679/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2184231887/10000000000 : ℝ)*X 0 0+(658189219/1250000000 : ℝ)*X 0 1+(134832483/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4369782007/10000000000 : ℝ)*X 0 0+(1124459337/2500000000 : ℝ)*X 0 1+(13266891/31250000 : ℝ)*X 0 2+(4369782007/10000000000 : ℝ)*X 1 0+(1124459337/2500000000 : ℝ)*X 1 1+(13266891/31250000 : ℝ)*X 1 2+(4369782007/10000000000 : ℝ)*X 2 0+(1124459337/2500000000 : ℝ)*X 2 1+(13266891/31250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (414696298741711522111873241/226750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22990049/6250000000000 : ℝ)*(base19) + (171235817/50000000000000 : ℝ)*(base23) + (6779733/50000000000000 : ℝ)*(lower2) + (46645539/100000000000000 : ℝ)*(upper3) + (2781957/10000000000000 : ℝ)*(upper5) + (5863946396561737/100000000000000 : ℝ)*(major0) + (5863946396561737/100000000000000 : ℝ)*(major1) + (5863946396561737/100000000000000 : ℝ)*(major2) + (1946577839255671/25000000000000 : ℝ)*(sp0) + (1946580235830777/25000000000000 : ℝ)*(sp1) + (7786320968692257/100000000000000 : ℝ)*(sp2) + (3941565960375037/100000000000000 : ℝ)*(sp3) + (9954141207/100000000000000 : ℝ)*(sp4) + (5460622199/100000000000000 : ℝ)*(sp5) + (985392855249309/25000000000000 : ℝ)*(f.failure) + (7786321311163891/100000000000000 : ℝ)*(f.sum) + (558458047787/13605000000000000000000000000 : ℝ)*base65 + (10718436628620592253/907000000000000000000000000000000 : ℝ)*base68 + (13941924728938407747/907000000000000000000000000000000 : ℝ)*base69 + (3169919522583592253/907000000000000000000000000000000 : ℝ)*base72 + (46046983253353/13605000000000000000000000000 : ℝ)*base74 + (24862123203277592253/907000000000000000000000000000000 : ℝ)*base76 + (6072631056222592253/907000000000000000000000000000000 : ℝ)*base78 + (8057009642094592253/907000000000000000000000000000000 : ℝ)*base80 + (2815006166281/6802500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (26442419/2500000000000000000000 : ℝ)*base89 + (26442419/2500000000000000000000 : ℝ)*base91 + (26442419/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1106_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148771791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14027/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5653/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11307/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14027/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1106_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1106_box_0 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2056133999/10000000000 : ℝ)*x 0 + (1075363191/2000000000 : ℝ)*x 1 + (5376815917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2056133999/10000000000 : ℝ)^8299 ≤ (6122913390231/50000000000000 : ℝ)^6251 := by
    have hnat : (2056133999 : ℕ)^8299*50000000000000^6251 ≤ 6122913390231^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2056133999 10000000000 6122913390231 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1075363191/2000000000 : ℝ)^8299 ≤ (43877086809027/100000000000000 : ℝ)^6251 := by
    have hnat : (1075363191 : ℕ)^8299*100000000000000^6251 ≤ 43877086809027^6251*2000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075363191 2000000000 43877086809027 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5376815917/10000000000 : ℝ)^8299 ≤ (8775417279467/20000000000000 : ℝ)^6251 := by
    have hnat : (5376815917 : ℕ)^8299*20000000000000^6251 ≤ 8775417279467^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376815917 10000000000 8775417279467 20000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2056133999/10000000000 : ℝ), (1075363191/2000000000 : ℝ), (5376815917/10000000000 : ℝ)] ![(6122913390231/50000000000000 : ℝ), (43877086809027/100000000000000 : ℝ), (8775417279467/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2056133999/10000000000 : ℝ)|^8299 ≤ (6122913390231/50000000000000 : ℝ)^6251
        have hw : |(-2056133999/10000000000 : ℝ)|=(2056133999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1075363191/2000000000 : ℝ)|^8299 ≤ (43877086809027/100000000000000 : ℝ)^6251
        have hw : |(1075363191/2000000000 : ℝ)|=(1075363191/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5376815917/10000000000 : ℝ)|^8299 ≤ (8775417279467/20000000000000 : ℝ)^6251
        have hw : |(5376815917/10000000000 : ℝ)|=(5376815917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_box_1 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5295635497/10000000000 : ℝ)*x 0 + (-67691767/312500000 : ℝ)*x 1 + (5376815961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295635497/10000000000 : ℝ)^8299 ≤ (2149988016331/5000000000000 : ℝ)^6251 := by
    have hnat : (5295635497 : ℕ)^8299*5000000000000^6251 ≤ 2149988016331^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295635497 10000000000 2149988016331 5000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67691767/312500000 : ℝ)^8299 ≤ (2624630558671/20000000000000 : ℝ)^6251 := by
    have hnat : (67691767 : ℕ)^8299*20000000000000^6251 ≤ 2624630558671^6251*312500000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67691767 312500000 2624630558671 20000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5376815961/10000000000 : ℝ)^8299 ≤ (43877086874031/100000000000000 : ℝ)^6251 := by
    have hnat : (5376815961 : ℕ)^8299*100000000000000^6251 ≤ 43877086874031^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376815961 10000000000 43877086874031 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295635497/10000000000 : ℝ), (-67691767/312500000 : ℝ), (5376815961/10000000000 : ℝ)] ![(2149988016331/5000000000000 : ℝ), (2624630558671/20000000000000 : ℝ), (43877086874031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295635497/10000000000 : ℝ)|^8299 ≤ (2149988016331/5000000000000 : ℝ)^6251
        have hw : |(5295635497/10000000000 : ℝ)|=(5295635497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-67691767/312500000 : ℝ)|^8299 ≤ (2624630558671/20000000000000 : ℝ)^6251
        have hw : |(-67691767/312500000 : ℝ)|=(67691767/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5376815961/10000000000 : ℝ)|^8299 ≤ (43877086874031/100000000000000 : ℝ)^6251
        have hw : |(5376815961/10000000000 : ℝ)|=(5376815961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_box_2 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1323908841/2500000000 : ℝ)*x 0 + (268840793/500000000 : ℝ)*x 1 + (-1083068429/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323908841/2500000000 : ℝ)^8299 ≤ (21499879446431/50000000000000 : ℝ)^6251 := by
    have hnat : (1323908841 : ℕ)^8299*50000000000000^6251 ≤ 21499879446431^6251*2500000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323908841 2500000000 21499879446431 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (268840793/500000000 : ℝ)^8299 ≤ (43877085779797/100000000000000 : ℝ)^6251 := by
    have hnat : (268840793 : ℕ)^8299*100000000000000^6251 ≤ 43877085779797^6251*500000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268840793 500000000 43877085779797 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083068429/5000000000 : ℝ)^8299 ≤ (13123155318919/100000000000000 : ℝ)^6251 := by
    have hnat : (1083068429 : ℕ)^8299*100000000000000^6251 ≤ 13123155318919^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083068429 5000000000 13123155318919 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323908841/2500000000 : ℝ), (268840793/500000000 : ℝ), (-1083068429/5000000000 : ℝ)] ![(21499879446431/50000000000000 : ℝ), (43877085779797/100000000000000 : ℝ), (13123155318919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323908841/2500000000 : ℝ)|^8299 ≤ (21499879446431/50000000000000 : ℝ)^6251
        have hw : |(1323908841/2500000000 : ℝ)|=(1323908841/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(268840793/500000000 : ℝ)|^8299 ≤ (43877085779797/100000000000000 : ℝ)^6251
        have hw : |(268840793/500000000 : ℝ)|=(268840793/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1083068429/5000000000 : ℝ)|^8299 ≤ (13123155318919/100000000000000 : ℝ)^6251
        have hw : |(-1083068429/5000000000 : ℝ)|=(1083068429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_box_3 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4477703137/10000000000 : ℝ)*x 0 + (172717577/400000000 : ℝ)*x 1 + (1079485013/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4477703137/10000000000 : ℝ)^8299 ≤ (34413701626631/100000000000000 : ℝ)^6251 := by
    have hnat : (4477703137 : ℕ)^8299*100000000000000^6251 ≤ 34413701626631^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4477703137 10000000000 34413701626631 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (172717577/400000000 : ℝ)^8299 ≤ (4099143252473/12500000000000 : ℝ)^6251 := by
    have hnat : (172717577 : ℕ)^8299*12500000000000^6251 ≤ 4099143252473^6251*400000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172717577 400000000 4099143252473 12500000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1079485013/2500000000 : ℝ)^8299 ≤ (8198288085431/25000000000000 : ℝ)^6251 := by
    have hnat : (1079485013 : ℕ)^8299*25000000000000^6251 ≤ 8198288085431^6251*2500000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079485013 2500000000 8198288085431 25000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4477703137/10000000000 : ℝ), (172717577/400000000 : ℝ), (1079485013/2500000000 : ℝ)] ![(34413701626631/100000000000000 : ℝ), (4099143252473/12500000000000 : ℝ), (8198288085431/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4477703137/10000000000 : ℝ)|^8299 ≤ (34413701626631/100000000000000 : ℝ)^6251
        have hw : |(4477703137/10000000000 : ℝ)|=(4477703137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(172717577/400000000 : ℝ)|^8299 ≤ (4099143252473/12500000000000 : ℝ)^6251
        have hw : |(172717577/400000000 : ℝ)|=(172717577/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1079485013/2500000000 : ℝ)|^8299 ≤ (8198288085431/25000000000000 : ℝ)^6251
        have hw : |(1079485013/2500000000 : ℝ)|=(1079485013/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_box_4 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2313697831/10000000000 : ℝ)*x 0 + (2640333479/5000000000 : ℝ)*x 1 + (5280666083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2313697831/10000000000 : ℝ)^8299 ≤ (14323064985343/100000000000000 : ℝ)^6251 := by
    have hnat : (2313697831 : ℕ)^8299*100000000000000^6251 ≤ 14323064985343^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2313697831 10000000000 14323064985343 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640333479/5000000000 : ℝ)^8299 ≤ (856769444261/2000000000000 : ℝ)^6251 := by
    have hnat : (2640333479 : ℕ)^8299*2000000000000^6251 ≤ 856769444261^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640333479 5000000000 856769444261 2000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5280666083/10000000000 : ℝ)^8299 ≤ (1713538511567/4000000000000 : ℝ)^6251 := by
    have hnat : (5280666083 : ℕ)^8299*4000000000000^6251 ≤ 1713538511567^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280666083 10000000000 1713538511567 4000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2313697831/10000000000 : ℝ), (2640333479/5000000000 : ℝ), (5280666083/10000000000 : ℝ)] ![(14323064985343/100000000000000 : ℝ), (856769444261/2000000000000 : ℝ), (1713538511567/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2313697831/10000000000 : ℝ)|^8299 ≤ (14323064985343/100000000000000 : ℝ)^6251
        have hw : |(-2313697831/10000000000 : ℝ)|=(2313697831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640333479/5000000000 : ℝ)|^8299 ≤ (856769444261/2000000000000 : ℝ)^6251
        have hw : |(2640333479/5000000000 : ℝ)|=(2640333479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5280666083/10000000000 : ℝ)|^8299 ≤ (1713538511567/4000000000000 : ℝ)^6251
        have hw : |(5280666083/10000000000 : ℝ)|=(5280666083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_box_5 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2681809687/5000000000 : ℝ)*x 0 + (-440770053/2000000000 : ℝ)*x 1 + (2640333563/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681809687/5000000000 : ℝ)^8299 ≤ (21867086274423/50000000000000 : ℝ)^6251 := by
    have hnat : (2681809687 : ℕ)^8299*50000000000000^6251 ≤ 21867086274423^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681809687 5000000000 21867086274423 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (440770053/2000000000 : ℝ)^8299 ≤ (671367671093/5000000000000 : ℝ)^6251 := by
    have hnat : (440770053 : ℕ)^8299*5000000000000^6251 ≤ 671367671093^6251*2000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440770053 2000000000 671367671093 5000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2640333563/5000000000 : ℝ)^8299 ≤ (21419237011217/50000000000000 : ℝ)^6251 := by
    have hnat : (2640333563 : ℕ)^8299*50000000000000^6251 ≤ 21419237011217^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640333563 5000000000 21419237011217 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681809687/5000000000 : ℝ), (-440770053/2000000000 : ℝ), (2640333563/5000000000 : ℝ)] ![(21867086274423/50000000000000 : ℝ), (671367671093/5000000000000 : ℝ), (21419237011217/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681809687/5000000000 : ℝ)|^8299 ≤ (21867086274423/50000000000000 : ℝ)^6251
        have hw : |(2681809687/5000000000 : ℝ)|=(2681809687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-440770053/2000000000 : ℝ)|^8299 ≤ (671367671093/5000000000000 : ℝ)^6251
        have hw : |(-440770053/2000000000 : ℝ)|=(440770053/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2640333563/5000000000 : ℝ)|^8299 ≤ (21419237011217/50000000000000 : ℝ)^6251
        have hw : |(2640333563/5000000000 : ℝ)|=(2640333563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_box_6 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2681810253/5000000000 : ℝ)*x 0 + (2640333043/5000000000 : ℝ)*x 1 + (-1101925067/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681810253/5000000000 : ℝ)^8299 ≤ (21867092401533/50000000000000 : ℝ)^6251 := by
    have hnat : (2681810253 : ℕ)^8299*50000000000000^6251 ≤ 21867092401533^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681810253 5000000000 21867092401533 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640333043/5000000000 : ℝ)^8299 ≤ (21419231410743/50000000000000 : ℝ)^6251 := by
    have hnat : (2640333043 : ℕ)^8299*50000000000000^6251 ≤ 21419231410743^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640333043 5000000000 21419231410743 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1101925067/5000000000 : ℝ)^8299 ≤ (6713676181113/50000000000000 : ℝ)^6251 := by
    have hnat : (1101925067 : ℕ)^8299*50000000000000^6251 ≤ 6713676181113^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101925067 5000000000 6713676181113 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681810253/5000000000 : ℝ), (2640333043/5000000000 : ℝ), (-1101925067/5000000000 : ℝ)] ![(21867092401533/50000000000000 : ℝ), (21419231410743/50000000000000 : ℝ), (6713676181113/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681810253/5000000000 : ℝ)|^8299 ≤ (21867092401533/50000000000000 : ℝ)^6251
        have hw : |(2681810253/5000000000 : ℝ)|=(2681810253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640333043/5000000000 : ℝ)|^8299 ≤ (21419231410743/50000000000000 : ℝ)^6251
        have hw : |(2640333043/5000000000 : ℝ)|=(2640333043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1101925067/5000000000 : ℝ)|^8299 ≤ (6713676181113/50000000000000 : ℝ)^6251
        have hw : |(-1101925067/5000000000 : ℝ)|=(1101925067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_box_7 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2130747409/5000000000 : ℝ)*x 0 + (2213011577/5000000000 : ℝ)*x 1 + (4426022391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2130747409/5000000000 : ℝ)^8299 ≤ (32225246477347/100000000000000 : ℝ)^6251 := by
    have hnat : (2130747409 : ℕ)^8299*100000000000000^6251 ≤ 32225246477347^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130747409 5000000000 32225246477347 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2213011577/5000000000 : ℝ)^8299 ≤ (33887380633411/100000000000000 : ℝ)^6251 := by
    have hnat : (2213011577 : ℕ)^8299*100000000000000^6251 ≤ 33887380633411^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2213011577 5000000000 33887380633411 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4426022391/10000000000 : ℝ)^8299 ≤ (33887372877637/100000000000000 : ℝ)^6251 := by
    have hnat : (4426022391 : ℕ)^8299*100000000000000^6251 ≤ 33887372877637^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4426022391 10000000000 33887372877637 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2130747409/5000000000 : ℝ), (2213011577/5000000000 : ℝ), (4426022391/10000000000 : ℝ)] ![(32225246477347/100000000000000 : ℝ), (33887380633411/100000000000000 : ℝ), (33887372877637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2130747409/5000000000 : ℝ)|^8299 ≤ (32225246477347/100000000000000 : ℝ)^6251
        have hw : |(2130747409/5000000000 : ℝ)|=(2130747409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2213011577/5000000000 : ℝ)|^8299 ≤ (33887380633411/100000000000000 : ℝ)^6251
        have hw : |(2213011577/5000000000 : ℝ)|=(2213011577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4426022391/10000000000 : ℝ)|^8299 ≤ (33887372877637/100000000000000 : ℝ)^6251
        have hw : |(4426022391/10000000000 : ℝ)|=(4426022391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_box_8 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2259879853/10000000000 : ℝ)*x 0 + (5215345179/10000000000 : ℝ)*x 1 + (336651323/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2259879853/10000000000 : ℝ)^8299 ≤ (2776488588219/20000000000000 : ℝ)^6251 := by
    have hnat : (2259879853 : ℕ)^8299*20000000000000^6251 ≤ 2776488588219^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259879853 10000000000 2776488588219 20000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215345179/10000000000 : ℝ)^8299 ≤ (84272753807/200000000000 : ℝ)^6251 := by
    have hnat : (5215345179 : ℕ)^8299*200000000000^6251 ≤ 84272753807^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215345179 10000000000 84272753807 200000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (336651323/625000000 : ℝ)^8299 ≤ (5497647517371/12500000000000 : ℝ)^6251 := by
    have hnat : (336651323 : ℕ)^8299*12500000000000^6251 ≤ 5497647517371^6251*625000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336651323 625000000 5497647517371 12500000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2259879853/10000000000 : ℝ), (5215345179/10000000000 : ℝ), (336651323/625000000 : ℝ)] ![(2776488588219/20000000000000 : ℝ), (84272753807/200000000000 : ℝ), (5497647517371/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2259879853/10000000000 : ℝ)|^8299 ≤ (2776488588219/20000000000000 : ℝ)^6251
        have hw : |(-2259879853/10000000000 : ℝ)|=(2259879853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215345179/10000000000 : ℝ)|^8299 ≤ (84272753807/200000000000 : ℝ)^6251
        have hw : |(5215345179/10000000000 : ℝ)|=(5215345179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(336651323/625000000 : ℝ)|^8299 ≤ (5497647517371/12500000000000 : ℝ)^6251
        have hw : |(336651323/625000000 : ℝ)|=(336651323/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_box_9 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1322210193/2500000000 : ℝ)*x 0 + (-270287281/1250000000 : ℝ)*x 1 + (2693210703/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322210193/2500000000 : ℝ)^8299 ≤ (42926527671227/100000000000000 : ℝ)^6251 := by
    have hnat : (1322210193 : ℕ)^8299*100000000000000^6251 ≤ 42926527671227^6251*2500000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322210193 2500000000 42926527671227 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270287281/1250000000 : ℝ)^8299 ≤ (13092289593303/100000000000000 : ℝ)^6251 := by
    have hnat : (270287281 : ℕ)^8299*100000000000000^6251 ≤ 13092289593303^6251*1250000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270287281 1250000000 13092289593303 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693210703/5000000000 : ℝ)^8299 ≤ (43981182718969/100000000000000 : ℝ)^6251 := by
    have hnat : (2693210703 : ℕ)^8299*100000000000000^6251 ≤ 43981182718969^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693210703 5000000000 43981182718969 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322210193/2500000000 : ℝ), (-270287281/1250000000 : ℝ), (2693210703/5000000000 : ℝ)] ![(42926527671227/100000000000000 : ℝ), (13092289593303/100000000000000 : ℝ), (43981182718969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322210193/2500000000 : ℝ)|^8299 ≤ (42926527671227/100000000000000 : ℝ)^6251
        have hw : |(1322210193/2500000000 : ℝ)|=(1322210193/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-270287281/1250000000 : ℝ)|^8299 ≤ (13092289593303/100000000000000 : ℝ)^6251
        have hw : |(-270287281/1250000000 : ℝ)|=(270287281/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693210703/5000000000 : ℝ)|^8299 ≤ (43981182718969/100000000000000 : ℝ)^6251
        have hw : |(2693210703/5000000000 : ℝ)|=(2693210703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_box_10 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5288840469/10000000000 : ℝ)*x 0 + (1077284089/2000000000 : ℝ)*x 1 + (-2162299951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288840469/10000000000 : ℝ)^8299 ≤ (2146326220311/5000000000000 : ℝ)^6251 := by
    have hnat : (5288840469 : ℕ)^8299*5000000000000^6251 ≤ 2146326220311^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288840469 10000000000 2146326220311 5000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1077284089/2000000000 : ℝ)^8299 ≤ (10995293075351/25000000000000 : ℝ)^6251 := by
    have hnat : (1077284089 : ℕ)^8299*25000000000000^6251 ≤ 10995293075351^6251*2000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077284089 2000000000 10995293075351 25000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2162299951/10000000000 : ℝ)^8299 ≤ (1309230328291/10000000000000 : ℝ)^6251 := by
    have hnat : (2162299951 : ℕ)^8299*10000000000000^6251 ≤ 1309230328291^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162299951 10000000000 1309230328291 10000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288840469/10000000000 : ℝ), (1077284089/2000000000 : ℝ), (-2162299951/10000000000 : ℝ)] ![(2146326220311/5000000000000 : ℝ), (10995293075351/25000000000000 : ℝ), (1309230328291/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288840469/10000000000 : ℝ)|^8299 ≤ (2146326220311/5000000000000 : ℝ)^6251
        have hw : |(5288840469/10000000000 : ℝ)|=(5288840469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1077284089/2000000000 : ℝ)|^8299 ≤ (10995293075351/25000000000000 : ℝ)^6251
        have hw : |(1077284089/2000000000 : ℝ)|=(1077284089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2162299951/10000000000 : ℝ)|^8299 ≤ (1309230328291/10000000000000 : ℝ)^6251
        have hw : |(-2162299951/10000000000 : ℝ)|=(2162299951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_box_11 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (899805673/2000000000 : ℝ)*x 0 + (67299011/156250000 : ℝ)*x 1 + (1076784127/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (899805673/2000000000 : ℝ)^8299 ≤ (34631464767029/100000000000000 : ℝ)^6251 := by
    have hnat : (899805673 : ℕ)^8299*100000000000000^6251 ≤ 34631464767029^6251*2000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899805673 2000000000 34631464767029 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67299011/156250000 : ℝ)^8299 ≤ (6536853719103/20000000000000 : ℝ)^6251 := by
    have hnat : (67299011 : ℕ)^8299*20000000000000^6251 ≤ 6536853719103^6251*156250000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67299011 156250000 6536853719103 20000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1076784127/2500000000 : ℝ)^8299 ≤ (326842666209/1000000000000 : ℝ)^6251 := by
    have hnat : (1076784127 : ℕ)^8299*1000000000000^6251 ≤ 326842666209^6251*2500000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076784127 2500000000 326842666209 1000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(899805673/2000000000 : ℝ), (67299011/156250000 : ℝ), (1076784127/2500000000 : ℝ)] ![(34631464767029/100000000000000 : ℝ), (6536853719103/20000000000000 : ℝ), (326842666209/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(899805673/2000000000 : ℝ)|^8299 ≤ (34631464767029/100000000000000 : ℝ)^6251
        have hw : |(899805673/2000000000 : ℝ)|=(899805673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(67299011/156250000 : ℝ)|^8299 ≤ (6536853719103/20000000000000 : ℝ)^6251
        have hw : |(67299011/156250000 : ℝ)|=(67299011/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1076784127/2500000000 : ℝ)|^8299 ≤ (326842666209/1000000000000 : ℝ)^6251
        have hw : |(1076784127/2500000000 : ℝ)|=(1076784127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_box_12 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-105514701/500000000 : ℝ)*x 0 + (2720415977/5000000000 : ℝ)*x 1 + (82385093/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105514701/500000000 : ℝ)^8299 ≤ (6337954172947/50000000000000 : ℝ)^6251 := by
    have hnat : (105514701 : ℕ)^8299*50000000000000^6251 ≤ 6337954172947^6251*500000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105514701 500000000 6337954172947 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2720415977/5000000000 : ℝ)^8299 ≤ (44571985296019/100000000000000 : ℝ)^6251 := by
    have hnat : (2720415977 : ℕ)^8299*100000000000000^6251 ≤ 44571985296019^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720415977 5000000000 44571985296019 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82385093/156250000 : ℝ)^8299 ≤ (2137605316779/5000000000000 : ℝ)^6251 := by
    have hnat : (82385093 : ℕ)^8299*5000000000000^6251 ≤ 2137605316779^6251*156250000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82385093 156250000 2137605316779 5000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-105514701/500000000 : ℝ), (2720415977/5000000000 : ℝ), (82385093/156250000 : ℝ)] ![(6337954172947/50000000000000 : ℝ), (44571985296019/100000000000000 : ℝ), (2137605316779/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-105514701/500000000 : ℝ)|^8299 ≤ (6337954172947/50000000000000 : ℝ)^6251
        have hw : |(-105514701/500000000 : ℝ)|=(105514701/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2720415977/5000000000 : ℝ)|^8299 ≤ (44571985296019/100000000000000 : ℝ)^6251
        have hw : |(2720415977/5000000000 : ℝ)|=(2720415977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(82385093/156250000 : ℝ)|^8299 ≤ (2137605316779/5000000000000 : ℝ)^6251
        have hw : |(82385093/156250000 : ℝ)|=(82385093/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_box_13 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1073857893/2000000000 : ℝ)*x 0 + (-2206938753/10000000000 : ℝ)*x 1 + (5272644911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073857893/2000000000 : ℝ)^8299 ≤ (8759112702261/20000000000000 : ℝ)^6251 := by
    have hnat : (1073857893 : ℕ)^8299*20000000000000^6251 ≤ 8759112702261^6251*2000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073857893 2000000000 8759112702261 20000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2206938753/10000000000 : ℝ)^8299 ≤ (6726170672977/50000000000000 : ℝ)^6251 := by
    have hnat : (2206938753 : ℕ)^8299*50000000000000^6251 ≤ 6726170672977^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2206938753 10000000000 6726170672977 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272644911/10000000000 : ℝ)^8299 ≤ (10688023782361/25000000000000 : ℝ)^6251 := by
    have hnat : (5272644911 : ℕ)^8299*25000000000000^6251 ≤ 10688023782361^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272644911 10000000000 10688023782361 25000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073857893/2000000000 : ℝ), (-2206938753/10000000000 : ℝ), (5272644911/10000000000 : ℝ)] ![(8759112702261/20000000000000 : ℝ), (6726170672977/50000000000000 : ℝ), (10688023782361/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073857893/2000000000 : ℝ)|^8299 ≤ (8759112702261/20000000000000 : ℝ)^6251
        have hw : |(1073857893/2000000000 : ℝ)|=(1073857893/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2206938753/10000000000 : ℝ)|^8299 ≤ (6726170672977/50000000000000 : ℝ)^6251
        have hw : |(-2206938753/10000000000 : ℝ)|=(2206938753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5272644911/10000000000 : ℝ)|^8299 ≤ (10688023782361/25000000000000 : ℝ)^6251
        have hw : |(5272644911/10000000000 : ℝ)|=(5272644911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_box_14 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5369289599/10000000000 : ℝ)*x 0 + (5272644517/10000000000 : ℝ)*x 1 + (-1103469549/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369289599/10000000000 : ℝ)^8299 ≤ (8759112992479/20000000000000 : ℝ)^6251 := by
    have hnat : (5369289599 : ℕ)^8299*20000000000000^6251 ≤ 8759112992479^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369289599 10000000000 8759112992479 20000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5272644517/10000000000 : ℝ)^8299 ≤ (42752090888121/100000000000000 : ℝ)^6251 := by
    have hnat : (5272644517 : ℕ)^8299*100000000000000^6251 ≤ 42752090888121^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272644517 10000000000 42752090888121 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1103469549/5000000000 : ℝ)^8299 ≤ (6726172068937/50000000000000 : ℝ)^6251 := by
    have hnat : (1103469549 : ℕ)^8299*50000000000000^6251 ≤ 6726172068937^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103469549 5000000000 6726172068937 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369289599/10000000000 : ℝ), (5272644517/10000000000 : ℝ), (-1103469549/5000000000 : ℝ)] ![(8759112992479/20000000000000 : ℝ), (42752090888121/100000000000000 : ℝ), (6726172068937/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369289599/10000000000 : ℝ)|^8299 ≤ (8759112992479/20000000000000 : ℝ)^6251
        have hw : |(5369289599/10000000000 : ℝ)|=(5369289599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5272644517/10000000000 : ℝ)|^8299 ≤ (42752090888121/100000000000000 : ℝ)^6251
        have hw : |(5272644517/10000000000 : ℝ)|=(5272644517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1103469549/5000000000 : ℝ)|^8299 ≤ (6726172068937/50000000000000 : ℝ)^6251
        have hw : |(-1103469549/5000000000 : ℝ)|=(1103469549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_box_15 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1060806821/2500000000 : ℝ)*x 0 + (2217517033/5000000000 : ℝ)*x 1 + (887007001/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060806821/2500000000 : ℝ)^8299 ≤ (16020989562567/50000000000000 : ℝ)^6251 := by
    have hnat : (1060806821 : ℕ)^8299*50000000000000^6251 ≤ 16020989562567^6251*2500000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060806821 2500000000 16020989562567 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2217517033/5000000000 : ℝ)^8299 ≤ (16989502826833/50000000000000 : ℝ)^6251 := by
    have hnat : (2217517033 : ℕ)^8299*50000000000000^6251 ≤ 16989502826833^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2217517033 5000000000 16989502826833 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (887007001/2000000000 : ℝ)^8299 ≤ (16989507602407/50000000000000 : ℝ)^6251 := by
    have hnat : (887007001 : ℕ)^8299*50000000000000^6251 ≤ 16989507602407^6251*2000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      887007001 2000000000 16989507602407 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060806821/2500000000 : ℝ), (2217517033/5000000000 : ℝ), (887007001/2000000000 : ℝ)] ![(16020989562567/50000000000000 : ℝ), (16989502826833/50000000000000 : ℝ), (16989507602407/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060806821/2500000000 : ℝ)|^8299 ≤ (16020989562567/50000000000000 : ℝ)^6251
        have hw : |(1060806821/2500000000 : ℝ)|=(1060806821/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2217517033/5000000000 : ℝ)|^8299 ≤ (16989502826833/50000000000000 : ℝ)^6251
        have hw : |(2217517033/5000000000 : ℝ)|=(2217517033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(887007001/2000000000 : ℝ)|^8299 ≤ (16989507602407/50000000000000 : ℝ)^6251
        have hw : |(887007001/2000000000 : ℝ)|=(887007001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1106_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148771791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14027/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11307/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62227/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59271/100000 : ℝ) ∧ (79697/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (83043/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14027/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11307/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14027/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11307/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14027/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11307/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14027/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11307/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14027/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11307/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14027/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11307/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11307/100000 : ℝ) ^ (4149/1024 : ℝ) ≤ (730067313747053/5000000000000000000 : ℝ) := by
    have hpowers : (11307/100000 : ℝ)^4149 ≤ (730067313747053/5000000000000000000 : ℝ)^1024 := by
      have hnat : (11307 : ℕ)^4149*5000000000000000000^1024 ≤ 730067313747053^1024*100000^4149 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11307 100000 730067313747053 5000000000000000000 4149 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11307/100000 : ℝ)) (X := (730067313747053/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14027/100000 : ℝ) ^ (4149/1024 : ℝ) ≤ (109284350006283/312500000000000000 : ℝ) := by
    have hpowers : (14027/100000 : ℝ)^4149 ≤ (109284350006283/312500000000000000 : ℝ)^1024 := by
      have hnat : (14027 : ℕ)^4149*312500000000000000^1024 ≤ 109284350006283^1024*100000^4149 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14027 100000 109284350006283 312500000000000000 4149 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14027/100000 : ℝ)) (X := (109284350006283/312500000000000000 : ℝ)) (by norm_num) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500730067313747053/2500000000000000000 : ℝ) ≤ (400028826482571/400000000000000 : ℝ) ^ (4149/1024 : ℝ) := by
    have hpowers : (2500730067313747053/2500000000000000000 : ℝ)^1024 ≤ (400028826482571/400000000000000 : ℝ)^4149 := by
      have hnat : (2500730067313747053 : ℕ)^1024*400000000000000^4149 ≤ 400028826482571^4149*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500730067313747053 2500000000000000000 400028826482571 400000000000000 1024 4149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400028826482571/400000000000000 : ℝ)) (X := (2500730067313747053/2500000000000000000 : ℝ)) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5002478616913847581/5000000000000000000 : ℝ) ≤ (10001223248987197/10000000000000000 : ℝ) ^ (4149/1024 : ℝ) := by
    have hpowers : (5002478616913847581/5000000000000000000 : ℝ)^1024 ≤ (10001223248987197/10000000000000000 : ℝ)^4149 := by
      have hnat : (5002478616913847581 : ℕ)^1024*10000000000000000^4149 ≤ 10001223248987197^4149*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002478616913847581 5000000000000000000 10001223248987197 10000000000000000 1024 4149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001223248987197/10000000000000000 : ℝ)) (X := (5002478616913847581/5000000000000000000 : ℝ)) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (156359284350006283/156250000000000000 : ℝ) ≤ (10001725835910119/10000000000000000 : ℝ) ^ (4149/1024 : ℝ) := by
    have hpowers : (156359284350006283/156250000000000000 : ℝ)^1024 ≤ (10001725835910119/10000000000000000 : ℝ)^4149 := by
      have hnat : (156359284350006283 : ℕ)^1024*10000000000000000^4149 ≤ 10001725835910119^4149*156250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        156359284350006283 156250000000000000 10001725835910119 10000000000000000 1024 4149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001725835910119/10000000000000000 : ℝ)) (X := (156359284350006283/156250000000000000 : ℝ)) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(730067313747053/5000000000000000000 : ℝ) ≤ ((6797648675034967473/6800000000000000000 : ℝ)+2*(251293461461/136000000000000 : ℝ)*(11307/100000 : ℝ))^(4149/1024 : ℝ) := by
    rw [show (6797648675034967473/6800000000000000000 : ℝ)+2*(251293461461/136000000000000 : ℝ)*(11307/100000 : ℝ)=(400028826482571/400000000000000 : ℝ) by norm_num, show 1+2*(730067313747053/5000000000000000000 : ℝ)=(2500730067313747053/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(109284350006283/312500000000000000 : ℝ)+(730067313747053/5000000000000000000 : ℝ) ≤ ((6797648675034967473/6800000000000000000 : ℝ)+(251293461461/136000000000000 : ℝ)*((14027/100000 : ℝ)+(11307/100000 : ℝ)))^(4149/1024 : ℝ) := by
    rw [show (6797648675034967473/6800000000000000000 : ℝ)+(251293461461/136000000000000 : ℝ)*((14027/100000 : ℝ)+(11307/100000 : ℝ))=(10001223248987197/10000000000000000 : ℝ) by norm_num, show 1+(109284350006283/312500000000000000 : ℝ)+(730067313747053/5000000000000000000 : ℝ)=(5002478616913847581/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(109284350006283/312500000000000000 : ℝ) ≤ ((6797648675034967473/6800000000000000000 : ℝ)+2*(251293461461/136000000000000 : ℝ)*(14027/100000 : ℝ))^(4149/1024 : ℝ) := by
    rw [show (6797648675034967473/6800000000000000000 : ℝ)+2*(251293461461/136000000000000 : ℝ)*(14027/100000 : ℝ)=(10001725835910119/10000000000000000 : ℝ) by norm_num, show 1+2*(109284350006283/312500000000000000 : ℝ)=(156359284350006283/156250000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6797648675034967473/6800000000000000000 : ℝ)*(X 1 0+X 2 0)+(251293461461/136000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4149/1024 : ℝ)) (lo := (11307/100000 : ℝ)) (hi := (14027/100000 : ℝ)) (c := (6797648675034967473/6800000000000000000 : ℝ)) (alpha := (251293461461/136000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6797648675034967473/6800000000000000000 : ℝ)*(X 0 1+X 2 1)+(251293461461/136000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4149/1024 : ℝ)) (lo := (11307/100000 : ℝ)) (hi := (14027/100000 : ℝ)) (c := (6797648675034967473/6800000000000000000 : ℝ)) (alpha := (251293461461/136000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6797648675034967473/6800000000000000000 : ℝ)*(X 0 2+X 1 2)+(251293461461/136000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4149/1024 : ℝ)) (lo := (11307/100000 : ℝ)) (hi := (14027/100000 : ℝ)) (c := (6797648675034967473/6800000000000000000 : ℝ)) (alpha := (251293461461/136000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2056133999/10000000000 : ℝ)*X 0 0+(1075363191/2000000000 : ℝ)*X 0 1+(5376815917/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5295635497/10000000000 : ℝ)*X 1 0+(-67691767/312500000 : ℝ)*X 1 1+(5376815961/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1323908841/2500000000 : ℝ)*X 2 0+(268840793/500000000 : ℝ)*X 2 1+(-1083068429/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4477703137/10000000000 : ℝ)*X 0 0+(172717577/400000000 : ℝ)*X 0 1+(1079485013/2500000000 : ℝ)*X 0 2+(4477703137/10000000000 : ℝ)*X 1 0+(172717577/400000000 : ℝ)*X 1 1+(1079485013/2500000000 : ℝ)*X 1 2+(4477703137/10000000000 : ℝ)*X 2 0+(172717577/400000000 : ℝ)*X 2 1+(1079485013/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2313697831/10000000000 : ℝ)*X 0 0+(2640333479/5000000000 : ℝ)*X 0 1+(5280666083/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2681809687/5000000000 : ℝ)*X 1 0+(-440770053/2000000000 : ℝ)*X 1 1+(2640333563/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2681810253/5000000000 : ℝ)*X 2 0+(2640333043/5000000000 : ℝ)*X 2 1+(-1101925067/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2130747409/5000000000 : ℝ)*X 0 0+(2213011577/5000000000 : ℝ)*X 0 1+(4426022391/10000000000 : ℝ)*X 0 2+(2130747409/5000000000 : ℝ)*X 1 0+(2213011577/5000000000 : ℝ)*X 1 1+(4426022391/10000000000 : ℝ)*X 1 2+(2130747409/5000000000 : ℝ)*X 2 0+(2213011577/5000000000 : ℝ)*X 2 1+(4426022391/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2259879853/10000000000 : ℝ)*X 0 0+(5215345179/10000000000 : ℝ)*X 0 1+(336651323/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1322210193/2500000000 : ℝ)*X 1 0+(-270287281/1250000000 : ℝ)*X 1 1+(2693210703/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5288840469/10000000000 : ℝ)*X 2 0+(1077284089/2000000000 : ℝ)*X 2 1+(-2162299951/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((899805673/2000000000 : ℝ)*X 0 0+(67299011/156250000 : ℝ)*X 0 1+(1076784127/2500000000 : ℝ)*X 0 2+(899805673/2000000000 : ℝ)*X 1 0+(67299011/156250000 : ℝ)*X 1 1+(1076784127/2500000000 : ℝ)*X 1 2+(899805673/2000000000 : ℝ)*X 2 0+(67299011/156250000 : ℝ)*X 2 1+(1076784127/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-105514701/500000000 : ℝ)*X 0 0+(2720415977/5000000000 : ℝ)*X 0 1+(82385093/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1073857893/2000000000 : ℝ)*X 1 0+(-2206938753/10000000000 : ℝ)*X 1 1+(5272644911/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5369289599/10000000000 : ℝ)*X 2 0+(5272644517/10000000000 : ℝ)*X 2 1+(-1103469549/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1060806821/2500000000 : ℝ)*X 0 0+(2217517033/5000000000 : ℝ)*X 0 1+(887007001/2000000000 : ℝ)*X 0 2+(1060806821/2500000000 : ℝ)*X 1 0+(2217517033/5000000000 : ℝ)*X 1 1+(887007001/2000000000 : ℝ)*X 1 2+(1060806821/2500000000 : ℝ)*X 2 0+(2217517033/5000000000 : ℝ)*X 2 1+(887007001/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62227/100000 : ℝ) ≤ (-26445549906339358588038438929157/42500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (67746713/100000000000000 : ℝ)*(upper1) + (169917879/50000000000000 : ℝ)*(upper4) + (72464541/100000000000000 : ℝ)*(upper5) + (486317738306701/12500000000000 : ℝ)*(major0) + (486317738306701/12500000000000 : ℝ)*(major1) + (486317738306701/12500000000000 : ℝ)*(major2) + (4691032673/20000000000000 : ℝ)*(sp2) + (1537140817/25000000000000 : ℝ)*(sp3) + (1037334470661039/20000000000000 : ℝ)*(sp4) + (1037312648447647/20000000000000 : ℝ)*(sp5) + (1296673676516077/25000000000000 : ℝ)*(sp6) + (1307550555442971/50000000000000 : ℝ)*(sp7) + (45807922477/100000000000000 : ℝ)*(sp8) + (77459494719/50000000000000 : ℝ)*(sp13) + (2615107259449211/100000000000000 : ℝ)*(f.failure) + (5186718161227673/100000000000000 : ℝ)*(f.sum) + (405100943939/850000000000000000000000000 : ℝ)*base66 + (1258450354455986573/85000000000000000000000000000000 : ℝ)*base67 + (1191984228925986573/85000000000000000000000000000000 : ℝ)*base69 + (762927667420986573/85000000000000000000000000000000 : ℝ)*base71 + (3425521996989/850000000000000000000000000 : ℝ)*base74 + (1076535672830986573/85000000000000000000000000000000 : ℝ)*base75 + (867859814840986573/85000000000000000000000000000000 : ℝ)*base77 + (930376517880986573/85000000000000000000000000000000 : ℝ)*base79 + (131554343439/850000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (5993099/10000000000000000000000 : ℝ)*base90 + (5993099/10000000000000000000000 : ℝ)*base92 + (5993099/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (59271/100000 : ℝ) ≤ (50382405492935716551233309293857/85000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (71694837/100000000000000 : ℝ)*(lower1) + (180633651/100000000000000 : ℝ)*(upper2) + (77331/625000000000 : ℝ)*(lower4) + (1977038770523597/50000000000000 : ℝ)*(major0) + (1977038770523597/50000000000000 : ℝ)*(major1) + (1977038770523597/50000000000000 : ℝ)*(major2) + (5230572924956289/100000000000000 : ℝ)*(sp0) + (261528856367243/5000000000000 : ℝ)*(sp1) + (1046092549122177/20000000000000 : ℝ)*(sp2) + (664452692441841/25000000000000 : ℝ)*(sp3) + (6113856469/100000000000000 : ℝ)*(sp5) + (130602001/4000000000000 : ℝ)*(sp7) + (30123897611/25000000000000 : ℝ)*(sp10) + (128953063/1250000000000 : ℝ)*(sp12) + (265781403481739/10000000000000 : ℝ)*(f.failure) + (5230583241201329/100000000000000 : ℝ)*(f.sum) + (15307783851417/3400000000000000000000000000 : ℝ)*base65 + (5134264482134810381/340000000000000000000000000000000 : ℝ)*base67 + (1917048791194810381/340000000000000000000000000000000 : ℝ)*base69 + (3023700087125189619/340000000000000000000000000000000 : ℝ)*base72 + (8592220750217/3400000000000000000000000000 : ℝ)*base73 + (1743812514454810381/340000000000000000000000000000000 : ℝ)*base75 + (1156229465874810381/340000000000000000000000000000000 : ℝ)*base77 + (4975802543634810381/340000000000000000000000000000000 : ℝ)*base79 + (9167266843383/3400000000000000000000000000 : ℝ)*base82 + (6824549/1000000000000000000000 : ℝ)*base89 + (6824549/1000000000000000000000 : ℝ)*base91 + (6824549/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (79697/100000 : ℝ) ≤ (33872419077717350290784415913059/42500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (195891747/100000000000000 : ℝ)*(upper0) + (35979683/50000000000000 : ℝ)*(upper1) + (144774409/25000000000000 : ℝ)*(upper2) + (475278067/50000000000000 : ℝ)*(lower5) + (552771701291813/12500000000000 : ℝ)*(major0) + (552771701291813/12500000000000 : ℝ)*(major1) + (552771701291813/12500000000000 : ℝ)*(major2) + (591612245619/100000000000000 : ℝ)*(sp1) + (207963953111/100000000000000 : ℝ)*(sp3) + (33775374201/100000000000000 : ℝ)*(sp4) + (146132311677597/2500000000000 : ℝ)*(sp8) + (2922367315116231/50000000000000 : ℝ)*(sp9) + (5845326242478081/100000000000000 : ℝ)*(sp10) + (1486123205519797/50000000000000 : ℝ)*(sp11) + (1486227187496353/50000000000000 : ℝ)*(f.failure) + (5845326242478081/100000000000000 : ℝ)*(f.sum) + (1289400774693/850000000000000000000000000 : ℝ)*base65 + (492193500010848549/85000000000000000000000000000000 : ℝ)*base67 + (122430612480848549/85000000000000000000000000000000 : ℝ)*base69 + (473921313935848549/85000000000000000000000000000000 : ℝ)*base71 + (34806126914357/850000000000000000000000000 : ℝ)*base74 + (1089428870300848549/85000000000000000000000000000000 : ℝ)*base75 + (1076096870965848549/85000000000000000000000000000000 : ℝ)*base77 + (576664717815848549/85000000000000000000000000000000 : ℝ)*base79 + (6159543649743/850000000000000000000000000 : ℝ)*base81 + (41778223/5000000000000000000000 : ℝ)*base89 + (41778223/5000000000000000000000 : ℝ)*base91 + (41778223/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-83043/100000 : ℝ) ≤ (-3529236997635818827759287070941/4250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9468333/3125000000000 : ℝ)*(upper3) + (69987729/25000000000000 : ℝ)*(lower4) + (575131637/100000000000000 : ℝ)*(upper5) + (111425611486439/2500000000000 : ℝ)*(major0) + (111425611486439/2500000000000 : ℝ)*(major1) + (111425611486439/2500000000000 : ℝ)*(major2) + (50939160987/100000000000000 : ℝ)*(sp4) + (600085777461/50000000000000 : ℝ)*(sp5) + (458686022231/25000000000000 : ℝ)*(sp6) + (81273962989/12500000000000 : ℝ)*(sp7) + (1486449546100037/25000000000000 : ℝ)*(sp12) + (2972324476003107/50000000000000 : ℝ)*(sp13) + (1486003594868053/25000000000000 : ℝ)*(sp14) + (1497614946913799/50000000000000 : ℝ)*(sp15) + (299588008553151/10000000000000 : ℝ)*(f.failure) + (1189169824712227/20000000000000 : ℝ)*(f.sum) + (827921419909/170000000000000000000000000 : ℝ)*base65 + (261304729796548647/17000000000000000000000000000000 : ℝ)*base67 + (117138988131548647/17000000000000000000000000000000 : ℝ)*base69 + (84085211752548647/17000000000000000000000000000000 : ℝ)*base71 + (1509742331899/170000000000000000000000000 : ℝ)*base73 + (120321539121451353/17000000000000000000000000000000 : ℝ)*base76 + (28563140454548647/17000000000000000000000000000000 : ℝ)*base77 + (22685992186548647/17000000000000000000000000000000 : ℝ)*base79 + (357968540921/170000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (7036559/1000000000000000000000 : ℝ)*base90 + (7036559/1000000000000000000000 : ℝ)*base92 + (7036559/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1106_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148771791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14027/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11307/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62227/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59271/100000 : ℝ) else (79697/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83043/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1106_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1106_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148771791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14027/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5653/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62227/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59271/100000 : ℝ) else (79697/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83043/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1106_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1106_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148771791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14027/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5653/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62227/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59271/100000 : ℝ) else (79697/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83043/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1106_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

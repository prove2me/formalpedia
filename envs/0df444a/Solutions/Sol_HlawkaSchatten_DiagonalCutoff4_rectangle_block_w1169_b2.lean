-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1169_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:44:28.573377+00:00
-- url     : https://prove2.me/submissions/80637811-be0a-4c5b-b34f-9fd891a22fc7

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
theorem support_rectangle_w1169_s6_0 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2154014891/10000000000 : ℝ)*x 0 + (5392843487/10000000000 : ℝ)*x 1 + (263294139/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2154014891/10000000000 : ℝ)^4181 ≤ (523651312023/4000000000000 : ℝ)^3157 := by
    have hnat : (2154014891 : ℕ)^4181*4000000000000^3157 ≤ 523651312023^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154014891 10000000000 523651312023 4000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392843487/10000000000 : ℝ)^4181 ≤ (353118616317/800000000000 : ℝ)^3157 := by
    have hnat : (5392843487 : ℕ)^4181*800000000000^3157 ≤ 353118616317^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392843487 10000000000 353118616317 800000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263294139/500000000 : ℝ)^4181 ≤ (42768890148811/100000000000000 : ℝ)^3157 := by
    have hnat : (263294139 : ℕ)^4181*100000000000000^3157 ≤ 42768890148811^3157*500000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263294139 500000000 42768890148811 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2154014891/10000000000 : ℝ), (5392843487/10000000000 : ℝ), (263294139/500000000 : ℝ)] ![(523651312023/4000000000000 : ℝ), (353118616317/800000000000 : ℝ), (42768890148811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2154014891/10000000000 : ℝ)|^4181 ≤ (523651312023/4000000000000 : ℝ)^3157
        have hw : |(-2154014891/10000000000 : ℝ)|=(2154014891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392843487/10000000000 : ℝ)|^4181 ≤ (353118616317/800000000000 : ℝ)^3157
        have hw : |(5392843487/10000000000 : ℝ)|=(5392843487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263294139/500000000 : ℝ)|^4181 ≤ (42768890148811/100000000000000 : ℝ)^3157
        have hw : |(263294139/500000000 : ℝ)|=(263294139/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s6_1 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668091007/1250000000 : ℝ)*x 0 + (-554602223/2500000000 : ℝ)*x 1 + (2632941477/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668091007/1250000000 : ℝ)^4181 ≤ (43619025046149/100000000000000 : ℝ)^3157 := by
    have hnat : (668091007 : ℕ)^4181*100000000000000^3157 ≤ 43619025046149^3157*1250000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668091007 1250000000 43619025046149 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (554602223/2500000000 : ℝ)^4181 ≤ (2722416584997/20000000000000 : ℝ)^3157 := by
    have hnat : (554602223 : ℕ)^4181*20000000000000^3157 ≤ 2722416584997^3157*2500000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554602223 2500000000 2722416584997 20000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632941477/5000000000 : ℝ)^4181 ≤ (8553778404081/20000000000000 : ℝ)^3157 := by
    have hnat : (2632941477 : ℕ)^4181*20000000000000^3157 ≤ 8553778404081^3157*5000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632941477 5000000000 8553778404081 20000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668091007/1250000000 : ℝ), (-554602223/2500000000 : ℝ), (2632941477/5000000000 : ℝ)] ![(43619025046149/100000000000000 : ℝ), (2722416584997/20000000000000 : ℝ), (8553778404081/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668091007/1250000000 : ℝ)|^4181 ≤ (43619025046149/100000000000000 : ℝ)^3157
        have hw : |(668091007/1250000000 : ℝ)|=(668091007/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-554602223/2500000000 : ℝ)|^4181 ≤ (2722416584997/20000000000000 : ℝ)^3157
        have hw : |(-554602223/2500000000 : ℝ)|=(554602223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632941477/5000000000 : ℝ)|^4181 ≤ (8553778404081/20000000000000 : ℝ)^3157
        have hw : |(2632941477/5000000000 : ℝ)|=(2632941477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s6_2 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672364033/5000000000 : ℝ)*x 0 + (1053176521/2000000000 : ℝ)*x 1 + (-110920467/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672364033/5000000000 : ℝ)^4181 ≤ (43619025154231/100000000000000 : ℝ)^3157 := by
    have hnat : (2672364033 : ℕ)^4181*100000000000000^3157 ≤ 43619025154231^3157*5000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672364033 5000000000 43619025154231 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053176521/2000000000 : ℝ)^4181 ≤ (42768888266461/100000000000000 : ℝ)^3157 := by
    have hnat : (1053176521 : ℕ)^4181*100000000000000^3157 ≤ 42768888266461^3157*2000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053176521 2000000000 42768888266461 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (110920467/500000000 : ℝ)^4181 ≤ (3403021641383/25000000000000 : ℝ)^3157 := by
    have hnat : (110920467 : ℕ)^4181*25000000000000^3157 ≤ 3403021641383^3157*500000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110920467 500000000 3403021641383 25000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672364033/5000000000 : ℝ), (1053176521/2000000000 : ℝ), (-110920467/500000000 : ℝ)] ![(43619025154231/100000000000000 : ℝ), (42768888266461/100000000000000 : ℝ), (3403021641383/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672364033/5000000000 : ℝ)|^4181 ≤ (43619025154231/100000000000000 : ℝ)^3157
        have hw : |(2672364033/5000000000 : ℝ)|=(2672364033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053176521/2000000000 : ℝ)|^4181 ≤ (42768888266461/100000000000000 : ℝ)^3157
        have hw : |(1053176521/2000000000 : ℝ)|=(1053176521/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-110920467/500000000 : ℝ)|^4181 ≤ (3403021641383/25000000000000 : ℝ)^3157
        have hw : |(-110920467/500000000 : ℝ)|=(110920467/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s6_3 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (872173677/2000000000 : ℝ)*x 0 + (2117867009/5000000000 : ℝ)*x 1 + (4489658029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (872173677/2000000000 : ℝ)^4181 ≤ (33316961511467/100000000000000 : ℝ)^3157 := by
    have hnat : (872173677 : ℕ)^4181*100000000000000^3157 ≤ 33316961511467^3157*2000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872173677 2000000000 33316961511467 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2117867009/5000000000 : ℝ)^4181 ≤ (250443539081/781250000000 : ℝ)^3157 := by
    have hnat : (2117867009 : ℕ)^4181*781250000000^3157 ≤ 250443539081^3157*5000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117867009 5000000000 250443539081 781250000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4489658029/10000000000 : ℝ)^4181 ≤ (17313132741049/50000000000000 : ℝ)^3157 := by
    have hnat : (4489658029 : ℕ)^4181*50000000000000^3157 ≤ 17313132741049^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489658029 10000000000 17313132741049 50000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(872173677/2000000000 : ℝ), (2117867009/5000000000 : ℝ), (4489658029/10000000000 : ℝ)] ![(33316961511467/100000000000000 : ℝ), (250443539081/781250000000 : ℝ), (17313132741049/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(872173677/2000000000 : ℝ)|^4181 ≤ (33316961511467/100000000000000 : ℝ)^3157
        have hw : |(872173677/2000000000 : ℝ)|=(872173677/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2117867009/5000000000 : ℝ)|^4181 ≤ (250443539081/781250000000 : ℝ)^3157
        have hw : |(2117867009/5000000000 : ℝ)|=(2117867009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4489658029/10000000000 : ℝ)|^4181 ≤ (17313132741049/50000000000000 : ℝ)^3157
        have hw : |(4489658029/10000000000 : ℝ)|=(4489658029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s6_4 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1077009877/5000000000 : ℝ)*x 0 + (1316550851/2500000000 : ℝ)*x 1 + (5392521713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077009877/5000000000 : ℝ)^4181 ≤ (654566097131/5000000000000 : ℝ)^3157 := by
    have hnat : (1077009877 : ℕ)^4181*5000000000000^3157 ≤ 654566097131^3157*5000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077009877 5000000000 654566097131 5000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316550851/2500000000 : ℝ)^4181 ≤ (21386169453303/50000000000000 : ℝ)^3157 := by
    have hnat : (1316550851 : ℕ)^4181*50000000000000^3157 ≤ 21386169453303^3157*2500000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316550851 2500000000 21386169453303 50000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392521713/10000000000 : ℝ)^4181 ≤ (8827267826129/20000000000000 : ℝ)^3157 := by
    have hnat : (5392521713 : ℕ)^4181*20000000000000^3157 ≤ 8827267826129^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392521713 10000000000 8827267826129 20000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1077009877/5000000000 : ℝ), (1316550851/2500000000 : ℝ), (5392521713/10000000000 : ℝ)] ![(654566097131/5000000000000 : ℝ), (21386169453303/50000000000000 : ℝ), (8827267826129/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1077009877/5000000000 : ℝ)|^4181 ≤ (654566097131/5000000000000 : ℝ)^3157
        have hw : |(-1077009877/5000000000 : ℝ)|=(1077009877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316550851/2500000000 : ℝ)|^4181 ≤ (21386169453303/50000000000000 : ℝ)^3157
        have hw : |(1316550851/2500000000 : ℝ)|=(1316550851/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392521713/10000000000 : ℝ)|^4181 ≤ (8827267826129/20000000000000 : ℝ)^3157
        have hw : |(5392521713/10000000000 : ℝ)|=(5392521713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s6_5 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312498431/10000000000 : ℝ)*x 0 + (-522942519/2500000000 : ℝ)*x 1 + (5392521709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312498431/10000000000 : ℝ)^4181 ≤ (10817754974977/25000000000000 : ℝ)^3157 := by
    have hnat : (5312498431 : ℕ)^4181*25000000000000^3157 ≤ 10817754974977^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312498431 10000000000 10817754974977 25000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (522942519/2500000000 : ℝ)^4181 ≤ (1259264099529/10000000000000 : ℝ)^3157 := by
    have hnat : (522942519 : ℕ)^4181*10000000000000^3157 ≤ 1259264099529^3157*2500000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522942519 2500000000 1259264099529 10000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392521709/10000000000 : ℝ)^4181 ≤ (44136339087287/100000000000000 : ℝ)^3157 := by
    have hnat : (5392521709 : ℕ)^4181*100000000000000^3157 ≤ 44136339087287^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392521709 10000000000 44136339087287 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312498431/10000000000 : ℝ), (-522942519/2500000000 : ℝ), (5392521709/10000000000 : ℝ)] ![(10817754974977/25000000000000 : ℝ), (1259264099529/10000000000000 : ℝ), (44136339087287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312498431/10000000000 : ℝ)|^4181 ≤ (10817754974977/25000000000000 : ℝ)^3157
        have hw : |(5312498431/10000000000 : ℝ)|=(5312498431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-522942519/2500000000 : ℝ)|^4181 ≤ (1259264099529/10000000000000 : ℝ)^3157
        have hw : |(-522942519/2500000000 : ℝ)|=(522942519/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392521709/10000000000 : ℝ)|^4181 ≤ (44136339087287/100000000000000 : ℝ)^3157
        have hw : |(5392521709/10000000000 : ℝ)|=(5392521709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s6_6 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656249217/5000000000 : ℝ)*x 0 + (539252167/1000000000 : ℝ)*x 1 + (-522942531/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656249217/5000000000 : ℝ)^4181 ≤ (4327101993227/10000000000000 : ℝ)^3157 := by
    have hnat : (2656249217 : ℕ)^4181*10000000000000^3157 ≤ 4327101993227^3157*5000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656249217 5000000000 4327101993227 10000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539252167/1000000000 : ℝ)^4181 ≤ (22068169332273/50000000000000 : ℝ)^3157 := by
    have hnat : (539252167 : ℕ)^4181*50000000000000^3157 ≤ 22068169332273^3157*1000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539252167 1000000000 22068169332273 50000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (522942531/2500000000 : ℝ)^4181 ≤ (6296320688991/50000000000000 : ℝ)^3157 := by
    have hnat : (522942531 : ℕ)^4181*50000000000000^3157 ≤ 6296320688991^3157*2500000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522942531 2500000000 6296320688991 50000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656249217/5000000000 : ℝ), (539252167/1000000000 : ℝ), (-522942531/2500000000 : ℝ)] ![(4327101993227/10000000000000 : ℝ), (22068169332273/50000000000000 : ℝ), (6296320688991/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656249217/5000000000 : ℝ)|^4181 ≤ (4327101993227/10000000000000 : ℝ)^3157
        have hw : |(2656249217/5000000000 : ℝ)|=(2656249217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539252167/1000000000 : ℝ)|^4181 ≤ (22068169332273/50000000000000 : ℝ)^3157
        have hw : |(539252167/1000000000 : ℝ)|=(539252167/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-522942531/2500000000 : ℝ)|^4181 ≤ (6296320688991/50000000000000 : ℝ)^3157
        have hw : |(-522942531/2500000000 : ℝ)|=(522942531/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s6_7 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4360878169/10000000000 : ℝ)*x 0 + (2244508213/5000000000 : ℝ)*x 1 + (4236377943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360878169/10000000000 : ℝ)^4181 ≤ (33317060506771/100000000000000 : ℝ)^3157 := by
    have hnat : (4360878169 : ℕ)^4181*100000000000000^3157 ≤ 33317060506771^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360878169 10000000000 33317060506771 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2244508213/5000000000 : ℝ)^4181 ≤ (1081866008403/3125000000000 : ℝ)^3157 := by
    have hnat : (2244508213 : ℕ)^4181*3125000000000^3157 ≤ 1081866008403^3157*5000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244508213 5000000000 1081866008403 3125000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4236377943/10000000000 : ℝ)^4181 ≤ (32063227206549/100000000000000 : ℝ)^3157 := by
    have hnat : (4236377943 : ℕ)^4181*100000000000000^3157 ≤ 32063227206549^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4236377943 10000000000 32063227206549 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360878169/10000000000 : ℝ), (2244508213/5000000000 : ℝ), (4236377943/10000000000 : ℝ)] ![(33317060506771/100000000000000 : ℝ), (1081866008403/3125000000000 : ℝ), (32063227206549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360878169/10000000000 : ℝ)|^4181 ≤ (33317060506771/100000000000000 : ℝ)^3157
        have hw : |(4360878169/10000000000 : ℝ)|=(4360878169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2244508213/5000000000 : ℝ)|^4181 ≤ (1081866008403/3125000000000 : ℝ)^3157
        have hw : |(2244508213/5000000000 : ℝ)|=(2244508213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4236377943/10000000000 : ℝ)|^4181 ≤ (32063227206549/100000000000000 : ℝ)^3157
        have hw : |(4236377943/10000000000 : ℝ)|=(4236377943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1169_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150000783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (141/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5677/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5691/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14071/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (141/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5677/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (141/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5677/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (141/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5677/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (141/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5677/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (141/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5677/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (141/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5677/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5677/50000 : ℝ) ^ (8361/2048 : ℝ) ≤ (3471897519192083/25000000000000000000 : ℝ) := by
    have hpowers : (5677/50000 : ℝ)^8361 ≤ (3471897519192083/25000000000000000000 : ℝ)^2048 := by
      have hnat : (5677 : ℕ)^8361*25000000000000000000^2048 ≤ 3471897519192083^2048*50000^8361 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5677 50000 3471897519192083 25000000000000000000 8361 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5677/50000 : ℝ)) (X := (3471897519192083/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (141/1000 : ℝ) ^ (8361/2048 : ℝ) ≤ (3362562850567291/10000000000000000000 : ℝ) := by
    have hpowers : (141/1000 : ℝ)^8361 ≤ (3362562850567291/10000000000000000000 : ℝ)^2048 := by
      have hnat : (141 : ℕ)^8361*10000000000000000000^2048 ≤ 3362562850567291^2048*1000^8361 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        141 1000 3362562850567291 10000000000000000000 8361 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (141/1000 : ℝ)) (X := (3362562850567291/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503471897519192083/12500000000000000000 : ℝ) ≤ (10000680272756687/10000000000000000 : ℝ) ^ (8361/2048 : ℝ) := by
    have hpowers : (12503471897519192083/12500000000000000000 : ℝ)^2048 ≤ (10000680272756687/10000000000000000 : ℝ)^8361 := by
      have hnat : (12503471897519192083 : ℕ)^2048*10000000000000000^8361 ≤ 10000680272756687^8361*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503471897519192083 12500000000000000000 10000680272756687 10000000000000000 2048 8361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000680272756687/10000000000000000 : ℝ)) (X := (12503471897519192083/12500000000000000000 : ℝ)) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023756609291220621/50000000000000000000 : ℝ) ≤ (5000581806135909/5000000000000000 : ℝ) ^ (8361/2048 : ℝ) := by
    have hpowers : (50023756609291220621/50000000000000000000 : ℝ)^2048 ≤ (5000581806135909/5000000000000000 : ℝ)^8361 := by
      have hnat : (50023756609291220621 : ℕ)^2048*5000000000000000^8361 ≤ 5000581806135909^8361*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023756609291220621 50000000000000000000 5000581806135909 5000000000000000 2048 8361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000581806135909/5000000000000000 : ℝ)) (X := (50023756609291220621/50000000000000000000 : ℝ)) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003362562850567291/5000000000000000000 : ℝ) ≤ (10001646951786949/10000000000000000 : ℝ) ^ (8361/2048 : ℝ) := by
    have hpowers : (5003362562850567291/5000000000000000000 : ℝ)^2048 ≤ (10001646951786949/10000000000000000 : ℝ)^8361 := by
      have hnat : (5003362562850567291 : ℕ)^2048*10000000000000000^8361 ≤ 10001646951786949^8361*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003362562850567291 5000000000000000000 10001646951786949 10000000000000000 2048 8361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001646951786949/10000000000000000 : ℝ)) (X := (5003362562850567291/5000000000000000000 : ℝ)) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3471897519192083/25000000000000000000 : ℝ) ≤ ((13725446177640133877/13730000000000000000 : ℝ)+2*(483339515131/274600000000000 : ℝ)*(5677/50000 : ℝ))^(8361/2048 : ℝ) := by
    rw [show (13725446177640133877/13730000000000000000 : ℝ)+2*(483339515131/274600000000000 : ℝ)*(5677/50000 : ℝ)=(10000680272756687/10000000000000000 : ℝ) by norm_num, show 1+2*(3471897519192083/25000000000000000000 : ℝ)=(12503471897519192083/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3362562850567291/10000000000000000000 : ℝ)+(3471897519192083/25000000000000000000 : ℝ) ≤ ((13725446177640133877/13730000000000000000 : ℝ)+(483339515131/274600000000000 : ℝ)*((141/1000 : ℝ)+(5677/50000 : ℝ)))^(8361/2048 : ℝ) := by
    rw [show (13725446177640133877/13730000000000000000 : ℝ)+(483339515131/274600000000000 : ℝ)*((141/1000 : ℝ)+(5677/50000 : ℝ))=(5000581806135909/5000000000000000 : ℝ) by norm_num, show 1+(3362562850567291/10000000000000000000 : ℝ)+(3471897519192083/25000000000000000000 : ℝ)=(50023756609291220621/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3362562850567291/10000000000000000000 : ℝ) ≤ ((13725446177640133877/13730000000000000000 : ℝ)+2*(483339515131/274600000000000 : ℝ)*(141/1000 : ℝ))^(8361/2048 : ℝ) := by
    rw [show (13725446177640133877/13730000000000000000 : ℝ)+2*(483339515131/274600000000000 : ℝ)*(141/1000 : ℝ)=(10001646951786949/10000000000000000 : ℝ) by norm_num, show 1+2*(3362562850567291/10000000000000000000 : ℝ)=(5003362562850567291/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13725446177640133877/13730000000000000000 : ℝ)*(X 1 0+X 2 0)+(483339515131/274600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8361/2048 : ℝ)) (lo := (5677/50000 : ℝ)) (hi := (141/1000 : ℝ)) (c := (13725446177640133877/13730000000000000000 : ℝ)) (alpha := (483339515131/274600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13725446177640133877/13730000000000000000 : ℝ)*(X 0 1+X 2 1)+(483339515131/274600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8361/2048 : ℝ)) (lo := (5677/50000 : ℝ)) (hi := (141/1000 : ℝ)) (c := (13725446177640133877/13730000000000000000 : ℝ)) (alpha := (483339515131/274600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13725446177640133877/13730000000000000000 : ℝ)*(X 0 2+X 1 2)+(483339515131/274600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8361/2048 : ℝ)) (lo := (5677/50000 : ℝ)) (hi := (141/1000 : ℝ)) (c := (13725446177640133877/13730000000000000000 : ℝ)) (alpha := (483339515131/274600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2154014891/10000000000 : ℝ)*X 0 0+(5392843487/10000000000 : ℝ)*X 0 1+(263294139/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668091007/1250000000 : ℝ)*X 1 0+(-554602223/2500000000 : ℝ)*X 1 1+(2632941477/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672364033/5000000000 : ℝ)*X 2 0+(1053176521/2000000000 : ℝ)*X 2 1+(-110920467/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((872173677/2000000000 : ℝ)*X 0 0+(2117867009/5000000000 : ℝ)*X 0 1+(4489658029/10000000000 : ℝ)*X 0 2+(872173677/2000000000 : ℝ)*X 1 0+(2117867009/5000000000 : ℝ)*X 1 1+(4489658029/10000000000 : ℝ)*X 1 2+(872173677/2000000000 : ℝ)*X 2 0+(2117867009/5000000000 : ℝ)*X 2 1+(4489658029/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1077009877/5000000000 : ℝ)*X 0 0+(1316550851/2500000000 : ℝ)*X 0 1+(5392521713/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312498431/10000000000 : ℝ)*X 1 0+(-522942519/2500000000 : ℝ)*X 1 1+(5392521709/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656249217/5000000000 : ℝ)*X 2 0+(539252167/1000000000 : ℝ)*X 2 1+(-522942531/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4360878169/10000000000 : ℝ)*X 0 0+(2244508213/5000000000 : ℝ)*X 0 1+(4236377943/10000000000 : ℝ)*X 0 2+(4360878169/10000000000 : ℝ)*X 1 0+(2244508213/5000000000 : ℝ)*X 1 1+(4236377943/10000000000 : ℝ)*X 1 2+(4360878169/10000000000 : ℝ)*X 2 0+(2244508213/5000000000 : ℝ)*X 2 1+(4236377943/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (222434846383947731656569927/42906250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (301482997/50000000000000 : ℝ)*(base19) + (137526013/25000000000000 : ℝ)*(base23) + (25201781/100000000000000 : ℝ)*(upper2) + (5415757/2500000000000 : ℝ)*(upper3) + (738419731929967/12500000000000 : ℝ)*(major0) + (738419731929967/12500000000000 : ℝ)*(major1) + (738419731929967/12500000000000 : ℝ)*(major2) + (984560158583807/12500000000000 : ℝ)*(sp0) + (1969124230577867/25000000000000 : ℝ)*(sp1) + (1575295589124037/20000000000000 : ℝ)*(sp2) + (492275019828399/12500000000000 : ℝ)*(sp3) + (8128303503/50000000000000 : ℝ)*(sp4) + (761182129/4000000000000 : ℝ)*(sp6) + (17854167939/100000000000000 : ℝ)*(sp7) + (3938218012795131/100000000000000 : ℝ)*(f.failure) + (3938248762638731/50000000000000 : ℝ)*(f.sum) + (14646865677493/6865000000000000000000000000 : ℝ)*base65 + (1203177600162707941/171625000000000000000000000000000 : ℝ)*base68 + (1984382169387832941/171625000000000000000000000000000 : ℝ)*base70 + (601622167308832941/171625000000000000000000000000000 : ℝ)*base72 + (4719475788299/3432500000000000000000000000 : ℝ)*base73 + (1008152998978082941/171625000000000000000000000000000 : ℝ)*base76 + (1683115796416667059/171625000000000000000000000000000 : ℝ)*base77 + (2247155171758582941/171625000000000000000000000000000 : ℝ)*base80 + (15930698699217/6865000000000000000000000000 : ℝ)*base82 + (68587573/10000000000000000000000 : ℝ)*base89 + (68587573/10000000000000000000000 : ℝ)*base91 + (68587573/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (916422868709898704136281607/171625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (90954217/10000000000000 : ℝ)*(base19) + (444651627/50000000000000 : ℝ)*(base23) + (1484547/100000000000000 : ℝ)*(upper2) + (21445961/25000000000000 : ℝ)*(upper3) + (61623827/50000000000000 : ℝ)*(upper5) + (2968683705483503/50000000000000 : ℝ)*(major0) + (2968683705483503/50000000000000 : ℝ)*(major1) + (2968683705483503/50000000000000 : ℝ)*(major2) + (5213556199/20000000000000 : ℝ)*(sp1) + (21534239071/100000000000000 : ℝ)*(sp2) + (7916510365230683/100000000000000 : ℝ)*(sp4) + (3958241693953759/50000000000000 : ℝ)*(sp5) + (3958243970844179/50000000000000 : ℝ)*(sp6) + (247389017419621/6250000000000 : ℝ)*(sp7) + (247389017419621/6250000000000 : ℝ)*(f.failure) + (7916510365230683/100000000000000 : ℝ)*(f.sum) + (957270382163/6865000000000000000000000000 : ℝ)*base65 + (870356557952418869/686500000000000000000000000000000 : ℝ)*base68 + (3619713196194081131/686500000000000000000000000000000 : ℝ)*base69 + (2783398620416581131/686500000000000000000000000000000 : ℝ)*base71 + (9238096445327/6865000000000000000000000000 : ℝ)*base74 + (9974199178519581131/686500000000000000000000000000000 : ℝ)*base75 + (1046348988496581131/686500000000000000000000000000000 : ℝ)*base77 + (1373034217868081131/686500000000000000000000000000000 : ℝ)*base79 + (17122815077553/6865000000000000000000000000 : ℝ)*base81 + (2063243/625000000000000000000 : ℝ)*base89 + (2063243/625000000000000000000 : ℝ)*base91 + (2063243/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1169_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150000783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (141/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5677/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5691/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14071/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1169_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1169_s7_0 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1077019197/5000000000 : ℝ)*x 0 + (1078511923/2000000000 : ℝ)*x 1 + (2633075631/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077019197/5000000000 : ℝ)^4181 ≤ (327286799383/2500000000000 : ℝ)^3157 := by
    have hnat : (1077019197 : ℕ)^4181*2500000000000^3157 ≤ 327286799383^3157*5000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077019197 5000000000 327286799383 2500000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078511923/2000000000 : ℝ)^4181 ≤ (2758546873159/6250000000000 : ℝ)^3157 := by
    have hnat : (1078511923 : ℕ)^4181*6250000000000^3157 ≤ 2758546873159^3157*2000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078511923 2000000000 2758546873159 6250000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633075631/5000000000 : ℝ)^4181 ≤ (42771778042117/100000000000000 : ℝ)^3157 := by
    have hnat : (2633075631 : ℕ)^4181*100000000000000^3157 ≤ 42771778042117^3157*5000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633075631 5000000000 42771778042117 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1077019197/5000000000 : ℝ), (1078511923/2000000000 : ℝ), (2633075631/5000000000 : ℝ)] ![(327286799383/2500000000000 : ℝ), (2758546873159/6250000000000 : ℝ), (42771778042117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1077019197/5000000000 : ℝ)|^4181 ≤ (327286799383/2500000000000 : ℝ)^3157
        have hw : |(-1077019197/5000000000 : ℝ)|=(1077019197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078511923/2000000000 : ℝ)|^4181 ≤ (2758546873159/6250000000000 : ℝ)^3157
        have hw : |(1078511923/2000000000 : ℝ)|=(1078511923/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633075631/5000000000 : ℝ)|^4181 ≤ (42771778042117/100000000000000 : ℝ)^3157
        have hw : |(2633075631/5000000000 : ℝ)|=(2633075631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s7_1 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336164221/2500000000 : ℝ)*x 0 + (-2218148401/10000000000 : ℝ)*x 1 + (263307563/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336164221/2500000000 : ℝ)^4181 ≤ (1744730232083/4000000000000 : ℝ)^3157 := by
    have hnat : (1336164221 : ℕ)^4181*4000000000000^3157 ≤ 1744730232083^3157*2500000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336164221 2500000000 1744730232083 4000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2218148401/10000000000 : ℝ)^4181 ≤ (1360996615813/10000000000000 : ℝ)^3157 := by
    have hnat : (2218148401 : ℕ)^4181*10000000000000^3157 ≤ 1360996615813^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2218148401 10000000000 1360996615813 10000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263307563/500000000 : ℝ)^4181 ≤ (10692944505151/25000000000000 : ℝ)^3157 := by
    have hnat : (263307563 : ℕ)^4181*25000000000000^3157 ≤ 10692944505151^3157*500000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263307563 500000000 10692944505151 25000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336164221/2500000000 : ℝ), (-2218148401/10000000000 : ℝ), (263307563/500000000 : ℝ)] ![(1744730232083/4000000000000 : ℝ), (1360996615813/10000000000000 : ℝ), (10692944505151/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336164221/2500000000 : ℝ)|^4181 ≤ (1744730232083/4000000000000 : ℝ)^3157
        have hw : |(1336164221/2500000000 : ℝ)|=(1336164221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2218148401/10000000000 : ℝ)|^4181 ≤ (1360996615813/10000000000000 : ℝ)^3157
        have hw : |(-2218148401/10000000000 : ℝ)|=(2218148401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263307563/500000000 : ℝ)|^4181 ≤ (10692944505151/25000000000000 : ℝ)^3157
        have hw : |(263307563/500000000 : ℝ)|=(263307563/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s7_2 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344656883/10000000000 : ℝ)*x 0 + (5266151261/10000000000 : ℝ)*x 1 + (-2218148401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344656883/10000000000 : ℝ)^4181 ≤ (43618255791267/100000000000000 : ℝ)^3157 := by
    have hnat : (5344656883 : ℕ)^4181*100000000000000^3157 ≤ 43618255791267^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344656883 10000000000 43618255791267 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266151261/10000000000 : ℝ)^4181 ≤ (42771778031361/100000000000000 : ℝ)^3157 := by
    have hnat : (5266151261 : ℕ)^4181*100000000000000^3157 ≤ 42771778031361^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266151261 10000000000 42771778031361 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2218148401/10000000000 : ℝ)^4181 ≤ (1360996615813/10000000000000 : ℝ)^3157 := by
    have hnat : (2218148401 : ℕ)^4181*10000000000000^3157 ≤ 1360996615813^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2218148401 10000000000 1360996615813 10000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344656883/10000000000 : ℝ), (5266151261/10000000000 : ℝ), (-2218148401/10000000000 : ℝ)] ![(43618255791267/100000000000000 : ℝ), (42771778031361/100000000000000 : ℝ), (1360996615813/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344656883/10000000000 : ℝ)|^4181 ≤ (43618255791267/100000000000000 : ℝ)^3157
        have hw : |(5344656883/10000000000 : ℝ)|=(5344656883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266151261/10000000000 : ℝ)|^4181 ≤ (42771778031361/100000000000000 : ℝ)^3157
        have hw : |(5266151261/10000000000 : ℝ)|=(5266151261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2218148401/10000000000 : ℝ)|^4181 ≤ (1360996615813/10000000000000 : ℝ)^3157
        have hw : |(-2218148401/10000000000 : ℝ)|=(2218148401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s7_3 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4360882497/10000000000 : ℝ)*x 0 + (4236284831/10000000000 : ℝ)*x 1 + (4489103517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360882497/10000000000 : ℝ)^4181 ≤ (33317104297849/100000000000000 : ℝ)^3157 := by
    have hnat : (4360882497 : ℕ)^4181*100000000000000^3157 ≤ 33317104297849^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360882497 10000000000 33317104297849 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4236284831/10000000000 : ℝ)^4181 ≤ (32062293904483/100000000000000 : ℝ)^3157 := by
    have hnat : (4236284831 : ℕ)^4181*100000000000000^3157 ≤ 32062293904483^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4236284831 10000000000 32062293904483 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4489103517/10000000000 : ℝ)^4181 ≤ (34620601782283/100000000000000 : ℝ)^3157 := by
    have hnat : (4489103517 : ℕ)^4181*100000000000000^3157 ≤ 34620601782283^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489103517 10000000000 34620601782283 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360882497/10000000000 : ℝ), (4236284831/10000000000 : ℝ), (4489103517/10000000000 : ℝ)] ![(33317104297849/100000000000000 : ℝ), (32062293904483/100000000000000 : ℝ), (34620601782283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360882497/10000000000 : ℝ)|^4181 ≤ (33317104297849/100000000000000 : ℝ)^3157
        have hw : |(4360882497/10000000000 : ℝ)|=(4360882497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4236284831/10000000000 : ℝ)|^4181 ≤ (32062293904483/100000000000000 : ℝ)^3157
        have hw : |(4236284831/10000000000 : ℝ)|=(4236284831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4489103517/10000000000 : ℝ)|^4181 ≤ (34620601782283/100000000000000 : ℝ)^3157
        have hw : |(4489103517/10000000000 : ℝ)|=(4489103517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s7_4 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-86161741/400000000 : ℝ)*x 0 + (1316617231/2500000000 : ℝ)*x 1 + (5392240571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86161741/400000000 : ℝ)^4181 ≤ (13091513274631/100000000000000 : ℝ)^3157 := by
    have hnat : (86161741 : ℕ)^4181*100000000000000^3157 ≤ 13091513274631^3157*400000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86161741 400000000 13091513274631 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316617231/2500000000 : ℝ)^4181 ≤ (10693798748917/25000000000000 : ℝ)^3157 := by
    have hnat : (1316617231 : ℕ)^4181*25000000000000^3157 ≤ 10693798748917^3157*2500000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316617231 2500000000 10693798748917 25000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392240571/10000000000 : ℝ)^4181 ≤ (44133291712501/100000000000000 : ℝ)^3157 := by
    have hnat : (5392240571 : ℕ)^4181*100000000000000^3157 ≤ 44133291712501^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392240571 10000000000 44133291712501 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-86161741/400000000 : ℝ), (1316617231/2500000000 : ℝ), (5392240571/10000000000 : ℝ)] ![(13091513274631/100000000000000 : ℝ), (10693798748917/25000000000000 : ℝ), (44133291712501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-86161741/400000000 : ℝ)|^4181 ≤ (13091513274631/100000000000000 : ℝ)^3157
        have hw : |(-86161741/400000000 : ℝ)|=(86161741/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316617231/2500000000 : ℝ)|^4181 ≤ (10693798748917/25000000000000 : ℝ)^3157
        have hw : |(1316617231/2500000000 : ℝ)|=(1316617231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392240571/10000000000 : ℝ)|^4181 ≤ (44133291712501/100000000000000 : ℝ)^3157
        have hw : |(5392240571/10000000000 : ℝ)|=(5392240571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s7_5 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656283527/5000000000 : ℝ)*x 0 + (-1046029747/5000000000 : ℝ)*x 1 + (674030067/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656283527/5000000000 : ℝ)^4181 ≤ (8654352028651/20000000000000 : ℝ)^3157 := by
    have hnat : (2656283527 : ℕ)^4181*20000000000000^3157 ≤ 8654352028651^3157*5000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656283527 5000000000 8654352028651 20000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1046029747/5000000000 : ℝ)^4181 ≤ (12594948506103/100000000000000 : ℝ)^3157 := by
    have hnat : (1046029747 : ℕ)^4181*100000000000000^3157 ≤ 12594948506103^3157*5000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046029747 5000000000 12594948506103 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674030067/1250000000 : ℝ)^4181 ≤ (11033322833281/25000000000000 : ℝ)^3157 := by
    have hnat : (674030067 : ℕ)^4181*25000000000000^3157 ≤ 11033322833281^3157*1250000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674030067 1250000000 11033322833281 25000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656283527/5000000000 : ℝ), (-1046029747/5000000000 : ℝ), (674030067/1250000000 : ℝ)] ![(8654352028651/20000000000000 : ℝ), (12594948506103/100000000000000 : ℝ), (11033322833281/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656283527/5000000000 : ℝ)|^4181 ≤ (8654352028651/20000000000000 : ℝ)^3157
        have hw : |(2656283527/5000000000 : ℝ)|=(2656283527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1046029747/5000000000 : ℝ)|^4181 ≤ (12594948506103/100000000000000 : ℝ)^3157
        have hw : |(-1046029747/5000000000 : ℝ)|=(1046029747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674030067/1250000000 : ℝ)|^4181 ≤ (11033322833281/25000000000000 : ℝ)^3157
        have hw : |(674030067/1250000000 : ℝ)|=(674030067/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s7_6 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656283647/5000000000 : ℝ)*x 0 + (2696120197/5000000000 : ℝ)*x 1 + (-1046029681/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656283647/5000000000 : ℝ)^4181 ≤ (8654352546433/20000000000000 : ℝ)^3157 := by
    have hnat : (2656283647 : ℕ)^4181*20000000000000^3157 ≤ 8654352546433^3157*5000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656283647 5000000000 8654352546433 20000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696120197/5000000000 : ℝ)^4181 ≤ (22066644896969/50000000000000 : ℝ)^3157 := by
    have hnat : (2696120197 : ℕ)^4181*50000000000000^3157 ≤ 22066644896969^3157*5000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696120197 5000000000 22066644896969 50000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1046029681/5000000000 : ℝ)^4181 ≤ (3148736863413/25000000000000 : ℝ)^3157 := by
    have hnat : (1046029681 : ℕ)^4181*25000000000000^3157 ≤ 3148736863413^3157*5000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046029681 5000000000 3148736863413 25000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656283647/5000000000 : ℝ), (2696120197/5000000000 : ℝ), (-1046029681/5000000000 : ℝ)] ![(8654352546433/20000000000000 : ℝ), (22066644896969/50000000000000 : ℝ), (3148736863413/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656283647/5000000000 : ℝ)|^4181 ≤ (8654352546433/20000000000000 : ℝ)^3157
        have hw : |(2656283647/5000000000 : ℝ)|=(2656283647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696120197/5000000000 : ℝ)|^4181 ≤ (22066644896969/50000000000000 : ℝ)^3157
        have hw : |(2696120197/5000000000 : ℝ)|=(2696120197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1046029681/5000000000 : ℝ)|^4181 ≤ (3148736863413/25000000000000 : ℝ)^3157
        have hw : |(-1046029681/5000000000 : ℝ)|=(1046029681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s7_7 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4360892219/10000000000 : ℝ)*x 0 + (2244233843/5000000000 : ℝ)*x 1 + (2118461443/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360892219/10000000000 : ℝ)^4181 ≤ (6663440533187/20000000000000 : ℝ)^3157 := by
    have hnat : (4360892219 : ℕ)^4181*20000000000000^3157 ≤ 6663440533187^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360892219 10000000000 6663440533187 20000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2244233843/5000000000 : ℝ)^4181 ≤ (34614107782053/100000000000000 : ℝ)^3157 := by
    have hnat : (2244233843 : ℕ)^4181*100000000000000^3157 ≤ 34614107782053^3157*5000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244233843 5000000000 34614107782053 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2118461443/5000000000 : ℝ)^4181 ≤ (16034344770313/50000000000000 : ℝ)^3157 := by
    have hnat : (2118461443 : ℕ)^4181*50000000000000^3157 ≤ 16034344770313^3157*5000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118461443 5000000000 16034344770313 50000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360892219/10000000000 : ℝ), (2244233843/5000000000 : ℝ), (2118461443/5000000000 : ℝ)] ![(6663440533187/20000000000000 : ℝ), (34614107782053/100000000000000 : ℝ), (16034344770313/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360892219/10000000000 : ℝ)|^4181 ≤ (6663440533187/20000000000000 : ℝ)^3157
        have hw : |(4360892219/10000000000 : ℝ)|=(4360892219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2244233843/5000000000 : ℝ)|^4181 ≤ (34614107782053/100000000000000 : ℝ)^3157
        have hw : |(2244233843/5000000000 : ℝ)|=(2244233843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2118461443/5000000000 : ℝ)|^4181 ≤ (16034344770313/50000000000000 : ℝ)^3157
        have hw : |(2118461443/5000000000 : ℝ)|=(2118461443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1169_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150000783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14071/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5691/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11387/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2813/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14071/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5691/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14071/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5691/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14071/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5691/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14071/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5691/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14071/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5691/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14071/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5691/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5691/50000 : ℝ) ^ (8361/2048 : ℝ) ≤ (3506985203128599/25000000000000000000 : ℝ) := by
    have hpowers : (5691/50000 : ℝ)^8361 ≤ (3506985203128599/25000000000000000000 : ℝ)^2048 := by
      have hnat : (5691 : ℕ)^8361*25000000000000000000^2048 ≤ 3506985203128599^2048*50000^8361 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5691 50000 3506985203128599 25000000000000000000 8361 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5691/50000 : ℝ)) (X := (3506985203128599/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14071/100000 : ℝ) ^ (8361/2048 : ℝ) ≤ (16672089447615893/50000000000000000000 : ℝ) := by
    have hpowers : (14071/100000 : ℝ)^8361 ≤ (16672089447615893/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14071 : ℕ)^8361*50000000000000000000^2048 ≤ 16672089447615893^2048*100000^8361 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14071 100000 16672089447615893 50000000000000000000 8361 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14071/100000 : ℝ)) (X := (16672089447615893/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503506985203128599/12500000000000000000 : ℝ) ≤ (10000687146999869/10000000000000000 : ℝ) ^ (8361/2048 : ℝ) := by
    have hpowers : (12503506985203128599/12500000000000000000 : ℝ)^2048 ≤ (10000687146999869/10000000000000000 : ℝ)^8361 := by
      have hnat : (12503506985203128599 : ℕ)^2048*10000000000000000^8361 ≤ 10000687146999869^8361*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503506985203128599 12500000000000000000 10000687146999869 10000000000000000 2048 8361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000687146999869/10000000000000000 : ℝ)) (X := (12503506985203128599/12500000000000000000 : ℝ)) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023686059853873091/50000000000000000000 : ℝ) ≤ (2500290039334477/2500000000000000 : ℝ) ^ (8361/2048 : ℝ) := by
    have hpowers : (50023686059853873091/50000000000000000000 : ℝ)^2048 ≤ (2500290039334477/2500000000000000 : ℝ)^8361 := by
      have hnat : (50023686059853873091 : ℕ)^2048*2500000000000000^8361 ≤ 2500290039334477^8361*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023686059853873091 50000000000000000000 2500290039334477 2500000000000000 2048 8361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500290039334477/2500000000000000 : ℝ)) (X := (50023686059853873091/50000000000000000000 : ℝ)) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016672089447615893/25000000000000000000 : ℝ) ≤ (10001633167675947/10000000000000000 : ℝ) ^ (8361/2048 : ℝ) := by
    have hpowers : (25016672089447615893/25000000000000000000 : ℝ)^2048 ≤ (10001633167675947/10000000000000000 : ℝ)^8361 := by
      have hnat : (25016672089447615893 : ℕ)^2048*10000000000000000^8361 ≤ 10001633167675947^8361*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016672089447615893 25000000000000000000 10001633167675947 10000000000000000 2048 8361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001633167675947/10000000000000000 : ℝ)) (X := (25016672089447615893/25000000000000000000 : ℝ)) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3506985203128599/25000000000000000000 : ℝ) ≤ ((5376216026189505589/5378000000000000000 : ℝ)+2*(473010338039/268900000000000 : ℝ)*(5691/50000 : ℝ))^(8361/2048 : ℝ) := by
    rw [show (5376216026189505589/5378000000000000000 : ℝ)+2*(473010338039/268900000000000 : ℝ)*(5691/50000 : ℝ)=(10000687146999869/10000000000000000 : ℝ) by norm_num, show 1+2*(3506985203128599/25000000000000000000 : ℝ)=(12503506985203128599/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16672089447615893/50000000000000000000 : ℝ)+(3506985203128599/25000000000000000000 : ℝ) ≤ ((5376216026189505589/5378000000000000000 : ℝ)+(473010338039/268900000000000 : ℝ)*((14071/100000 : ℝ)+(5691/50000 : ℝ)))^(8361/2048 : ℝ) := by
    rw [show (5376216026189505589/5378000000000000000 : ℝ)+(473010338039/268900000000000 : ℝ)*((14071/100000 : ℝ)+(5691/50000 : ℝ))=(2500290039334477/2500000000000000 : ℝ) by norm_num, show 1+(16672089447615893/50000000000000000000 : ℝ)+(3506985203128599/25000000000000000000 : ℝ)=(50023686059853873091/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16672089447615893/50000000000000000000 : ℝ) ≤ ((5376216026189505589/5378000000000000000 : ℝ)+2*(473010338039/268900000000000 : ℝ)*(14071/100000 : ℝ))^(8361/2048 : ℝ) := by
    rw [show (5376216026189505589/5378000000000000000 : ℝ)+2*(473010338039/268900000000000 : ℝ)*(14071/100000 : ℝ)=(10001633167675947/10000000000000000 : ℝ) by norm_num, show 1+2*(16672089447615893/50000000000000000000 : ℝ)=(25016672089447615893/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5376216026189505589/5378000000000000000 : ℝ)*(X 1 0+X 2 0)+(473010338039/268900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8361/2048 : ℝ)) (lo := (5691/50000 : ℝ)) (hi := (14071/100000 : ℝ)) (c := (5376216026189505589/5378000000000000000 : ℝ)) (alpha := (473010338039/268900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5376216026189505589/5378000000000000000 : ℝ)*(X 0 1+X 2 1)+(473010338039/268900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8361/2048 : ℝ)) (lo := (5691/50000 : ℝ)) (hi := (14071/100000 : ℝ)) (c := (5376216026189505589/5378000000000000000 : ℝ)) (alpha := (473010338039/268900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5376216026189505589/5378000000000000000 : ℝ)*(X 0 2+X 1 2)+(473010338039/268900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8361/2048 : ℝ)) (lo := (5691/50000 : ℝ)) (hi := (14071/100000 : ℝ)) (c := (5376216026189505589/5378000000000000000 : ℝ)) (alpha := (473010338039/268900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1077019197/5000000000 : ℝ)*X 0 0+(1078511923/2000000000 : ℝ)*X 0 1+(2633075631/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336164221/2500000000 : ℝ)*X 1 0+(-2218148401/10000000000 : ℝ)*X 1 1+(263307563/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344656883/10000000000 : ℝ)*X 2 0+(5266151261/10000000000 : ℝ)*X 2 1+(-2218148401/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4360882497/10000000000 : ℝ)*X 0 0+(4236284831/10000000000 : ℝ)*X 0 1+(4489103517/10000000000 : ℝ)*X 0 2+(4360882497/10000000000 : ℝ)*X 1 0+(4236284831/10000000000 : ℝ)*X 1 1+(4489103517/10000000000 : ℝ)*X 1 2+(4360882497/10000000000 : ℝ)*X 2 0+(4236284831/10000000000 : ℝ)*X 2 1+(4489103517/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-86161741/400000000 : ℝ)*X 0 0+(1316617231/2500000000 : ℝ)*X 0 1+(5392240571/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656283527/5000000000 : ℝ)*X 1 0+(-1046029747/5000000000 : ℝ)*X 1 1+(674030067/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656283647/5000000000 : ℝ)*X 2 0+(2696120197/5000000000 : ℝ)*X 2 1+(-1046029681/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4360892219/10000000000 : ℝ)*X 0 0+(2244233843/5000000000 : ℝ)*X 0 1+(2118461443/5000000000 : ℝ)*X 0 2+(4360892219/10000000000 : ℝ)*X 1 0+(2244233843/5000000000 : ℝ)*X 1 1+(2118461443/5000000000 : ℝ)*X 1 2+(4360892219/10000000000 : ℝ)*X 2 0+(2244233843/5000000000 : ℝ)*X 2 1+(2118461443/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (297652102712052938735625081/26890000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (217349853/10000000000000 : ℝ)*(base19) + (505596489/25000000000000 : ℝ)*(base23) + (79973387/100000000000000 : ℝ)*(lower2) + (278305861/100000000000000 : ℝ)*(upper3) + (83781783/50000000000000 : ℝ)*(upper5) + (5933228263161143/100000000000000 : ℝ)*(major0) + (5933228263161143/100000000000000 : ℝ)*(major1) + (741653532895143/12500000000000 : ℝ)*(major2) + (7910931892707643/100000000000000 : ℝ)*(sp0) + (3955494561300633/50000000000000 : ℝ)*(sp1) + (98887365921423/1250000000000 : ℝ)*(sp2) + (123607273113337/3125000000000 : ℝ)*(sp3) + (59403392153/100000000000000 : ℝ)*(sp4) + (32121620737/100000000000000 : ℝ)*(sp7) + (24721655382797/625000000000 : ℝ)*(f.failure) + (1977747824024949/25000000000000 : ℝ)*(f.sum) + (21174259649433/26890000000000000000000000000 : ℝ)*base65 + (3033143791494951773/537800000000000000000000000000000 : ℝ)*base68 + (146297084073378273/67225000000000000000000000000000 : ℝ)*base70 + (2128537996332551773/537800000000000000000000000000000 : ℝ)*base72 + (87149471098607/26890000000000000000000000000 : ℝ)*base74 + (1236173007324853273/67225000000000000000000000000000 : ℝ)*base76 + (1930593253866131773/537800000000000000000000000000000 : ℝ)*base78 + (8455862931545131773/537800000000000000000000000000000 : ℝ)*base80 + (19277081679427/13445000000000000000000000000 : ℝ)*base81 + (355051/62500000000000000000 : ℝ)*base89 + (355051/62500000000000000000 : ℝ)*base91 + (269949/62500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (317153258692281261406630629/67225000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (238972279/50000000000000 : ℝ)*(base19) + (156998069/12500000000000 : ℝ)*(base23) + (90167177/50000000000000 : ℝ)*(upper2) + (72783913/50000000000000 : ℝ)*(upper3) + (319961/97656250000 : ℝ)*(upper5) + (2981589419750787/50000000000000 : ℝ)*(major0) + (2981589419750787/50000000000000 : ℝ)*(major1) + (2981589419750787/50000000000000 : ℝ)*(major2) + (742795747/20000000000000 : ℝ)*(sp1) + (65856297/390625000000 : ℝ)*(sp2) + (1987731428457469/25000000000000 : ℝ)*(sp4) + (993865190238323/12500000000000 : ℝ)*(sp5) + (7950907598633293/100000000000000 : ℝ)*(sp6) + (1987715903956839/50000000000000 : ℝ)*(sp7) + (1987715903956839/50000000000000 : ℝ)*(f.failure) + (1987731428457469/25000000000000 : ℝ)*(f.sum) + (6306140059599/3361250000000000000000000000 : ℝ)*base65 + (2409573553997291457/268900000000000000000000000000000 : ℝ)*base68 + (542372657928091457/268900000000000000000000000000000 : ℝ)*base70 + (1030696952631308543/268900000000000000000000000000000 : ℝ)*base71 + (42846527867121/13445000000000000000000000000 : ℝ)*base73 + (4851346167967291457/268900000000000000000000000000000 : ℝ)*base76 + (1605891781174491457/268900000000000000000000000000000 : ℝ)*base78 + (3623451713890291457/268900000000000000000000000000000 : ℝ)*base80 + (12161528881617/1680625000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (51795063/5000000000000000000000 : ℝ)*base90 + (51795063/5000000000000000000000 : ℝ)*base92 + (51795063/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1169_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150000783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14071/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5691/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11387/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1169_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1169_s8_0 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2154045483/10000000000 : ℝ)*x 0 + (215700167/400000000 : ℝ)*x 1 + (210648073/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2154045483/10000000000 : ℝ)^4181 ≤ (654576451727/5000000000000 : ℝ)^3157 := by
    have hnat : (2154045483 : ℕ)^4181*5000000000000^3157 ≤ 654576451727^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154045483 10000000000 654576451727 5000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215700167/400000000 : ℝ)^4181 ≤ (4413614902727/10000000000000 : ℝ)^3157 := by
    have hnat : (215700167 : ℕ)^4181*10000000000000^3157 ≤ 4413614902727^3157*400000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215700167 400000000 4413614902727 10000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210648073/400000000 : ℝ)^4181 ≤ (21386160961047/50000000000000 : ℝ)^3157 := by
    have hnat : (210648073 : ℕ)^4181*50000000000000^3157 ≤ 21386160961047^3157*400000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210648073 400000000 21386160961047 50000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2154045483/10000000000 : ℝ), (215700167/400000000 : ℝ), (210648073/400000000 : ℝ)] ![(654576451727/5000000000000 : ℝ), (4413614902727/10000000000000 : ℝ), (21386160961047/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2154045483/10000000000 : ℝ)|^4181 ≤ (654576451727/5000000000000 : ℝ)^3157
        have hw : |(-2154045483/10000000000 : ℝ)|=(2154045483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215700167/400000000 : ℝ)|^4181 ≤ (4413614902727/10000000000000 : ℝ)^3157
        have hw : |(215700167/400000000 : ℝ)|=(215700167/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210648073/400000000 : ℝ)|^4181 ≤ (21386160961047/50000000000000 : ℝ)^3157
        have hw : |(210648073/400000000 : ℝ)|=(210648073/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s8_1 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672321127/5000000000 : ℝ)*x 0 + (-443620173/2000000000 : ℝ)*x 1 + (5266201871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672321127/5000000000 : ℝ)^4181 ≤ (10904524419483/25000000000000 : ℝ)^3157 := by
    have hnat : (2672321127 : ℕ)^4181*25000000000000^3157 ≤ 10904524419483^3157*5000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672321127 5000000000 10904524419483 25000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (443620173/2000000000 : ℝ)^4181 ≤ (13609579886193/100000000000000 : ℝ)^3157 := by
    have hnat : (443620173 : ℕ)^4181*100000000000000^3157 ≤ 13609579886193^3157*2000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443620173 2000000000 13609579886193 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266201871/10000000000 : ℝ)^4181 ≤ (42772322416893/100000000000000 : ℝ)^3157 := by
    have hnat : (5266201871 : ℕ)^4181*100000000000000^3157 ≤ 42772322416893^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266201871 10000000000 42772322416893 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672321127/5000000000 : ℝ), (-443620173/2000000000 : ℝ), (5266201871/10000000000 : ℝ)] ![(10904524419483/25000000000000 : ℝ), (13609579886193/100000000000000 : ℝ), (42772322416893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672321127/5000000000 : ℝ)|^4181 ≤ (10904524419483/25000000000000 : ℝ)^3157
        have hw : |(2672321127/5000000000 : ℝ)|=(2672321127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-443620173/2000000000 : ℝ)|^4181 ≤ (13609579886193/100000000000000 : ℝ)^3157
        have hw : |(-443620173/2000000000 : ℝ)|=(443620173/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266201871/10000000000 : ℝ)|^4181 ≤ (42772322416893/100000000000000 : ℝ)^3157
        have hw : |(5266201871/10000000000 : ℝ)|=(5266201871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s8_2 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344642189/10000000000 : ℝ)*x 0 + (5266201887/10000000000 : ℝ)*x 1 + (-2218100931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344642189/10000000000 : ℝ)^4181 ≤ (43618096975399/100000000000000 : ℝ)^3157 := by
    have hnat : (5344642189 : ℕ)^4181*100000000000000^3157 ≤ 43618096975399^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344642189 10000000000 43618096975399 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266201887/10000000000 : ℝ)^4181 ≤ (42772322588997/100000000000000 : ℝ)^3157 := by
    have hnat : (5266201887 : ℕ)^4181*100000000000000^3157 ≤ 42772322588997^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266201887 10000000000 42772322588997 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2218100931/10000000000 : ℝ)^4181 ≤ (13609580422499/100000000000000 : ℝ)^3157 := by
    have hnat : (2218100931 : ℕ)^4181*100000000000000^3157 ≤ 13609580422499^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2218100931 10000000000 13609580422499 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344642189/10000000000 : ℝ), (5266201887/10000000000 : ℝ), (-2218100931/10000000000 : ℝ)] ![(43618096975399/100000000000000 : ℝ), (42772322588997/100000000000000 : ℝ), (13609580422499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344642189/10000000000 : ℝ)|^4181 ≤ (43618096975399/100000000000000 : ℝ)^3157
        have hw : |(5344642189/10000000000 : ℝ)|=(5344642189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266201887/10000000000 : ℝ)|^4181 ≤ (42772322588997/100000000000000 : ℝ)^3157
        have hw : |(5266201887/10000000000 : ℝ)|=(5266201887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2218100931/10000000000 : ℝ)|^4181 ≤ (13609580422499/100000000000000 : ℝ)^3157
        have hw : |(-2218100931/10000000000 : ℝ)|=(2218100931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s8_3 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4360885181/10000000000 : ℝ)*x 0 + (2118195259/5000000000 : ℝ)*x 1 + (4488997139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360885181/10000000000 : ℝ)^4181 ≤ (33317131454799/100000000000000 : ℝ)^3157 := by
    have hnat : (4360885181 : ℕ)^4181*100000000000000^3157 ≤ 33317131454799^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360885181 10000000000 33317131454799 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2118195259/5000000000 : ℝ)^4181 ≤ (4007919156469/12500000000000 : ℝ)^3157 := by
    have hnat : (2118195259 : ℕ)^4181*12500000000000^3157 ≤ 4007919156469^3157*5000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118195259 5000000000 4007919156469 12500000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4488997139/10000000000 : ℝ)^4181 ≤ (34619515279783/100000000000000 : ℝ)^3157 := by
    have hnat : (4488997139 : ℕ)^4181*100000000000000^3157 ≤ 34619515279783^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488997139 10000000000 34619515279783 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360885181/10000000000 : ℝ), (2118195259/5000000000 : ℝ), (4488997139/10000000000 : ℝ)] ![(33317131454799/100000000000000 : ℝ), (4007919156469/12500000000000 : ℝ), (34619515279783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360885181/10000000000 : ℝ)|^4181 ≤ (33317131454799/100000000000000 : ℝ)^3157
        have hw : |(4360885181/10000000000 : ℝ)|=(4360885181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2118195259/5000000000 : ℝ)|^4181 ≤ (4007919156469/12500000000000 : ℝ)^3157
        have hw : |(2118195259/5000000000 : ℝ)|=(2118195259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4488997139/10000000000 : ℝ)|^4181 ≤ (34619515279783/100000000000000 : ℝ)^3157
        have hw : |(4488997139/10000000000 : ℝ)|=(4488997139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s8_4 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2154050267/10000000000 : ℝ)*x 0 + (164578729/312500000 : ℝ)*x 1 + (1078437109/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2154050267/10000000000 : ℝ)^4181 ≤ (409111485653/3125000000000 : ℝ)^3157 := by
    have hnat : (2154050267 : ℕ)^4181*3125000000000^3157 ≤ 409111485653^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154050267 10000000000 409111485653 3125000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164578729/312500000 : ℝ)^4181 ≤ (4277573717597/10000000000000 : ℝ)^3157 := by
    have hnat : (164578729 : ℕ)^4181*10000000000000^3157 ≤ 4277573717597^3157*312500000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164578729 312500000 4277573717597 10000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078437109/2000000000 : ℝ)^4181 ≤ (44132695268229/100000000000000 : ℝ)^3157 := by
    have hnat : (1078437109 : ℕ)^4181*100000000000000^3157 ≤ 44132695268229^3157*2000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078437109 2000000000 44132695268229 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2154050267/10000000000 : ℝ), (164578729/312500000 : ℝ), (1078437109/2000000000 : ℝ)] ![(409111485653/3125000000000 : ℝ), (4277573717597/10000000000000 : ℝ), (44132695268229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2154050267/10000000000 : ℝ)|^4181 ≤ (409111485653/3125000000000 : ℝ)^3157
        have hw : |(-2154050267/10000000000 : ℝ)|=(2154050267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164578729/312500000 : ℝ)|^4181 ≤ (4277573717597/10000000000000 : ℝ)^3157
        have hw : |(164578729/312500000 : ℝ)|=(164578729/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078437109/2000000000 : ℝ)|^4181 ≤ (44132695268229/100000000000000 : ℝ)^3157
        have hw : |(1078437109/2000000000 : ℝ)|=(1078437109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s8_5 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (664072453/1250000000 : ℝ)*x 0 + (-83684689/400000000 : ℝ)*x 1 + (5392185561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664072453/1250000000 : ℝ)^4181 ≤ (338061685449/781250000000 : ℝ)^3157 := by
    have hnat : (664072453 : ℕ)^4181*781250000000^3157 ≤ 338061685449^3157*1250000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664072453 1250000000 338061685449 781250000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (83684689/400000000 : ℝ)^4181 ≤ (12595408803983/100000000000000 : ℝ)^3157 := by
    have hnat : (83684689 : ℕ)^4181*100000000000000^3157 ≤ 12595408803983^3157*400000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83684689 400000000 12595408803983 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392185561/10000000000 : ℝ)^4181 ≤ (22066347720829/50000000000000 : ℝ)^3157 := by
    have hnat : (5392185561 : ℕ)^4181*50000000000000^3157 ≤ 22066347720829^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392185561 10000000000 22066347720829 50000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664072453/1250000000 : ℝ), (-83684689/400000000 : ℝ), (5392185561/10000000000 : ℝ)] ![(338061685449/781250000000 : ℝ), (12595408803983/100000000000000 : ℝ), (22066347720829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664072453/1250000000 : ℝ)|^4181 ≤ (338061685449/781250000000 : ℝ)^3157
        have hw : |(664072453/1250000000 : ℝ)|=(664072453/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-83684689/400000000 : ℝ)|^4181 ≤ (12595408803983/100000000000000 : ℝ)^3157
        have hw : |(-83684689/400000000 : ℝ)|=(83684689/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392185561/10000000000 : ℝ)|^4181 ≤ (22066347720829/50000000000000 : ℝ)^3157
        have hw : |(5392185561/10000000000 : ℝ)|=(5392185561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s8_6 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1328144909/2500000000 : ℝ)*x 0 + (107843711/200000000 : ℝ)*x 1 + (-261514653/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328144909/2500000000 : ℝ)^4181 ≤ (43271895866917/100000000000000 : ℝ)^3157 := by
    have hnat : (1328144909 : ℕ)^4181*100000000000000^3157 ≤ 43271895866917^3157*2500000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328144909 2500000000 43271895866917 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107843711/200000000 : ℝ)^4181 ≤ (1765307812897/4000000000000 : ℝ)^3157 := by
    have hnat : (107843711 : ℕ)^4181*4000000000000^3157 ≤ 1765307812897^3157*200000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107843711 200000000 1765307812897 4000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (261514653/1250000000 : ℝ)^4181 ≤ (1259540879601/10000000000000 : ℝ)^3157 := by
    have hnat : (261514653 : ℕ)^4181*10000000000000^3157 ≤ 1259540879601^3157*1250000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261514653 1250000000 1259540879601 10000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328144909/2500000000 : ℝ), (107843711/200000000 : ℝ), (-261514653/1250000000 : ℝ)] ![(43271895866917/100000000000000 : ℝ), (1765307812897/4000000000000 : ℝ), (1259540879601/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328144909/2500000000 : ℝ)|^4181 ≤ (43271895866917/100000000000000 : ℝ)^3157
        have hw : |(1328144909/2500000000 : ℝ)|=(1328144909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(107843711/200000000 : ℝ)|^4181 ≤ (1765307812897/4000000000000 : ℝ)^3157
        have hw : |(107843711/200000000 : ℝ)|=(107843711/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-261514653/1250000000 : ℝ)|^4181 ≤ (1259540879601/10000000000000 : ℝ)^3157
        have hw : |(-261514653/1250000000 : ℝ)|=(261514653/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s8_7 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (545111851/1250000000 : ℝ)*x 0 + (2244181097/5000000000 : ℝ)*x 1 + (847405551/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545111851/1250000000 : ℝ)^4181 ≤ (16658614430843/50000000000000 : ℝ)^3157 := by
    have hnat : (545111851 : ℕ)^4181*50000000000000^3157 ≤ 16658614430843^3157*1250000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545111851 1250000000 16658614430843 50000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2244181097/5000000000 : ℝ)^4181 ≤ (34613030378273/100000000000000 : ℝ)^3157 := by
    have hnat : (2244181097 : ℕ)^4181*100000000000000^3157 ≤ 34613030378273^3157*5000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244181097 5000000000 34613030378273 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (847405551/2000000000 : ℝ)^4181 ≤ (32069740740037/100000000000000 : ℝ)^3157 := by
    have hnat : (847405551 : ℕ)^4181*100000000000000^3157 ≤ 32069740740037^3157*2000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847405551 2000000000 32069740740037 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(545111851/1250000000 : ℝ), (2244181097/5000000000 : ℝ), (847405551/2000000000 : ℝ)] ![(16658614430843/50000000000000 : ℝ), (34613030378273/100000000000000 : ℝ), (32069740740037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(545111851/1250000000 : ℝ)|^4181 ≤ (16658614430843/50000000000000 : ℝ)^3157
        have hw : |(545111851/1250000000 : ℝ)|=(545111851/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2244181097/5000000000 : ℝ)|^4181 ≤ (34613030378273/100000000000000 : ℝ)^3157
        have hw : |(2244181097/5000000000 : ℝ)|=(2244181097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(847405551/2000000000 : ℝ)|^4181 ≤ (32069740740037/100000000000000 : ℝ)^3157
        have hw : |(847405551/2000000000 : ℝ)|=(847405551/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1169_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150000783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11387/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11389/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (879/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2813/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11387/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2813/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11387/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2813/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11387/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2813/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11387/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2813/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11387/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2813/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11387/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11387/100000 : ℝ) ^ (8361/2048 : ℝ) ≤ (2810623141326141/20000000000000000000 : ℝ) := by
    have hpowers : (11387/100000 : ℝ)^8361 ≤ (2810623141326141/20000000000000000000 : ℝ)^2048 := by
      have hnat : (11387 : ℕ)^8361*20000000000000000000^2048 ≤ 2810623141326141^2048*100000^8361 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11387 100000 2810623141326141 20000000000000000000 8361 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11387/100000 : ℝ)) (X := (2810623141326141/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2813/20000 : ℝ) ^ (8361/2048 : ℝ) ≤ (16643085363264511/50000000000000000000 : ℝ) := by
    have hpowers : (2813/20000 : ℝ)^8361 ≤ (16643085363264511/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2813 : ℕ)^8361*50000000000000000000^2048 ≤ 16643085363264511^2048*20000^8361 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2813 20000 16643085363264511 50000000000000000000 8361 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2813/20000 : ℝ)) (X := (16643085363264511/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002810623141326141/10000000000000000000 : ℝ) ≤ (5000344190020137/5000000000000000 : ℝ) ^ (8361/2048 : ℝ) := by
    have hpowers : (10002810623141326141/10000000000000000000 : ℝ)^2048 ≤ (5000344190020137/5000000000000000 : ℝ)^8361 := by
      have hnat : (10002810623141326141 : ℕ)^2048*5000000000000000^8361 ≤ 5000344190020137^8361*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002810623141326141 10000000000000000000 5000344190020137 5000000000000000 2048 8361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000344190020137/5000000000000000 : ℝ)) (X := (10002810623141326141/10000000000000000000 : ℝ)) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047339286433159727/100000000000000000000 : ℝ) ≤ (80009274827079/80000000000000 : ℝ) ^ (8361/2048 : ℝ) := by
    have hpowers : (100047339286433159727/100000000000000000000 : ℝ)^2048 ≤ (80009274827079/80000000000000 : ℝ)^8361 := by
      have hnat : (100047339286433159727 : ℕ)^2048*80000000000000^8361 ≤ 80009274827079^8361*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047339286433159727 100000000000000000000 80009274827079 80000000000000 2048 8361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80009274827079/80000000000000 : ℝ)) (X := (100047339286433159727/100000000000000000000 : ℝ)) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016643085363264511/25000000000000000000 : ℝ) ≤ (2500407581682369/2500000000000000 : ℝ) ^ (8361/2048 : ℝ) := by
    have hpowers : (25016643085363264511/25000000000000000000 : ℝ)^2048 ≤ (2500407581682369/2500000000000000 : ℝ)^8361 := by
      have hnat : (25016643085363264511 : ℕ)^2048*2500000000000000^8361 ≤ 2500407581682369^8361*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016643085363264511 25000000000000000000 2500407581682369 2500000000000000 2048 8361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500407581682369/2500000000000000 : ℝ)) (X := (25016643085363264511/25000000000000000000 : ℝ)) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2810623141326141/20000000000000000000 : ℝ) ≤ ((13385558767398955299/13390000000000000000 : ℝ)+2*(470973344601/267800000000000 : ℝ)*(11387/100000 : ℝ))^(8361/2048 : ℝ) := by
    rw [show (13385558767398955299/13390000000000000000 : ℝ)+2*(470973344601/267800000000000 : ℝ)*(11387/100000 : ℝ)=(5000344190020137/5000000000000000 : ℝ) by norm_num, show 1+2*(2810623141326141/20000000000000000000 : ℝ)=(10002810623141326141/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16643085363264511/50000000000000000000 : ℝ)+(2810623141326141/20000000000000000000 : ℝ) ≤ ((13385558767398955299/13390000000000000000 : ℝ)+(470973344601/267800000000000 : ℝ)*((2813/20000 : ℝ)+(11387/100000 : ℝ)))^(8361/2048 : ℝ) := by
    rw [show (13385558767398955299/13390000000000000000 : ℝ)+(470973344601/267800000000000 : ℝ)*((2813/20000 : ℝ)+(11387/100000 : ℝ))=(80009274827079/80000000000000 : ℝ) by norm_num, show 1+(16643085363264511/50000000000000000000 : ℝ)+(2810623141326141/20000000000000000000 : ℝ)=(100047339286433159727/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16643085363264511/50000000000000000000 : ℝ) ≤ ((13385558767398955299/13390000000000000000 : ℝ)+2*(470973344601/267800000000000 : ℝ)*(2813/20000 : ℝ))^(8361/2048 : ℝ) := by
    rw [show (13385558767398955299/13390000000000000000 : ℝ)+2*(470973344601/267800000000000 : ℝ)*(2813/20000 : ℝ)=(2500407581682369/2500000000000000 : ℝ) by norm_num, show 1+2*(16643085363264511/50000000000000000000 : ℝ)=(25016643085363264511/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13385558767398955299/13390000000000000000 : ℝ)*(X 1 0+X 2 0)+(470973344601/267800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8361/2048 : ℝ)) (lo := (11387/100000 : ℝ)) (hi := (2813/20000 : ℝ)) (c := (13385558767398955299/13390000000000000000 : ℝ)) (alpha := (470973344601/267800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13385558767398955299/13390000000000000000 : ℝ)*(X 0 1+X 2 1)+(470973344601/267800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8361/2048 : ℝ)) (lo := (11387/100000 : ℝ)) (hi := (2813/20000 : ℝ)) (c := (13385558767398955299/13390000000000000000 : ℝ)) (alpha := (470973344601/267800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13385558767398955299/13390000000000000000 : ℝ)*(X 0 2+X 1 2)+(470973344601/267800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8361/2048 : ℝ)) (lo := (11387/100000 : ℝ)) (hi := (2813/20000 : ℝ)) (c := (13385558767398955299/13390000000000000000 : ℝ)) (alpha := (470973344601/267800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2154045483/10000000000 : ℝ)*X 0 0+(215700167/400000000 : ℝ)*X 0 1+(210648073/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672321127/5000000000 : ℝ)*X 1 0+(-443620173/2000000000 : ℝ)*X 1 1+(5266201871/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344642189/10000000000 : ℝ)*X 2 0+(5266201887/10000000000 : ℝ)*X 2 1+(-2218100931/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4360885181/10000000000 : ℝ)*X 0 0+(2118195259/5000000000 : ℝ)*X 0 1+(4488997139/10000000000 : ℝ)*X 0 2+(4360885181/10000000000 : ℝ)*X 1 0+(2118195259/5000000000 : ℝ)*X 1 1+(4488997139/10000000000 : ℝ)*X 1 2+(4360885181/10000000000 : ℝ)*X 2 0+(2118195259/5000000000 : ℝ)*X 2 1+(4488997139/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2154050267/10000000000 : ℝ)*X 0 0+(164578729/312500000 : ℝ)*X 0 1+(1078437109/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((664072453/1250000000 : ℝ)*X 1 0+(-83684689/400000000 : ℝ)*X 1 1+(5392185561/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328144909/2500000000 : ℝ)*X 2 0+(107843711/200000000 : ℝ)*X 2 1+(-261514653/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((545111851/1250000000 : ℝ)*X 0 0+(2244181097/5000000000 : ℝ)*X 0 1+(847405551/2000000000 : ℝ)*X 0 2+(545111851/1250000000 : ℝ)*X 1 0+(2244181097/5000000000 : ℝ)*X 1 1+(847405551/2000000000 : ℝ)*X 1 2+(545111851/1250000000 : ℝ)*X 2 0+(2244181097/5000000000 : ℝ)*X 2 1+(847405551/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19645285987502001669694539/8368750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (270696073/50000000000000 : ℝ)*(base19) + (91332557/20000000000000 : ℝ)*(base23) + (888419/12500000000000 : ℝ)*(upper2) + (7226379/6250000000000 : ℝ)*(upper3) + (928129/100000000000000 : ℝ)*(upper4) + (5938142619905653/100000000000000 : ℝ)*(major0) + (5938142619905653/100000000000000 : ℝ)*(major1) + (2969071309952827/50000000000000 : ℝ)*(major2) + (7917530023584759/100000000000000 : ℝ)*(sp0) + (3958771769097617/50000000000000 : ℝ)*(sp1) + (1583508724584919/20000000000000 : ℝ)*(sp2) + (3166985477643/80000000000 : ℝ)*(sp3) + (14056002621/100000000000000 : ℝ)*(sp4) + (2308730393/25000000000000 : ℝ)*(sp7) + (1979370540987661/50000000000000 : ℝ)*(f.failure) + (395877203979369/5000000000000 : ℝ)*(f.sum) + (18709911484347/26780000000000000000000000000 : ℝ)*base65 + (17217880747711894753/1339000000000000000000000000000000 : ℝ)*base68 + (14841272579726994727/669500000000000000000000000000000 : ℝ)*base70 + (12269037682870894753/1339000000000000000000000000000000 : ℝ)*base72 + (29059731269733/26780000000000000000000000000 : ℝ)*base74 + (26174424097609994727/669500000000000000000000000000000 : ℝ)*base76 + (35678115594541944753/1339000000000000000000000000000000 : ℝ)*base78 + (56552706289369944753/1339000000000000000000000000000000 : ℝ)*base80 + (38162102660103/13390000000000000000000000000 : ℝ)*base81 + (93338563/5000000000000000000000 : ℝ)*base89 + (93338563/5000000000000000000000 : ℝ)*base91 + (43338563/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (41790806566666626674427/6695000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1114452917/100000000000000 : ℝ)*(base19) + (307956039/25000000000000 : ℝ)*(base23) + (3157997/800000000000 : ℝ)*(lower1) + (65750843/50000000000000 : ℝ)*(upper3) + (43245519/100000000000000 : ℝ)*(lower4) + (3768657/3125000000000 : ℝ)*(upper5) + (2984075511256093/50000000000000 : ℝ)*(major0) + (2984075511256093/50000000000000 : ℝ)*(major1) + (2984075511256093/50000000000000 : ℝ)*(major2) + (1490806751/50000000000000 : ℝ)*(sp2) + (7957555257670307/100000000000000 : ℝ)*(sp4) + (7957554143217391/100000000000000 : ℝ)*(sp5) + (7957551044232649/100000000000000 : ℝ)*(sp6) + (1989373289642157/50000000000000 : ℝ)*(sp7) + (1989373289642157/50000000000000 : ℝ)*(f.failure) + (7957555257670307/100000000000000 : ℝ)*(f.sum) + (219354193873/1673750000000000000000000000 : ℝ)*base66 + (3184909382090963193/669500000000000000000000000000000 : ℝ)*base68 + (14277104385536807/669500000000000000000000000000000 : ℝ)*base69 + (52227099336328963193/669500000000000000000000000000000 : ℝ)*base72 + (4512767188051/3347500000000000000000000000 : ℝ)*base74 + (14750326260216463193/669500000000000000000000000000000 : ℝ)*base76 + (545615088140036807/669500000000000000000000000000000 : ℝ)*base77 + (10709956197413036807/669500000000000000000000000000000 : ℝ)*base79 + (29415514328847/6695000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (39808931/5000000000000000000000 : ℝ)*base89 + (39808931/5000000000000000000000 : ℝ)*base91 + (39808931/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1169_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150000783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11387/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11389/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (879/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1169_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1169_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150000783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (141/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5677/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11389/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (879/6250 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1169_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1169_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1169_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150000783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (141/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5677/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11389/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (879/6250 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1169_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

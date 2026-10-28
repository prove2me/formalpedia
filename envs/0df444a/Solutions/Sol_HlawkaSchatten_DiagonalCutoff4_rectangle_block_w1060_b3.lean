-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1060_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:02:55.231078+00:00
-- url     : https://prove2.me/submissions/1e8fa3b2-652c-42c6-8f22-a665b590aa0d

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
theorem support_rectangle_w1060_s9_0 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2206729011/10000000000 : ℝ)*x 0 + (5394434757/10000000000 : ℝ)*x 1 + (329022933/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2206729011/10000000000 : ℝ)^8253 ≤ (1675171101989/12500000000000 : ℝ)^6205 := by
    have hnat : (2206729011 : ℕ)^8253*12500000000000^6205 ≤ 1675171101989^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2206729011 10000000000 1675171101989 12500000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394434757/10000000000 : ℝ)^8253 ≤ (11000514440847/25000000000000 : ℝ)^6205 := by
    have hnat : (5394434757 : ℕ)^8253*25000000000000^6205 ≤ 11000514440847^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394434757 10000000000 11000514440847 25000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329022933/625000000 : ℝ)^8253 ≤ (166392864851/390625000000 : ℝ)^6205 := by
    have hnat : (329022933 : ℕ)^8253*390625000000^6205 ≤ 166392864851^6205*625000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329022933 625000000 166392864851 390625000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2206729011/10000000000 : ℝ), (5394434757/10000000000 : ℝ), (329022933/625000000 : ℝ)] ![(1675171101989/12500000000000 : ℝ), (11000514440847/25000000000000 : ℝ), (166392864851/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2206729011/10000000000 : ℝ)|^8253 ≤ (1675171101989/12500000000000 : ℝ)^6205
        have hw : |(-2206729011/10000000000 : ℝ)|=(2206729011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394434757/10000000000 : ℝ)|^8253 ≤ (11000514440847/25000000000000 : ℝ)^6205
        have hw : |(5394434757/10000000000 : ℝ)|=(5394434757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329022933/625000000 : ℝ)|^8253 ≤ (166392864851/390625000000 : ℝ)^6205
        have hw : |(329022933/625000000 : ℝ)|=(329022933/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s9_1 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344985581/10000000000 : ℝ)*x 0 + (-1136361521/5000000000 : ℝ)*x 1 + (1316091687/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344985581/10000000000 : ℝ)^8253 ≤ (10866596940543/25000000000000 : ℝ)^6205 := by
    have hnat : (5344985581 : ℕ)^8253*25000000000000^6205 ≤ 10866596940543^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344985581 10000000000 10866596940543 25000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1136361521/5000000000 : ℝ)^8253 ≤ (1742130095589/12500000000000 : ℝ)^6205 := by
    have hnat : (1136361521 : ℕ)^8253*12500000000000^6205 ≤ 1742130095589^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136361521 5000000000 1742130095589 12500000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316091687/2500000000 : ℝ)^8253 ≤ (42596571464671/100000000000000 : ℝ)^6205 := by
    have hnat : (1316091687 : ℕ)^8253*100000000000000^6205 ≤ 42596571464671^6205*2500000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316091687 2500000000 42596571464671 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344985581/10000000000 : ℝ), (-1136361521/5000000000 : ℝ), (1316091687/2500000000 : ℝ)] ![(10866596940543/25000000000000 : ℝ), (1742130095589/12500000000000 : ℝ), (42596571464671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344985581/10000000000 : ℝ)|^8253 ≤ (10866596940543/25000000000000 : ℝ)^6205
        have hw : |(5344985581/10000000000 : ℝ)|=(5344985581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1136361521/5000000000 : ℝ)|^8253 ≤ (1742130095589/12500000000000 : ℝ)^6205
        have hw : |(-1136361521/5000000000 : ℝ)|=(1136361521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316091687/2500000000 : ℝ)|^8253 ≤ (42596571464671/100000000000000 : ℝ)^6205
        have hw : |(1316091687/2500000000 : ℝ)|=(1316091687/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s9_2 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344985567/10000000000 : ℝ)*x 0 + (5264366819/10000000000 : ℝ)*x 1 + (-2272722967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344985567/10000000000 : ℝ)^8253 ≤ (5433298451343/12500000000000 : ℝ)^6205 := by
    have hnat : (5344985567 : ℕ)^8253*12500000000000^6205 ≤ 5433298451343^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344985567 10000000000 5433298451343 12500000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264366819/10000000000 : ℝ)^8253 ≤ (42596572228783/100000000000000 : ℝ)^6205 := by
    have hnat : (5264366819 : ℕ)^8253*100000000000000^6205 ≤ 42596572228783^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264366819 10000000000 42596572228783 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2272722967/10000000000 : ℝ)^8253 ≤ (3484260038247/25000000000000 : ℝ)^6205 := by
    have hnat : (2272722967 : ℕ)^8253*25000000000000^6205 ≤ 3484260038247^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2272722967 10000000000 3484260038247 25000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344985567/10000000000 : ℝ), (5264366819/10000000000 : ℝ), (-2272722967/10000000000 : ℝ)] ![(5433298451343/12500000000000 : ℝ), (42596572228783/100000000000000 : ℝ), (3484260038247/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344985567/10000000000 : ℝ)|^8253 ≤ (5433298451343/12500000000000 : ℝ)^6205
        have hw : |(5344985567/10000000000 : ℝ)|=(5344985567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264366819/10000000000 : ℝ)|^8253 ≤ (42596572228783/100000000000000 : ℝ)^6205
        have hw : |(5264366819/10000000000 : ℝ)|=(5264366819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2272722967/10000000000 : ℝ)|^8253 ≤ (3484260038247/25000000000000 : ℝ)^6205
        have hw : |(-2272722967/10000000000 : ℝ)|=(2272722967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s9_3 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (547044623/1250000000 : ℝ)*x 0 + (850185957/2000000000 : ℝ)*x 1 + (180221671/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (547044623/1250000000 : ℝ)^8253 ≤ (33316525347877/100000000000000 : ℝ)^6205 := by
    have hnat : (547044623 : ℕ)^8253*100000000000000^6205 ≤ 33316525347877^6205*1250000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547044623 1250000000 33316525347877 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (850185957/2000000000 : ℝ)^8253 ≤ (16026278204383/50000000000000 : ℝ)^6205 := by
    have hnat : (850185957 : ℕ)^8253*50000000000000^6205 ≤ 16026278204383^6205*2000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850185957 2000000000 16026278204383 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (180221671/400000000 : ℝ)^8253 ≤ (4328864778219/12500000000000 : ℝ)^6205 := by
    have hnat : (180221671 : ℕ)^8253*12500000000000^6205 ≤ 4328864778219^6205*400000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180221671 400000000 4328864778219 12500000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(547044623/1250000000 : ℝ), (850185957/2000000000 : ℝ), (180221671/400000000 : ℝ)] ![(33316525347877/100000000000000 : ℝ), (16026278204383/50000000000000 : ℝ), (4328864778219/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(547044623/1250000000 : ℝ)|^8253 ≤ (33316525347877/100000000000000 : ℝ)^6205
        have hw : |(547044623/1250000000 : ℝ)|=(547044623/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(850185957/2000000000 : ℝ)|^8253 ≤ (16026278204383/50000000000000 : ℝ)^6205
        have hw : |(850185957/2000000000 : ℝ)|=(850185957/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(180221671/400000000 : ℝ)|^8253 ≤ (4328864778219/12500000000000 : ℝ)^6205
        have hw : |(180221671/400000000 : ℝ)|=(180221671/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s9_4 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (265611989/500000000 : ℝ)*x 0 + (-2142981749/10000000000 : ℝ)*x 1 + (5394107897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265611989/500000000 : ℝ)^8253 ≤ (43112559290481/100000000000000 : ℝ)^6205 := by
    have hnat : (265611989 : ℕ)^8253*100000000000000^6205 ≤ 43112559290481^6205*500000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265611989 500000000 43112559290481 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2142981749/10000000000 : ℝ)^8253 ≤ (3222232266339/25000000000000 : ℝ)^6205 := by
    have hnat : (2142981749 : ℕ)^8253*25000000000000^6205 ≤ 3222232266339^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142981749 10000000000 3222232266339 25000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394107897/10000000000 : ℝ)^8253 ≤ (879970232687/2000000000000 : ℝ)^6205 := by
    have hnat : (5394107897 : ℕ)^8253*2000000000000^6205 ≤ 879970232687^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394107897 10000000000 879970232687 2000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265611989/500000000 : ℝ), (-2142981749/10000000000 : ℝ), (5394107897/10000000000 : ℝ)] ![(43112559290481/100000000000000 : ℝ), (3222232266339/25000000000000 : ℝ), (879970232687/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265611989/500000000 : ℝ)|^8253 ≤ (43112559290481/100000000000000 : ℝ)^6205
        have hw : |(265611989/500000000 : ℝ)|=(265611989/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2142981749/10000000000 : ℝ)|^8253 ≤ (3222232266339/25000000000000 : ℝ)^6205
        have hw : |(-2142981749/10000000000 : ℝ)|=(2142981749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394107897/10000000000 : ℝ)|^8253 ≤ (879970232687/2000000000000 : ℝ)^6205
        have hw : |(5394107897/10000000000 : ℝ)|=(5394107897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s9_5 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656119849/5000000000 : ℝ)*x 0 + (5394108039/10000000000 : ℝ)*x 1 + (-1071490833/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656119849/5000000000 : ℝ)^8253 ≤ (8622511681069/20000000000000 : ℝ)^6205 := by
    have hnat : (2656119849 : ℕ)^8253*20000000000000^6205 ≤ 8622511681069^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656119849 5000000000 8622511681069 20000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394108039/10000000000 : ℝ)^8253 ≤ (5499814146863/12500000000000 : ℝ)^6205 := by
    have hnat : (5394108039 : ℕ)^8253*12500000000000^6205 ≤ 5499814146863^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394108039 10000000000 5499814146863 12500000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1071490833/5000000000 : ℝ)^8253 ≤ (12888928401389/100000000000000 : ℝ)^6205 := by
    have hnat : (1071490833 : ℕ)^8253*100000000000000^6205 ≤ 12888928401389^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071490833 5000000000 12888928401389 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656119849/5000000000 : ℝ), (5394108039/10000000000 : ℝ), (-1071490833/5000000000 : ℝ)] ![(8622511681069/20000000000000 : ℝ), (5499814146863/12500000000000 : ℝ), (12888928401389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656119849/5000000000 : ℝ)|^8253 ≤ (8622511681069/20000000000000 : ℝ)^6205
        have hw : |(2656119849/5000000000 : ℝ)|=(2656119849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394108039/10000000000 : ℝ)|^8253 ≤ (5499814146863/12500000000000 : ℝ)^6205
        have hw : |(5394108039/10000000000 : ℝ)|=(5394108039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1071490833/5000000000 : ℝ)|^8253 ≤ (12888928401389/100000000000000 : ℝ)^6205
        have hw : |(-1071490833/5000000000 : ℝ)|=(1071490833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s9_6 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4376367039/10000000000 : ℝ)*x 0 + (4504904241/10000000000 : ℝ)*x 1 + (850313899/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4376367039/10000000000 : ℝ)^8253 ≤ (6663325431989/20000000000000 : ℝ)^6205 := by
    have hnat : (4376367039 : ℕ)^8253*20000000000000^6205 ≤ 6663325431989^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4376367039 10000000000 6663325431989 20000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4504904241/10000000000 : ℝ)^8253 ≤ (1731220036877/5000000000000 : ℝ)^6205 := by
    have hnat : (4504904241 : ℕ)^8253*5000000000000^6205 ≤ 1731220036877^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504904241 10000000000 1731220036877 5000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (850313899/2000000000 : ℝ)^8253 ≤ (3205897208923/10000000000000 : ℝ)^6205 := by
    have hnat : (850313899 : ℕ)^8253*10000000000000^6205 ≤ 3205897208923^6205*2000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850313899 2000000000 3205897208923 10000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4376367039/10000000000 : ℝ), (4504904241/10000000000 : ℝ), (850313899/2000000000 : ℝ)] ![(6663325431989/20000000000000 : ℝ), (1731220036877/5000000000000 : ℝ), (3205897208923/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4376367039/10000000000 : ℝ)|^8253 ≤ (6663325431989/20000000000000 : ℝ)^6205
        have hw : |(4376367039/10000000000 : ℝ)|=(4376367039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4504904241/10000000000 : ℝ)|^8253 ≤ (1731220036877/5000000000000 : ℝ)^6205
        have hw : |(4504904241/10000000000 : ℝ)|=(4504904241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(850313899/2000000000 : ℝ)|^8253 ≤ (3205897208923/10000000000000 : ℝ)^6205
        have hw : |(850313899/2000000000 : ℝ)|=(850313899/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1060_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147876331/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13999/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11243/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2811/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13999/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13999/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11243/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13999/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11243/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13999/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11243/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13999/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11243/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13999/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11243/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13999/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11243/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11243/100000 : ℝ) ^ (2063/512 : ℝ) ≤ (2997454870341951/20000000000000000000 : ℝ) := by
    have hpowers : (11243/100000 : ℝ)^2063 ≤ (2997454870341951/20000000000000000000 : ℝ)^512 := by
      have hnat : (11243 : ℕ)^2063*20000000000000000000^512 ≤ 2997454870341951^512*100000^2063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11243 100000 2997454870341951 20000000000000000000 2063 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11243/100000 : ℝ)) (X := (2997454870341951/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hpowhi : (13999/100000 : ℝ) ^ (2063/512 : ℝ) ≤ (18127644238686597/50000000000000000000 : ℝ) := by
    have hpowers : (13999/100000 : ℝ)^2063 ≤ (18127644238686597/50000000000000000000 : ℝ)^512 := by
      have hnat : (13999 : ℕ)^2063*50000000000000000000^512 ≤ 18127644238686597^512*100000^2063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13999 100000 18127644238686597 50000000000000000000 2063 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13999/100000 : ℝ)) (X := (18127644238686597/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002997454870341951/10000000000000000000 : ℝ) ≤ (5000371915656533/5000000000000000 : ℝ) ^ (2063/512 : ℝ) := by
    have hpowers : (10002997454870341951/10000000000000000000 : ℝ)^512 ≤ (5000371915656533/5000000000000000 : ℝ)^2063 := by
      have hnat : (10002997454870341951 : ℕ)^512*5000000000000000^2063 ≤ 5000371915656533^2063*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002997454870341951 10000000000000000000 5000371915656533 5000000000000000 512 2063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000371915656533/5000000000000000 : ℝ)) (X := (10002997454870341951/10000000000000000000 : ℝ)) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051242562829082949/100000000000000000000 : ℝ) ≤ (10001271504601297/10000000000000000 : ℝ) ^ (2063/512 : ℝ) := by
    have hpowers : (100051242562829082949/100000000000000000000 : ℝ)^512 ≤ (10001271504601297/10000000000000000 : ℝ)^2063 := by
      have hnat : (100051242562829082949 : ℕ)^512*10000000000000000^2063 ≤ 10001271504601297^2063*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051242562829082949 100000000000000000000 10001271504601297 10000000000000000 512 2063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001271504601297/10000000000000000 : ℝ)) (X := (100051242562829082949/100000000000000000000 : ℝ)) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018127644238686597/25000000000000000000 : ℝ) ≤ (1250224897236191/1250000000000000 : ℝ) ^ (2063/512 : ℝ) := by
    have hpowers : (25018127644238686597/25000000000000000000 : ℝ)^512 ≤ (1250224897236191/1250000000000000 : ℝ)^2063 := by
      have hnat : (25018127644238686597 : ℕ)^512*1250000000000000^2063 ≤ 1250224897236191^2063*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018127644238686597 25000000000000000000 1250224897236191 1250000000000000 512 2063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250224897236191/1250000000000000 : ℝ)) (X := (25018127644238686597/25000000000000000000 : ℝ)) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2997454870341951/20000000000000000000 : ℝ) ≤ ((2755018473753964763/2756000000000000000 : ℝ)+2*(527673288231/275600000000000 : ℝ)*(11243/100000 : ℝ))^(2063/512 : ℝ) := by
    rw [show (2755018473753964763/2756000000000000000 : ℝ)+2*(527673288231/275600000000000 : ℝ)*(11243/100000 : ℝ)=(5000371915656533/5000000000000000 : ℝ) by norm_num, show 1+2*(2997454870341951/20000000000000000000 : ℝ)=(10002997454870341951/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18127644238686597/50000000000000000000 : ℝ)+(2997454870341951/20000000000000000000 : ℝ) ≤ ((2755018473753964763/2756000000000000000 : ℝ)+(527673288231/275600000000000 : ℝ)*((13999/100000 : ℝ)+(11243/100000 : ℝ)))^(2063/512 : ℝ) := by
    rw [show (2755018473753964763/2756000000000000000 : ℝ)+(527673288231/275600000000000 : ℝ)*((13999/100000 : ℝ)+(11243/100000 : ℝ))=(10001271504601297/10000000000000000 : ℝ) by norm_num, show 1+(18127644238686597/50000000000000000000 : ℝ)+(2997454870341951/20000000000000000000 : ℝ)=(100051242562829082949/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18127644238686597/50000000000000000000 : ℝ) ≤ ((2755018473753964763/2756000000000000000 : ℝ)+2*(527673288231/275600000000000 : ℝ)*(13999/100000 : ℝ))^(2063/512 : ℝ) := by
    rw [show (2755018473753964763/2756000000000000000 : ℝ)+2*(527673288231/275600000000000 : ℝ)*(13999/100000 : ℝ)=(1250224897236191/1250000000000000 : ℝ) by norm_num, show 1+2*(18127644238686597/50000000000000000000 : ℝ)=(25018127644238686597/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2755018473753964763/2756000000000000000 : ℝ)*(X 1 0+X 2 0)+(527673288231/275600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2063/512 : ℝ)) (lo := (11243/100000 : ℝ)) (hi := (13999/100000 : ℝ)) (c := (2755018473753964763/2756000000000000000 : ℝ)) (alpha := (527673288231/275600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2755018473753964763/2756000000000000000 : ℝ)*(X 0 1+X 2 1)+(527673288231/275600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2063/512 : ℝ)) (lo := (11243/100000 : ℝ)) (hi := (13999/100000 : ℝ)) (c := (2755018473753964763/2756000000000000000 : ℝ)) (alpha := (527673288231/275600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2755018473753964763/2756000000000000000 : ℝ)*(X 0 2+X 1 2)+(527673288231/275600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2063/512 : ℝ)) (lo := (11243/100000 : ℝ)) (hi := (13999/100000 : ℝ)) (c := (2755018473753964763/2756000000000000000 : ℝ)) (alpha := (527673288231/275600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2206729011/10000000000 : ℝ)*X 0 0+(5394434757/10000000000 : ℝ)*X 0 1+(329022933/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344985581/10000000000 : ℝ)*X 1 0+(-1136361521/5000000000 : ℝ)*X 1 1+(1316091687/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344985567/10000000000 : ℝ)*X 2 0+(5264366819/10000000000 : ℝ)*X 2 1+(-2272722967/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((547044623/1250000000 : ℝ)*X 0 0+(850185957/2000000000 : ℝ)*X 0 1+(180221671/400000000 : ℝ)*X 0 2+(547044623/1250000000 : ℝ)*X 1 0+(850185957/2000000000 : ℝ)*X 1 1+(180221671/400000000 : ℝ)*X 1 2+(547044623/1250000000 : ℝ)*X 2 0+(850185957/2000000000 : ℝ)*X 2 1+(180221671/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((265611989/500000000 : ℝ)*X 1 0+(-2142981749/10000000000 : ℝ)*X 1 1+(5394107897/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s9_4 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656119849/5000000000 : ℝ)*X 2 0+(5394108039/10000000000 : ℝ)*X 2 1+(-1071490833/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s9_5 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((4376367039/10000000000 : ℝ)*X 0 0+(4504904241/10000000000 : ℝ)*X 0 1+(850313899/2000000000 : ℝ)*X 0 2+(4376367039/10000000000 : ℝ)*X 1 0+(4504904241/10000000000 : ℝ)*X 1 1+(850313899/2000000000 : ℝ)*X 1 2+(4376367039/10000000000 : ℝ)*X 2 0+(4504904241/10000000000 : ℝ)*X 2 1+(850313899/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s9_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (697287119355626248787148219/137800000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (278543/2500000000000 : ℝ)*(base19) + (9276343/10000000000000 : ℝ)*(lower2) + (16167759/25000000000000 : ℝ)*(lower3) + (45809621/50000000000000 : ℝ)*(lower4) + (5807924190825543/100000000000000 : ℝ)*(major0) + (5807924190825543/100000000000000 : ℝ)*(major1) + (5807924190825543/100000000000000 : ℝ)*(major2) + (7688293240828399/100000000000000 : ℝ)*(sp0) + (48051799715117/625000000000 : ℝ)*(sp1) + (768828978337763/10000000000000 : ℝ)*(sp2) + (3927550530666933/100000000000000 : ℝ)*(sp3) + (2637633979/50000000000000 : ℝ)*(sp4) + (3457450769/100000000000000 : ℝ)*(sp5) + (2220742227/50000000000000 : ℝ)*(sp6) + (3927554972151387/100000000000000 : ℝ)*(f.failure) + (7688293240828399/100000000000000 : ℝ)*(f.sum) + (30299614915987/13780000000000000000000000000 : ℝ)*base66 + (449453890379471309/275600000000000000000000000000000 : ℝ)*base67 + (3905860363925471309/275600000000000000000000000000000 : ℝ)*base69 + (1638437908793871309/275600000000000000000000000000000 : ℝ)*base71 + (22622579145427/13780000000000000000000000000 : ℝ)*base74 + (4661886665907071309/275600000000000000000000000000000 : ℝ)*base75 + (2316510806446671309/275600000000000000000000000000000 : ℝ)*base77 + (2215987351778671309/275600000000000000000000000000000 : ℝ)*base79 + (115724439947453/13780000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (13878903/10000000000000000000000 : ℝ)*base90 + (13878903/10000000000000000000000 : ℝ)*base92 + (13878903/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1060_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147876331/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13999/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11243/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2811/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13999/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1060_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1060_box_0 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2077055421/10000000000 : ℝ)*x 0 + (5377449451/10000000000 : ℝ)*x 1 + (134436249/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2077055421/10000000000 : ℝ)^8253 ≤ (12364240743627/100000000000000 : ℝ)^6205 := by
    have hnat : (2077055421 : ℕ)^8253*100000000000000^6205 ≤ 12364240743627^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077055421 10000000000 12364240743627 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5377449451/10000000000 : ℝ)^8253 ≤ (43817876863331/100000000000000 : ℝ)^6205 := by
    have hnat : (5377449451 : ℕ)^8253*100000000000000^6205 ≤ 43817876863331^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377449451 10000000000 43817876863331 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (134436249/250000000 : ℝ)^8253 ≤ (43817882379821/100000000000000 : ℝ)^6205 := by
    have hnat : (134436249 : ℕ)^8253*100000000000000^6205 ≤ 43817882379821^6205*250000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134436249 250000000 43817882379821 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2077055421/10000000000 : ℝ), (5377449451/10000000000 : ℝ), (134436249/250000000 : ℝ)] ![(12364240743627/100000000000000 : ℝ), (43817876863331/100000000000000 : ℝ), (43817882379821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2077055421/10000000000 : ℝ)|^8253 ≤ (12364240743627/100000000000000 : ℝ)^6205
        have hw : |(-2077055421/10000000000 : ℝ)|=(2077055421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5377449451/10000000000 : ℝ)|^8253 ≤ (43817876863331/100000000000000 : ℝ)^6205
        have hw : |(5377449451/10000000000 : ℝ)|=(5377449451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(134436249/250000000 : ℝ)|^8253 ≤ (43817882379821/100000000000000 : ℝ)^6205
        have hw : |(134436249/250000000 : ℝ)|=(134436249/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_box_1 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (661891971/1250000000 : ℝ)*x 0 + (-437694109/2000000000 : ℝ)*x 1 + (5377449647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661891971/1250000000 : ℝ)^8253 ≤ (42928030898157/100000000000000 : ℝ)^6205 := by
    have hnat : (661891971 : ℕ)^8253*100000000000000^6205 ≤ 42928030898157^6205*1250000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661891971 1250000000 42928030898157 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (437694109/2000000000 : ℝ)^8253 ≤ (3313522524839/25000000000000 : ℝ)^6205 := by
    have hnat : (437694109 : ℕ)^8253*25000000000000^6205 ≤ 3313522524839^6205*2000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437694109 2000000000 3313522524839 25000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5377449647/10000000000 : ℝ)^8253 ≤ (43817878987559/100000000000000 : ℝ)^6205 := by
    have hnat : (5377449647 : ℕ)^8253*100000000000000^6205 ≤ 43817878987559^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377449647 10000000000 43817878987559 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661891971/1250000000 : ℝ), (-437694109/2000000000 : ℝ), (5377449647/10000000000 : ℝ)] ![(42928030898157/100000000000000 : ℝ), (3313522524839/25000000000000 : ℝ), (43817878987559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661891971/1250000000 : ℝ)|^8253 ≤ (42928030898157/100000000000000 : ℝ)^6205
        have hw : |(661891971/1250000000 : ℝ)|=(661891971/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-437694109/2000000000 : ℝ)|^8253 ≤ (3313522524839/25000000000000 : ℝ)^6205
        have hw : |(-437694109/2000000000 : ℝ)|=(437694109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5377449647/10000000000 : ℝ)|^8253 ≤ (43817878987559/100000000000000 : ℝ)^6205
        have hw : |(5377449647/10000000000 : ℝ)|=(5377449647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_box_2 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2647567949/5000000000 : ℝ)*x 0 + (1344362441/2500000000 : ℝ)*x 1 + (-1094235107/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647567949/5000000000 : ℝ)^8253 ≤ (5366004037491/12500000000000 : ℝ)^6205 := by
    have hnat : (2647567949 : ℕ)^8253*12500000000000^6205 ≤ 5366004037491^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647567949 5000000000 5366004037491 12500000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1344362441/2500000000 : ℝ)^8253 ≤ (43817880255593/100000000000000 : ℝ)^6205 := by
    have hnat : (1344362441 : ℕ)^8253*100000000000000^6205 ≤ 43817880255593^6205*2500000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344362441 2500000000 43817880255593 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1094235107/5000000000 : ℝ)^8253 ≤ (6627043716533/50000000000000 : ℝ)^6205 := by
    have hnat : (1094235107 : ℕ)^8253*50000000000000^6205 ≤ 6627043716533^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094235107 5000000000 6627043716533 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647567949/5000000000 : ℝ), (1344362441/2500000000 : ℝ), (-1094235107/5000000000 : ℝ)] ![(5366004037491/12500000000000 : ℝ), (43817880255593/100000000000000 : ℝ), (6627043716533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647567949/5000000000 : ℝ)|^8253 ≤ (5366004037491/12500000000000 : ℝ)^6205
        have hw : |(2647567949/5000000000 : ℝ)|=(2647567949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1344362441/2500000000 : ℝ)|^8253 ≤ (43817880255593/100000000000000 : ℝ)^6205
        have hw : |(1344362441/2500000000 : ℝ)|=(1344362441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1094235107/5000000000 : ℝ)|^8253 ≤ (6627043716533/50000000000000 : ℝ)^6205
        have hw : |(-1094235107/5000000000 : ℝ)|=(1094235107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_box_3 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (896962629/2000000000 : ℝ)*x 0 + (4324295879/10000000000 : ℝ)*x 1 + (432429573/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (896962629/2000000000 : ℝ)^8253 ≤ (688383325263/2000000000000 : ℝ)^6205 := by
    have hnat : (896962629 : ℕ)^8253*2000000000000^6205 ≤ 688383325263^6205*2000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896962629 2000000000 688383325263 2000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4324295879/10000000000 : ℝ)^8253 ≤ (32790417612113/100000000000000 : ℝ)^6205 := by
    have hnat : (4324295879 : ℕ)^8253*100000000000000^6205 ≤ 32790417612113^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4324295879 10000000000 32790417612113 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (432429573/1000000000 : ℝ)^8253 ≤ (32790416109359/100000000000000 : ℝ)^6205 := by
    have hnat : (432429573 : ℕ)^8253*100000000000000^6205 ≤ 32790416109359^6205*1000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432429573 1000000000 32790416109359 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(896962629/2000000000 : ℝ), (4324295879/10000000000 : ℝ), (432429573/1000000000 : ℝ)] ![(688383325263/2000000000000 : ℝ), (32790417612113/100000000000000 : ℝ), (32790416109359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(896962629/2000000000 : ℝ)|^8253 ≤ (688383325263/2000000000000 : ℝ)^6205
        have hw : |(896962629/2000000000 : ℝ)|=(896962629/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4324295879/10000000000 : ℝ)|^8253 ≤ (32790417612113/100000000000000 : ℝ)^6205
        have hw : |(4324295879/10000000000 : ℝ)|=(4324295879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(432429573/1000000000 : ℝ)|^8253 ≤ (32790416109359/100000000000000 : ℝ)^6205
        have hw : |(432429573/1000000000 : ℝ)|=(432429573/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_box_4 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1168891353/5000000000 : ℝ)*x 0 + (1320000237/2500000000 : ℝ)*x 1 + (2640000397/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1168891353/5000000000 : ℝ)^8253 ≤ (14470179049413/100000000000000 : ℝ)^6205 := by
    have hnat : (1168891353 : ℕ)^8253*100000000000000^6205 ≤ 14470179049413^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1168891353 5000000000 14470179049413 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1320000237/2500000000 : ℝ)^8253 ≤ (10691227823863/25000000000000 : ℝ)^6205 := by
    have hnat : (1320000237 : ℕ)^8253*25000000000000^6205 ≤ 10691227823863^6205*2500000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320000237 2500000000 10691227823863 25000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2640000397/5000000000 : ℝ)^8253 ≤ (2138245481823/5000000000000 : ℝ)^6205 := by
    have hnat : (2640000397 : ℕ)^8253*5000000000000^6205 ≤ 2138245481823^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640000397 5000000000 2138245481823 5000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1168891353/5000000000 : ℝ), (1320000237/2500000000 : ℝ), (2640000397/5000000000 : ℝ)] ![(14470179049413/100000000000000 : ℝ), (10691227823863/25000000000000 : ℝ), (2138245481823/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1168891353/5000000000 : ℝ)|^8253 ≤ (14470179049413/100000000000000 : ℝ)^6205
        have hw : |(-1168891353/5000000000 : ℝ)|=(1168891353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1320000237/2500000000 : ℝ)|^8253 ≤ (10691227823863/25000000000000 : ℝ)^6205
        have hw : |(1320000237/2500000000 : ℝ)|=(1320000237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2640000397/5000000000 : ℝ)|^8253 ≤ (2138245481823/5000000000000 : ℝ)^6205
        have hw : |(2640000397/5000000000 : ℝ)|=(2640000397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_box_5 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1072822313/2000000000 : ℝ)*x 0 + (-2226550097/10000000000 : ℝ)*x 1 + (5280000881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072822313/2000000000 : ℝ)^8253 ≤ (4367338142009/10000000000000 : ℝ)^6205 := by
    have hnat : (1072822313 : ℕ)^8253*10000000000000^6205 ≤ 4367338142009^6205*2000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072822313 2000000000 4367338142009 10000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2226550097/10000000000 : ℝ)^8253 ≤ (1695213499309/12500000000000 : ℝ)^6205 := by
    have hnat : (2226550097 : ℕ)^8253*12500000000000^6205 ≤ 1695213499309^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2226550097 10000000000 1695213499309 12500000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5280000881/10000000000 : ℝ)^8253 ≤ (42764910573683/100000000000000 : ℝ)^6205 := by
    have hnat : (5280000881 : ℕ)^8253*100000000000000^6205 ≤ 42764910573683^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280000881 10000000000 42764910573683 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072822313/2000000000 : ℝ), (-2226550097/10000000000 : ℝ), (5280000881/10000000000 : ℝ)] ![(4367338142009/10000000000000 : ℝ), (1695213499309/12500000000000 : ℝ), (42764910573683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072822313/2000000000 : ℝ)|^8253 ≤ (4367338142009/10000000000000 : ℝ)^6205
        have hw : |(1072822313/2000000000 : ℝ)|=(1072822313/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2226550097/10000000000 : ℝ)|^8253 ≤ (1695213499309/12500000000000 : ℝ)^6205
        have hw : |(-2226550097/10000000000 : ℝ)|=(2226550097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5280000881/10000000000 : ℝ)|^8253 ≤ (42764910573683/100000000000000 : ℝ)^6205
        have hw : |(5280000881/10000000000 : ℝ)|=(5280000881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_box_6 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5364111759/10000000000 : ℝ)*x 0 + (5280000791/10000000000 : ℝ)*x 1 + (-556637489/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364111759/10000000000 : ℝ)^8253 ≤ (43673383520919/100000000000000 : ℝ)^6205 := by
    have hnat : (5364111759 : ℕ)^8253*100000000000000^6205 ≤ 43673383520919^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364111759 10000000000 43673383520919 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5280000791/10000000000 : ℝ)^8253 ≤ (21382454802071/50000000000000 : ℝ)^6205 := by
    have hnat : (5280000791 : ℕ)^8253*50000000000000^6205 ≤ 21382454802071^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280000791 10000000000 21382454802071 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (556637489/2500000000 : ℝ)^8253 ≤ (3390426713049/25000000000000 : ℝ)^6205 := by
    have hnat : (556637489 : ℕ)^8253*25000000000000^6205 ≤ 3390426713049^6205*2500000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      556637489 2500000000 3390426713049 25000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364111759/10000000000 : ℝ), (5280000791/10000000000 : ℝ), (-556637489/2500000000 : ℝ)] ![(43673383520919/100000000000000 : ℝ), (21382454802071/50000000000000 : ℝ), (3390426713049/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364111759/10000000000 : ℝ)|^8253 ≤ (43673383520919/100000000000000 : ℝ)^6205
        have hw : |(5364111759/10000000000 : ℝ)|=(5364111759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5280000791/10000000000 : ℝ)|^8253 ≤ (21382454802071/50000000000000 : ℝ)^6205
        have hw : |(5280000791/10000000000 : ℝ)|=(5280000791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-556637489/2500000000 : ℝ)|^8253 ≤ (3390426713049/25000000000000 : ℝ)^6205
        have hw : |(-556637489/2500000000 : ℝ)|=(556637489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_box_7 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4267574709/10000000000 : ℝ)*x 0 + (443289343/1000000000 : ℝ)*x 1 + (2216446797/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4267574709/10000000000 : ℝ)^8253 ≤ (32219592729763/100000000000000 : ℝ)^6205 := by
    have hnat : (4267574709 : ℕ)^8253*100000000000000^6205 ≤ 32219592729763^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4267574709 10000000000 32219592729763 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (443289343/1000000000 : ℝ)^8253 ≤ (1355608111723/4000000000000 : ℝ)^6205 := by
    have hnat : (443289343 : ℕ)^8253*4000000000000^6205 ≤ 1355608111723^6205*1000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443289343 1000000000 1355608111723 4000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2216446797/5000000000 : ℝ)^8253 ≤ (3389020446071/10000000000000 : ℝ)^6205 := by
    have hnat : (2216446797 : ℕ)^8253*10000000000000^6205 ≤ 3389020446071^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2216446797 5000000000 3389020446071 10000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4267574709/10000000000 : ℝ), (443289343/1000000000 : ℝ), (2216446797/5000000000 : ℝ)] ![(32219592729763/100000000000000 : ℝ), (1355608111723/4000000000000 : ℝ), (3389020446071/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4267574709/10000000000 : ℝ)|^8253 ≤ (32219592729763/100000000000000 : ℝ)^6205
        have hw : |(4267574709/10000000000 : ℝ)|=(4267574709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(443289343/1000000000 : ℝ)|^8253 ≤ (1355608111723/4000000000000 : ℝ)^6205
        have hw : |(443289343/1000000000 : ℝ)|=(443289343/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2216446797/5000000000 : ℝ)|^8253 ≤ (3389020446071/10000000000000 : ℝ)^6205
        have hw : |(2216446797/5000000000 : ℝ)|=(2216446797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_box_8 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-456672201/2000000000 : ℝ)*x 0 + (2606943921/5000000000 : ℝ)*x 1 + (2693524833/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (456672201/2000000000 : ℝ)^8253 ≤ (14023874319671/100000000000000 : ℝ)^6205 := by
    have hnat : (456672201 : ℕ)^8253*100000000000000^6205 ≤ 14023874319671^6205*2000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456672201 2000000000 14023874319671 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2606943921/5000000000 : ℝ)^8253 ≤ (5256771501887/12500000000000 : ℝ)^6205 := by
    have hnat : (2606943921 : ℕ)^8253*12500000000000^6205 ≤ 5256771501887^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2606943921 5000000000 5256771501887 12500000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693524833/5000000000 : ℝ)^8253 ≤ (4392195365471/10000000000000 : ℝ)^6205 := by
    have hnat : (2693524833 : ℕ)^8253*10000000000000^6205 ≤ 4392195365471^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693524833 5000000000 4392195365471 10000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-456672201/2000000000 : ℝ), (2606943921/5000000000 : ℝ), (2693524833/5000000000 : ℝ)] ![(14023874319671/100000000000000 : ℝ), (5256771501887/12500000000000 : ℝ), (4392195365471/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-456672201/2000000000 : ℝ)|^8253 ≤ (14023874319671/100000000000000 : ℝ)^6205
        have hw : |(-456672201/2000000000 : ℝ)|=(456672201/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2606943921/5000000000 : ℝ)|^8253 ≤ (5256771501887/12500000000000 : ℝ)^6205
        have hw : |(2606943921/5000000000 : ℝ)|=(2606943921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693524833/5000000000 : ℝ)|^8253 ≤ (4392195365471/10000000000000 : ℝ)^6205
        have hw : |(2693524833/5000000000 : ℝ)|=(2693524833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_box_9 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (661042119/1250000000 : ℝ)*x 0 + (-2184648479/10000000000 : ℝ)*x 1 + (2693524801/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661042119/1250000000 : ℝ)^8253 ≤ (21427367881047/50000000000000 : ℝ)^6205 := by
    have hnat : (661042119 : ℕ)^8253*50000000000000^6205 ≤ 21427367881047^6205*1250000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661042119 1250000000 21427367881047 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2184648479/10000000000 : ℝ)^8253 ≤ (13223311261519/100000000000000 : ℝ)^6205 := by
    have hnat : (2184648479 : ℕ)^8253*100000000000000^6205 ≤ 13223311261519^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184648479 10000000000 13223311261519 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693524801/5000000000 : ℝ)^8253 ≤ (10980488240169/25000000000000 : ℝ)^6205 := by
    have hnat : (2693524801 : ℕ)^8253*25000000000000^6205 ≤ 10980488240169^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693524801 5000000000 10980488240169 25000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661042119/1250000000 : ℝ), (-2184648479/10000000000 : ℝ), (2693524801/5000000000 : ℝ)] ![(21427367881047/50000000000000 : ℝ), (13223311261519/100000000000000 : ℝ), (10980488240169/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661042119/1250000000 : ℝ)|^8253 ≤ (21427367881047/50000000000000 : ℝ)^6205
        have hw : |(661042119/1250000000 : ℝ)|=(661042119/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2184648479/10000000000 : ℝ)|^8253 ≤ (13223311261519/100000000000000 : ℝ)^6205
        have hw : |(-2184648479/10000000000 : ℝ)|=(2184648479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693524801/5000000000 : ℝ)|^8253 ≤ (10980488240169/25000000000000 : ℝ)^6205
        have hw : |(2693524801/5000000000 : ℝ)|=(2693524801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_box_10 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1322084261/2500000000 : ℝ)*x 0 + (5387049623/10000000000 : ℝ)*x 1 + (-273081041/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322084261/2500000000 : ℝ)^8253 ≤ (42854736753697/100000000000000 : ℝ)^6205 := by
    have hnat : (1322084261 : ℕ)^8253*100000000000000^6205 ≤ 42854736753697^6205*2500000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322084261 2500000000 42854736753697 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5387049623/10000000000 : ℝ)^8253 ≤ (21960976594203/50000000000000 : ℝ)^6205 := by
    have hnat : (5387049623 : ℕ)^8253*50000000000000^6205 ≤ 21960976594203^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387049623 10000000000 21960976594203 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (273081041/1250000000 : ℝ)^8253 ≤ (13223310045877/100000000000000 : ℝ)^6205 := by
    have hnat : (273081041 : ℕ)^8253*100000000000000^6205 ≤ 13223310045877^6205*1250000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273081041 1250000000 13223310045877 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322084261/2500000000 : ℝ), (5387049623/10000000000 : ℝ), (-273081041/1250000000 : ℝ)] ![(42854736753697/100000000000000 : ℝ), (21960976594203/50000000000000 : ℝ), (13223310045877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322084261/2500000000 : ℝ)|^8253 ≤ (42854736753697/100000000000000 : ℝ)^6205
        have hw : |(1322084261/2500000000 : ℝ)|=(1322084261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5387049623/10000000000 : ℝ)|^8253 ≤ (21960976594203/50000000000000 : ℝ)^6205
        have hw : |(5387049623/10000000000 : ℝ)|=(5387049623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-273081041/1250000000 : ℝ)|^8253 ≤ (13223310045877/100000000000000 : ℝ)^6205
        have hw : |(-273081041/1250000000 : ℝ)|=(273081041/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_box_11 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1126485201/2500000000 : ℝ)*x 0 + (215679569/500000000 : ℝ)*x 1 + (2156795759/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1126485201/2500000000 : ℝ)^8253 ≤ (17317498820207/50000000000000 : ℝ)^6205 := by
    have hnat : (1126485201 : ℕ)^8253*50000000000000^6205 ≤ 17317498820207^6205*2500000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126485201 2500000000 17317498820207 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215679569/500000000 : ℝ)^8253 ≤ (32682500478761/100000000000000 : ℝ)^6205 := by
    have hnat : (215679569 : ℕ)^8253*100000000000000^6205 ≤ 32682500478761^6205*500000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215679569 500000000 32682500478761 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2156795759/5000000000 : ℝ)^8253 ≤ (8170625467359/25000000000000 : ℝ)^6205 := by
    have hnat : (2156795759 : ℕ)^8253*25000000000000^6205 ≤ 8170625467359^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156795759 5000000000 8170625467359 25000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1126485201/2500000000 : ℝ), (215679569/500000000 : ℝ), (2156795759/5000000000 : ℝ)] ![(17317498820207/50000000000000 : ℝ), (32682500478761/100000000000000 : ℝ), (8170625467359/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1126485201/2500000000 : ℝ)|^8253 ≤ (17317498820207/50000000000000 : ℝ)^6205
        have hw : |(1126485201/2500000000 : ℝ)|=(1126485201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215679569/500000000 : ℝ)|^8253 ≤ (32682500478761/100000000000000 : ℝ)^6205
        have hw : |(215679569/500000000 : ℝ)|=(215679569/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2156795759/5000000000 : ℝ)|^8253 ≤ (8170625467359/25000000000000 : ℝ)^6205
        have hw : |(2156795759/5000000000 : ℝ)|=(2156795759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_box_12 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-266481209/1250000000 : ℝ)*x 0 + (5442222271/10000000000 : ℝ)*x 1 + (2636001657/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (266481209/1250000000 : ℝ)^8253 ≤ (6399976650953/50000000000000 : ℝ)^6205 := by
    have hnat : (266481209 : ℕ)^8253*50000000000000^6205 ≤ 6399976650953^6205*1250000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266481209 1250000000 6399976650953 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5442222271/10000000000 : ℝ)^8253 ≤ (44521269779169/100000000000000 : ℝ)^6205 := by
    have hnat : (5442222271 : ℕ)^8253*100000000000000^6205 ≤ 44521269779169^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442222271 10000000000 44521269779169 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2636001657/5000000000 : ℝ)^8253 ≤ (42678776912011/100000000000000 : ℝ)^6205 := by
    have hnat : (2636001657 : ℕ)^8253*100000000000000^6205 ≤ 42678776912011^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636001657 5000000000 42678776912011 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-266481209/1250000000 : ℝ), (5442222271/10000000000 : ℝ), (2636001657/5000000000 : ℝ)] ![(6399976650953/50000000000000 : ℝ), (44521269779169/100000000000000 : ℝ), (42678776912011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-266481209/1250000000 : ℝ)|^8253 ≤ (6399976650953/50000000000000 : ℝ)^6205
        have hw : |(-266481209/1250000000 : ℝ)|=(266481209/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5442222271/10000000000 : ℝ)|^8253 ≤ (44521269779169/100000000000000 : ℝ)^6205
        have hw : |(5442222271/10000000000 : ℝ)|=(5442222271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2636001657/5000000000 : ℝ)|^8253 ≤ (42678776912011/100000000000000 : ℝ)^6205
        have hw : |(2636001657/5000000000 : ℝ)|=(2636001657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_box_13 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2684885029/5000000000 : ℝ)*x 0 + (-1114808429/5000000000 : ℝ)*x 1 + (263600151/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684885029/5000000000 : ℝ)^8253 ≤ (10933667001847/25000000000000 : ℝ)^6205 := by
    have hnat : (2684885029 : ℕ)^8253*25000000000000^6205 ≤ 10933667001847^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684885029 5000000000 10933667001847 25000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1114808429/5000000000 : ℝ)^8253 ≤ (1358655823427/10000000000000 : ℝ)^6205 := by
    have hnat : (1114808429 : ℕ)^8253*10000000000000^6205 ≤ 1358655823427^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1114808429 5000000000 1358655823427 10000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263600151/500000000 : ℝ)^8253 ≤ (42678773746429/100000000000000 : ℝ)^6205 := by
    have hnat : (263600151 : ℕ)^8253*100000000000000^6205 ≤ 42678773746429^6205*500000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263600151 500000000 42678773746429 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684885029/5000000000 : ℝ), (-1114808429/5000000000 : ℝ), (263600151/500000000 : ℝ)] ![(10933667001847/25000000000000 : ℝ), (1358655823427/10000000000000 : ℝ), (42678773746429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684885029/5000000000 : ℝ)|^8253 ≤ (10933667001847/25000000000000 : ℝ)^6205
        have hw : |(2684885029/5000000000 : ℝ)|=(2684885029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1114808429/5000000000 : ℝ)|^8253 ≤ (1358655823427/10000000000000 : ℝ)^6205
        have hw : |(-1114808429/5000000000 : ℝ)|=(1114808429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263600151/500000000 : ℝ)|^8253 ≤ (42678773746429/100000000000000 : ℝ)^6205
        have hw : |(263600151/500000000 : ℝ)|=(263600151/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_box_14 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2684884989/5000000000 : ℝ)*x 0 + (2636001683/5000000000 : ℝ)*x 1 + (-445923301/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684884989/5000000000 : ℝ)^8253 ≤ (8746933428153/20000000000000 : ℝ)^6205 := by
    have hnat : (2684884989 : ℕ)^8253*20000000000000^6205 ≤ 8746933428153^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684884989 5000000000 8746933428153 20000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2636001683/5000000000 : ℝ)^8253 ≤ (4267877747191/10000000000000 : ℝ)^6205 := by
    have hnat : (2636001683 : ℕ)^8253*10000000000000^6205 ≤ 4267877747191^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636001683 5000000000 4267877747191 10000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (445923301/2000000000 : ℝ)^8253 ≤ (13586555373229/100000000000000 : ℝ)^6205 := by
    have hnat : (445923301 : ℕ)^8253*100000000000000^6205 ≤ 13586555373229^6205*2000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      445923301 2000000000 13586555373229 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684884989/5000000000 : ℝ), (2636001683/5000000000 : ℝ), (-445923301/2000000000 : ℝ)] ![(8746933428153/20000000000000 : ℝ), (4267877747191/10000000000000 : ℝ), (13586555373229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684884989/5000000000 : ℝ)|^8253 ≤ (8746933428153/20000000000000 : ℝ)^6205
        have hw : |(2684884989/5000000000 : ℝ)|=(2684884989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2636001683/5000000000 : ℝ)|^8253 ≤ (4267877747191/10000000000000 : ℝ)^6205
        have hw : |(2636001683/5000000000 : ℝ)|=(2636001683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-445923301/2000000000 : ℝ)|^8253 ≤ (13586555373229/100000000000000 : ℝ)^6205
        have hw : |(-445923301/2000000000 : ℝ)|=(445923301/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_box_15 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4249514747/10000000000 : ℝ)*x 0 + (2220900869/5000000000 : ℝ)*x 1 + (4441801739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4249514747/10000000000 : ℝ)^8253 ≤ (32038366060847/100000000000000 : ℝ)^6205 := by
    have hnat : (4249514747 : ℕ)^8253*100000000000000^6205 ≤ 32038366060847^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249514747 10000000000 32038366060847 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2220900869/5000000000 : ℝ)^8253 ≤ (8495204239947/25000000000000 : ℝ)^6205 := by
    have hnat : (2220900869 : ℕ)^8253*25000000000000^6205 ≤ 8495204239947^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2220900869 5000000000 8495204239947 25000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4441801739/10000000000 : ℝ)^8253 ≤ (33980816969963/100000000000000 : ℝ)^6205 := by
    have hnat : (4441801739 : ℕ)^8253*100000000000000^6205 ≤ 33980816969963^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4441801739 10000000000 33980816969963 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4249514747/10000000000 : ℝ), (2220900869/5000000000 : ℝ), (4441801739/10000000000 : ℝ)] ![(32038366060847/100000000000000 : ℝ), (8495204239947/25000000000000 : ℝ), (33980816969963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4249514747/10000000000 : ℝ)|^8253 ≤ (32038366060847/100000000000000 : ℝ)^6205
        have hw : |(4249514747/10000000000 : ℝ)|=(4249514747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2220900869/5000000000 : ℝ)|^8253 ≤ (8495204239947/25000000000000 : ℝ)^6205
        have hw : |(2220900869/5000000000 : ℝ)|=(2220900869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4441801739/10000000000 : ℝ)|^8253 ≤ (33980816969963/100000000000000 : ℝ)^6205
        have hw : |(4441801739/10000000000 : ℝ)|=(4441801739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1060_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147876331/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13999/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2811/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(3889/6250 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14809/25000 : ℝ) ∧ (79553/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (82939/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13999/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2811/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13999/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2811/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13999/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2811/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13999/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2811/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13999/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2811/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13999/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2811/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2811/25000 : ℝ) ^ (2063/512 : ℝ) ≤ (14992646255440887/100000000000000000000 : ℝ) := by
    have hpowers : (2811/25000 : ℝ)^2063 ≤ (14992646255440887/100000000000000000000 : ℝ)^512 := by
      have hnat : (2811 : ℕ)^2063*100000000000000000000^512 ≤ 14992646255440887^512*25000^2063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2811 25000 14992646255440887 100000000000000000000 2063 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2811/25000 : ℝ)) (X := (14992646255440887/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hpowhi : (13999/100000 : ℝ) ^ (2063/512 : ℝ) ≤ (18127644238686597/50000000000000000000 : ℝ) := by
    have hpowers : (13999/100000 : ℝ)^2063 ≤ (18127644238686597/50000000000000000000 : ℝ)^512 := by
      have hnat : (13999 : ℕ)^2063*50000000000000000000^512 ≤ 18127644238686597^512*100000^2063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13999 100000 18127644238686597 50000000000000000000 2063 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13999/100000 : ℝ)) (X := (18127644238686597/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014992646255440887/50000000000000000000 : ℝ) ≤ (5000372048947611/5000000000000000 : ℝ) ^ (2063/512 : ℝ) := by
    have hpowers : (50014992646255440887/50000000000000000000 : ℝ)^512 ≤ (5000372048947611/5000000000000000 : ℝ)^2063 := by
      have hnat : (50014992646255440887 : ℕ)^512*5000000000000000^2063 ≤ 5000372048947611^2063*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014992646255440887 50000000000000000000 5000372048947611 5000000000000000 512 2063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000372048947611/5000000000000000 : ℝ)) (X := (50014992646255440887/50000000000000000000 : ℝ)) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051247934732814081/100000000000000000000 : ℝ) ≤ (2500317909467769/2500000000000000 : ℝ) ^ (2063/512 : ℝ) := by
    have hpowers : (100051247934732814081/100000000000000000000 : ℝ)^512 ≤ (2500317909467769/2500000000000000 : ℝ)^2063 := by
      have hnat : (100051247934732814081 : ℕ)^512*2500000000000000^2063 ≤ 2500317909467769^2063*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051247934732814081 100000000000000000000 2500317909467769 2500000000000000 512 2063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500317909467769/2500000000000000 : ℝ)) (X := (100051247934732814081/100000000000000000000 : ℝ)) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018127644238686597/25000000000000000000 : ℝ) ≤ (1000179917784693/1000000000000000 : ℝ) ^ (2063/512 : ℝ) := by
    have hpowers : (25018127644238686597/25000000000000000000 : ℝ)^512 ≤ (1000179917784693/1000000000000000 : ℝ)^2063 := by
      have hnat : (25018127644238686597 : ℕ)^512*1000000000000000^2063 ≤ 1000179917784693^2063*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018127644238686597 25000000000000000000 1000179917784693 1000000000000000 512 2063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000179917784693/1000000000000000 : ℝ)) (X := (25018127644238686597/25000000000000000000 : ℝ)) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14992646255440887/100000000000000000000 : ℝ) ≤ ((13770093335362165929/13775000000000000000 : ℝ)+2*(263769987927/137750000000000 : ℝ)*(2811/25000 : ℝ))^(2063/512 : ℝ) := by
    rw [show (13770093335362165929/13775000000000000000 : ℝ)+2*(263769987927/137750000000000 : ℝ)*(2811/25000 : ℝ)=(5000372048947611/5000000000000000 : ℝ) by norm_num, show 1+2*(14992646255440887/100000000000000000000 : ℝ)=(50014992646255440887/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18127644238686597/50000000000000000000 : ℝ)+(14992646255440887/100000000000000000000 : ℝ) ≤ ((13770093335362165929/13775000000000000000 : ℝ)+(263769987927/137750000000000 : ℝ)*((13999/100000 : ℝ)+(2811/25000 : ℝ)))^(2063/512 : ℝ) := by
    rw [show (13770093335362165929/13775000000000000000 : ℝ)+(263769987927/137750000000000 : ℝ)*((13999/100000 : ℝ)+(2811/25000 : ℝ))=(2500317909467769/2500000000000000 : ℝ) by norm_num, show 1+(18127644238686597/50000000000000000000 : ℝ)+(14992646255440887/100000000000000000000 : ℝ)=(100051247934732814081/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18127644238686597/50000000000000000000 : ℝ) ≤ ((13770093335362165929/13775000000000000000 : ℝ)+2*(263769987927/137750000000000 : ℝ)*(13999/100000 : ℝ))^(2063/512 : ℝ) := by
    rw [show (13770093335362165929/13775000000000000000 : ℝ)+2*(263769987927/137750000000000 : ℝ)*(13999/100000 : ℝ)=(1000179917784693/1000000000000000 : ℝ) by norm_num, show 1+2*(18127644238686597/50000000000000000000 : ℝ)=(25018127644238686597/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13770093335362165929/13775000000000000000 : ℝ)*(X 1 0+X 2 0)+(263769987927/137750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2063/512 : ℝ)) (lo := (2811/25000 : ℝ)) (hi := (13999/100000 : ℝ)) (c := (13770093335362165929/13775000000000000000 : ℝ)) (alpha := (263769987927/137750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13770093335362165929/13775000000000000000 : ℝ)*(X 0 1+X 2 1)+(263769987927/137750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2063/512 : ℝ)) (lo := (2811/25000 : ℝ)) (hi := (13999/100000 : ℝ)) (c := (13770093335362165929/13775000000000000000 : ℝ)) (alpha := (263769987927/137750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13770093335362165929/13775000000000000000 : ℝ)*(X 0 2+X 1 2)+(263769987927/137750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2063/512 : ℝ)) (lo := (2811/25000 : ℝ)) (hi := (13999/100000 : ℝ)) (c := (13770093335362165929/13775000000000000000 : ℝ)) (alpha := (263769987927/137750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2077055421/10000000000 : ℝ)*X 0 0+(5377449451/10000000000 : ℝ)*X 0 1+(134436249/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((661891971/1250000000 : ℝ)*X 1 0+(-437694109/2000000000 : ℝ)*X 1 1+(5377449647/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2647567949/5000000000 : ℝ)*X 2 0+(1344362441/2500000000 : ℝ)*X 2 1+(-1094235107/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((896962629/2000000000 : ℝ)*X 0 0+(4324295879/10000000000 : ℝ)*X 0 1+(432429573/1000000000 : ℝ)*X 0 2+(896962629/2000000000 : ℝ)*X 1 0+(4324295879/10000000000 : ℝ)*X 1 1+(432429573/1000000000 : ℝ)*X 1 2+(896962629/2000000000 : ℝ)*X 2 0+(4324295879/10000000000 : ℝ)*X 2 1+(432429573/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1168891353/5000000000 : ℝ)*X 0 0+(1320000237/2500000000 : ℝ)*X 0 1+(2640000397/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1072822313/2000000000 : ℝ)*X 1 0+(-2226550097/10000000000 : ℝ)*X 1 1+(5280000881/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5364111759/10000000000 : ℝ)*X 2 0+(5280000791/10000000000 : ℝ)*X 2 1+(-556637489/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4267574709/10000000000 : ℝ)*X 0 0+(443289343/1000000000 : ℝ)*X 0 1+(2216446797/5000000000 : ℝ)*X 0 2+(4267574709/10000000000 : ℝ)*X 1 0+(443289343/1000000000 : ℝ)*X 1 1+(2216446797/5000000000 : ℝ)*X 1 2+(4267574709/10000000000 : ℝ)*X 2 0+(443289343/1000000000 : ℝ)*X 2 1+(2216446797/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-456672201/2000000000 : ℝ)*X 0 0+(2606943921/5000000000 : ℝ)*X 0 1+(2693524833/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((661042119/1250000000 : ℝ)*X 1 0+(-2184648479/10000000000 : ℝ)*X 1 1+(2693524801/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1322084261/2500000000 : ℝ)*X 2 0+(5387049623/10000000000 : ℝ)*X 2 1+(-273081041/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1126485201/2500000000 : ℝ)*X 0 0+(215679569/500000000 : ℝ)*X 0 1+(2156795759/5000000000 : ℝ)*X 0 2+(1126485201/2500000000 : ℝ)*X 1 0+(215679569/500000000 : ℝ)*X 1 1+(2156795759/5000000000 : ℝ)*X 1 2+(1126485201/2500000000 : ℝ)*X 2 0+(215679569/500000000 : ℝ)*X 2 1+(2156795759/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-266481209/1250000000 : ℝ)*X 0 0+(5442222271/10000000000 : ℝ)*X 0 1+(2636001657/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2684885029/5000000000 : ℝ)*X 1 0+(-1114808429/5000000000 : ℝ)*X 1 1+(263600151/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2684884989/5000000000 : ℝ)*X 2 0+(2636001683/5000000000 : ℝ)*X 2 1+(-445923301/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4249514747/10000000000 : ℝ)*X 0 0+(2220900869/5000000000 : ℝ)*X 0 1+(4441801739/10000000000 : ℝ)*X 0 2+(4249514747/10000000000 : ℝ)*X 1 0+(2220900869/5000000000 : ℝ)*X 1 1+(4441801739/10000000000 : ℝ)*X 1 2+(4249514747/10000000000 : ℝ)*X 2 0+(2220900869/5000000000 : ℝ)*X 2 1+(4441801739/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-3889/6250 : ℝ) ≤ (-214276019346854741001392416095441/344375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24962953/25000000000000 : ℝ)*(upper0) + (1020381/25000000000000 : ℝ)*(lower1) + (23907561/20000000000000 : ℝ)*(lower2) + (1925744383628843/50000000000000 : ℝ)*(major0) + (1925744383628843/50000000000000 : ℝ)*(major1) + (1925744383628843/50000000000000 : ℝ)*(major2) + (15880487/1250000000000 : ℝ)*(sp3) + (5119181615885233/100000000000000 : ℝ)*(sp4) + (5119172204605557/100000000000000 : ℝ)*(sp5) + (5119136458441029/100000000000000 : ℝ)*(sp6) + (2604532356553507/100000000000000 : ℝ)*(sp7) + (1431086677/50000000000000 : ℝ)*(sp8) + (1227345303/10000000000000 : ℝ)*(sp13) + (48019617559/100000000000000 : ℝ)*(sp14) + (2604533626992467/100000000000000 : ℝ)*(f.failure) + (5119184478058587/100000000000000 : ℝ)*(f.sum) + (36240590577281/13775000000000000000000000000 : ℝ)*base66 + (6412901701534890147/688750000000000000000000000000000 : ℝ)*base67 + (7119640527757390147/688750000000000000000000000000000 : ℝ)*base69 + (5123039418277390147/688750000000000000000000000000000 : ℝ)*base71 + (52142651398069/13775000000000000000000000000 : ℝ)*base73 + (746656372006140147/688750000000000000000000000000000 : ℝ)*base75 + (728898280057609853/688750000000000000000000000000000 : ℝ)*base78 + (22935696316128859853/688750000000000000000000000000000 : ℝ)*base80 + (7499490029119/13775000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (15401423/10000000000000000000000 : ℝ)*base90 + (15401423/10000000000000000000000 : ℝ)*base92 + (15401423/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (14809/25000 : ℝ) ≤ (10737025371338871856060889881209/18125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (56650791/100000000000000 : ℝ)*(lower0) + (39394393/25000000000000 : ℝ)*(lower3) + (122332451/100000000000000 : ℝ)*(upper4) + (1957152637381011/50000000000000 : ℝ)*(major0) + (1957152637381011/50000000000000 : ℝ)*(major1) + (1957152637381011/50000000000000 : ℝ)*(major2) + (5161849773294849/100000000000000 : ℝ)*(sp0) + (5161850033698973/100000000000000 : ℝ)*(sp1) + (1032368405357227/20000000000000 : ℝ)*(sp2) + (41359509923537/1562500000000 : ℝ)*(sp3) + (388386609/25000000000000 : ℝ)*(sp5) + (4780229637/50000000000000 : ℝ)*(sp6) + (162944631/4000000000000 : ℝ)*(sp7) + (11337191/625000000000 : ℝ)*(sp12) + (2647012708722143/100000000000000 : ℝ)*(f.failure) + (5161851587245409/100000000000000 : ℝ)*(f.sum) + (1116324705451/362500000000000000000000000 : ℝ)*base65 + (167967689961488199/36250000000000000000000000000000 : ℝ)*base68 + (297189895187738199/36250000000000000000000000000000 : ℝ)*base70 + (114822473313988199/36250000000000000000000000000000 : ℝ)*base72 + (19436050581873/725000000000000000000000000 : ℝ)*base74 + (30466410491488199/36250000000000000000000000000000 : ℝ)*base76 + (213490572273988199/36250000000000000000000000000000 : ℝ)*base78 + (386787487755238199/36250000000000000000000000000000 : ℝ)*base80 + (305167329981/90625000000000000000000000 : ℝ)*base82 + (5297333/10000000000000000000000 : ℝ)*base89 + (5297333/10000000000000000000000 : ℝ)*base91 + (5297333/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (79553/100000 : ℝ) ≤ (68492591280627179033004373814307/86093750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23817917/50000000000000 : ℝ)*(upper0) + (32790429/50000000000000 : ℝ)*(lower3) + (19901503/25000000000000 : ℝ)*(upper4) + (1095642427750211/25000000000000 : ℝ)*(major0) + (1095642427750211/25000000000000 : ℝ)*(major1) + (1095642427750211/25000000000000 : ℝ)*(major2) + (8586285321/20000000000000 : ℝ)*(sp1) + (40936878183/50000000000000 : ℝ)*(sp2) + (20339151389/50000000000000 : ℝ)*(sp3) + (1176358847/100000000000000 : ℝ)*(sp4) + (2887473719418817/50000000000000 : ℝ)*(sp8) + (5774905683769877/100000000000000 : ℝ)*(sp9) + (1443716685360029/25000000000000 : ℝ)*(sp10) + (1481815760434029/50000000000000 : ℝ)*(sp11) + (740918049792709/25000000000000 : ℝ)*(f.failure) + (2887474307598241/50000000000000 : ℝ)*(f.sum) + (34580150724487/6887500000000000000000000000 : ℝ)*base66 + (249420050434788981/344375000000000000000000000000000 : ℝ)*base68 + (2957137383597288981/344375000000000000000000000000000 : ℝ)*base70 + (3817948580622288981/344375000000000000000000000000000 : ℝ)*base72 + (72749172899537/6887500000000000000000000000 : ℝ)*base74 + (2323226563270413981/344375000000000000000000000000000 : ℝ)*base76 + (3286640366014788981/344375000000000000000000000000000 : ℝ)*base78 + (562533167997711019/344375000000000000000000000000000 : ℝ)*base79 + (10350810021131/3443750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (17470679/2500000000000000000000 : ℝ)*base89 + (17470679/2500000000000000000000 : ℝ)*base91 + (17470679/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-82939/100000 : ℝ) ≤ (-15032200516003555431090100820439/18125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (71310589/100000000000000 : ℝ)*(lower0) + (33709249/100000000000000 : ℝ)*(upper1) + (52094579/100000000000000 : ℝ)*(lower2) + (64748639/25000000000000 : ℝ)*(upper5) + (4417060358345543/100000000000000 : ℝ)*(major0) + (4417060358345543/100000000000000 : ℝ)*(major1) + (4417060358345543/100000000000000 : ℝ)*(major2) + (1314494021/100000000000000 : ℝ)*(sp4) + (175122137303/100000000000000 : ℝ)*(sp5) + (29556943517/20000000000000 : ℝ)*(sp7) + (293738432413169/5000000000000 : ℝ)*(sp12) + (2937297420310049/50000000000000 : ℝ)*(sp13) + (5874769962757401/100000000000000 : ℝ)*(sp14) + (2986848395452413/100000000000000 : ℝ)*(sp15) + (1493498090084999/50000000000000 : ℝ)*(f.failure) + (5874769962757401/100000000000000 : ℝ)*(f.sum) + (14040926944743/3443750000000000000000000000 : ℝ)*base65 + (12655965977839704447/1377500000000000000000000000000000 : ℝ)*base67 + (3454042190567204447/1377500000000000000000000000000000 : ℝ)*base69 + (17209155961407204447/1377500000000000000000000000000000 : ℝ)*base71 + (550188371676753/13775000000000000000000000000 : ℝ)*base74 + (12437317650919704447/1377500000000000000000000000000000 : ℝ)*base75 + (15757997869534704447/1377500000000000000000000000000000 : ℝ)*base77 + (61155090214105295553/1377500000000000000000000000000000 : ℝ)*base80 + (6653965100539/6887500000000000000000000000 : ℝ)*base82 + (19741331/5000000000000000000000 : ℝ)*base90 + (19741331/5000000000000000000000 : ℝ)*base92 + (19741331/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1060_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147876331/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13999/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2811/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(14809/25000 : ℝ) else (79553/100000 : ℝ) ≤ X j i ∧ X j i ≤ (82939/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1060_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1060_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147876331/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13999/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11243/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(14809/25000 : ℝ) else (79553/100000 : ℝ) ≤ X j i ∧ X j i ≤ (82939/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1060_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1060_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147876331/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13999/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11243/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(14809/25000 : ℝ) else (79553/100000 : ℝ) ≤ X j i ∧ X j i ≤ (82939/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1060_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1182_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:50:11.091163+00:00
-- url     : https://prove2.me/submissions/7f438736-a31a-423f-b9ec-909662a5ee0a

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
theorem support_rectangle_w1182_box_0 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2022315241/10000000000 : ℝ)*x 0 + (2687866411/5000000000 : ℝ)*x 1 + (5375732773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2022315241/10000000000 : ℝ)^8375 ≤ (376710413393/3125000000000 : ℝ)^6327 := by
    have hnat : (2022315241 : ℕ)^8375*3125000000000^6327 ≤ 376710413393^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2022315241 10000000000 376710413393 3125000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2687866411/5000000000 : ℝ)^8375 ≤ (43972633640197/100000000000000 : ℝ)^6327 := by
    have hnat : (2687866411 : ℕ)^8375*100000000000000^6327 ≤ 43972633640197^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687866411 5000000000 43972633640197 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5375732773/10000000000 : ℝ)^8375 ≤ (21986316554823/50000000000000 : ℝ)^6327 := by
    have hnat : (5375732773 : ℕ)^8375*50000000000000^6327 ≤ 21986316554823^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375732773 10000000000 21986316554823 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2022315241/10000000000 : ℝ), (2687866411/5000000000 : ℝ), (5375732773/10000000000 : ℝ)] ![(376710413393/3125000000000 : ℝ), (43972633640197/100000000000000 : ℝ), (21986316554823/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2022315241/10000000000 : ℝ)|^8375 ≤ (376710413393/3125000000000 : ℝ)^6327
        have hw : |(-2022315241/10000000000 : ℝ)|=(2022315241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2687866411/5000000000 : ℝ)|^8375 ≤ (43972633640197/100000000000000 : ℝ)^6327
        have hw : |(2687866411/5000000000 : ℝ)|=(2687866411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5375732773/10000000000 : ℝ)|^8375 ≤ (21986316554823/50000000000000 : ℝ)^6327
        have hw : |(5375732773/10000000000 : ℝ)|=(5375732773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_box_1 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (8275527/15625000 : ℝ)*x 0 + (-17040697/80000000 : ℝ)*x 1 + (5375732369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8275527/15625000 : ℝ)^8375 ≤ (21557516537979/50000000000000 : ℝ)^6327 := by
    have hnat : (8275527 : ℕ)^8375*50000000000000^6327 ≤ 21557516537979^6327*15625000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8275527 15625000 21557516537979 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17040697/80000000 : ℝ)^8375 ≤ (12912338182509/100000000000000 : ℝ)^6327 := by
    have hnat : (17040697 : ℕ)^8375*100000000000000^6327 ≤ 12912338182509^6327*80000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17040697 80000000 12912338182509 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5375732369/10000000000 : ℝ)^8375 ≤ (43972628735299/100000000000000 : ℝ)^6327 := by
    have hnat : (5375732369 : ℕ)^8375*100000000000000^6327 ≤ 43972628735299^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375732369 10000000000 43972628735299 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8275527/15625000 : ℝ), (-17040697/80000000 : ℝ), (5375732369/10000000000 : ℝ)] ![(21557516537979/50000000000000 : ℝ), (12912338182509/100000000000000 : ℝ), (43972628735299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8275527/15625000 : ℝ)|^8375 ≤ (21557516537979/50000000000000 : ℝ)^6327
        have hw : |(8275527/15625000 : ℝ)|=(8275527/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-17040697/80000000 : ℝ)|^8375 ≤ (12912338182509/100000000000000 : ℝ)^6327
        have hw : |(-17040697/80000000 : ℝ)|=(17040697/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5375732369/10000000000 : ℝ)|^8375 ≤ (43972628735299/100000000000000 : ℝ)^6327
        have hw : |(5375732369/10000000000 : ℝ)|=(5375732369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_box_2 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (529633673/1000000000 : ℝ)*x 0 + (2687866331/5000000000 : ℝ)*x 1 + (-532521867/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529633673/1000000000 : ℝ)^8375 ≤ (43115027149397/100000000000000 : ℝ)^6327 := by
    have hnat : (529633673 : ℕ)^8375*100000000000000^6327 ≤ 43115027149397^6327*1000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529633673 1000000000 43115027149397 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2687866331/5000000000 : ℝ)^8375 ≤ (43972631907783/100000000000000 : ℝ)^6327 := by
    have hnat : (2687866331 : ℕ)^8375*100000000000000^6327 ≤ 43972631907783^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687866331 5000000000 43972631907783 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (532521867/2500000000 : ℝ)^8375 ≤ (3228085233691/25000000000000 : ℝ)^6327 := by
    have hnat : (532521867 : ℕ)^8375*25000000000000^6327 ≤ 3228085233691^6327*2500000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532521867 2500000000 3228085233691 25000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529633673/1000000000 : ℝ), (2687866331/5000000000 : ℝ), (-532521867/2500000000 : ℝ)] ![(43115027149397/100000000000000 : ℝ), (43972631907783/100000000000000 : ℝ), (3228085233691/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529633673/1000000000 : ℝ)|^8375 ≤ (43115027149397/100000000000000 : ℝ)^6327
        have hw : |(529633673/1000000000 : ℝ)|=(529633673/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2687866331/5000000000 : ℝ)|^8375 ≤ (43972631907783/100000000000000 : ℝ)^6327
        have hw : |(2687866331/5000000000 : ℝ)|=(2687866331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-532521867/2500000000 : ℝ)|^8375 ≤ (3228085233691/25000000000000 : ℝ)^6327
        have hw : |(-532521867/2500000000 : ℝ)|=(532521867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_box_3 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4466197013/10000000000 : ℝ)*x 0 + (861517587/2000000000 : ℝ)*x 1 + (2153794183/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4466197013/10000000000 : ℝ)^8375 ≤ (34405314203703/100000000000000 : ℝ)^6327 := by
    have hnat : (4466197013 : ℕ)^8375*100000000000000^6327 ≤ 34405314203703^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4466197013 10000000000 34405314203703 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (861517587/2000000000 : ℝ)^8375 ≤ (32797340719583/100000000000000 : ℝ)^6327 := by
    have hnat : (861517587 : ℕ)^8375*100000000000000^6327 ≤ 32797340719583^6327*2000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861517587 2000000000 32797340719583 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2153794183/5000000000 : ℝ)^8375 ≤ (8199336265843/25000000000000 : ℝ)^6327 := by
    have hnat : (2153794183 : ℕ)^8375*25000000000000^6327 ≤ 8199336265843^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153794183 5000000000 8199336265843 25000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4466197013/10000000000 : ℝ), (861517587/2000000000 : ℝ), (2153794183/5000000000 : ℝ)] ![(34405314203703/100000000000000 : ℝ), (32797340719583/100000000000000 : ℝ), (8199336265843/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4466197013/10000000000 : ℝ)|^8375 ≤ (34405314203703/100000000000000 : ℝ)^6327
        have hw : |(4466197013/10000000000 : ℝ)|=(4466197013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(861517587/2000000000 : ℝ)|^8375 ≤ (32797340719583/100000000000000 : ℝ)^6327
        have hw : |(861517587/2000000000 : ℝ)|=(861517587/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2153794183/5000000000 : ℝ)|^8375 ≤ (8199336265843/25000000000000 : ℝ)^6327
        have hw : |(2153794183/5000000000 : ℝ)|=(2153794183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_box_4 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-284360257/1250000000 : ℝ)*x 0 + (1320407223/2500000000 : ℝ)*x 1 + (264081443/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (284360257/1250000000 : ℝ)^8375 ≤ (7043387010017/50000000000000 : ℝ)^6327 := by
    have hnat : (284360257 : ℕ)^8375*50000000000000^6327 ≤ 7043387010017^6327*1250000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284360257 1250000000 7043387010017 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1320407223/2500000000 : ℝ)^8375 ≤ (21478306578967/50000000000000 : ℝ)^6327 := by
    have hnat : (1320407223 : ℕ)^8375*50000000000000^6327 ≤ 21478306578967^6327*2500000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320407223 2500000000 21478306578967 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (264081443/500000000 : ℝ)^8375 ≤ (21478306406713/50000000000000 : ℝ)^6327 := by
    have hnat : (264081443 : ℕ)^8375*50000000000000^6327 ≤ 21478306406713^6327*500000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264081443 500000000 21478306406713 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-284360257/1250000000 : ℝ), (1320407223/2500000000 : ℝ), (264081443/500000000 : ℝ)] ![(7043387010017/50000000000000 : ℝ), (21478306578967/50000000000000 : ℝ), (21478306406713/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-284360257/1250000000 : ℝ)|^8375 ≤ (7043387010017/50000000000000 : ℝ)^6327
        have hw : |(-284360257/1250000000 : ℝ)|=(284360257/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1320407223/2500000000 : ℝ)|^8375 ≤ (21478306578967/50000000000000 : ℝ)^6327
        have hw : |(1320407223/2500000000 : ℝ)|=(1320407223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(264081443/500000000 : ℝ)|^8375 ≤ (21478306406713/50000000000000 : ℝ)^6327
        have hw : |(264081443/500000000 : ℝ)|=(264081443/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_box_5 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5362761323/10000000000 : ℝ)*x 0 + (-433444401/2000000000 : ℝ)*x 1 + (1320407223/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362761323/10000000000 : ℝ)^8375 ≤ (10958059613369/25000000000000 : ℝ)^6327 := by
    have hnat : (5362761323 : ℕ)^8375*25000000000000^6327 ≤ 10958059613369^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362761323 10000000000 10958059613369 25000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (433444401/2000000000 : ℝ)^8375 ≤ (412848386959/3125000000000 : ℝ)^6327 := by
    have hnat : (433444401 : ℕ)^8375*3125000000000^6327 ≤ 412848386959^6327*2000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433444401 2000000000 412848386959 3125000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1320407223/2500000000 : ℝ)^8375 ≤ (21478306578967/50000000000000 : ℝ)^6327 := by
    have hnat : (1320407223 : ℕ)^8375*50000000000000^6327 ≤ 21478306578967^6327*2500000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320407223 2500000000 21478306578967 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362761323/10000000000 : ℝ), (-433444401/2000000000 : ℝ), (1320407223/2500000000 : ℝ)] ![(10958059613369/25000000000000 : ℝ), (412848386959/3125000000000 : ℝ), (21478306578967/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362761323/10000000000 : ℝ)|^8375 ≤ (10958059613369/25000000000000 : ℝ)^6327
        have hw : |(5362761323/10000000000 : ℝ)|=(5362761323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-433444401/2000000000 : ℝ)|^8375 ≤ (412848386959/3125000000000 : ℝ)^6327
        have hw : |(-433444401/2000000000 : ℝ)|=(433444401/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1320407223/2500000000 : ℝ)|^8375 ≤ (21478306578967/50000000000000 : ℝ)^6327
        have hw : |(1320407223/2500000000 : ℝ)|=(1320407223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_box_6 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1340690317/2500000000 : ℝ)*x 0 + (5281628883/10000000000 : ℝ)*x 1 + (-216722209/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1340690317/2500000000 : ℝ)^8375 ≤ (5479029732303/12500000000000 : ℝ)^6327 := by
    have hnat : (1340690317 : ℕ)^8375*12500000000000^6327 ≤ 5479029732303^6327*2500000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340690317 2500000000 5479029732303 12500000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5281628883/10000000000 : ℝ)^8375 ≤ (42956613061041/100000000000000 : ℝ)^6327 := by
    have hnat : (5281628883 : ℕ)^8375*100000000000000^6327 ≤ 42956613061041^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281628883 10000000000 42956613061041 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216722209/1000000000 : ℝ)^8375 ≤ (165139363357/1250000000000 : ℝ)^6327 := by
    have hnat : (216722209 : ℕ)^8375*1250000000000^6327 ≤ 165139363357^6327*1000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216722209 1000000000 165139363357 1250000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1340690317/2500000000 : ℝ), (5281628883/10000000000 : ℝ), (-216722209/1000000000 : ℝ)] ![(5479029732303/12500000000000 : ℝ), (42956613061041/100000000000000 : ℝ), (165139363357/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1340690317/2500000000 : ℝ)|^8375 ≤ (5479029732303/12500000000000 : ℝ)^6327
        have hw : |(1340690317/2500000000 : ℝ)|=(1340690317/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5281628883/10000000000 : ℝ)|^8375 ≤ (42956613061041/100000000000000 : ℝ)^6327
        have hw : |(5281628883/10000000000 : ℝ)|=(5281628883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-216722209/1000000000 : ℝ)|^8375 ≤ (165139363357/1250000000000 : ℝ)^6327
        have hw : |(-216722209/1000000000 : ℝ)|=(216722209/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_box_7 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4251565427/10000000000 : ℝ)*x 0 + (4414883479/10000000000 : ℝ)*x 1 + (441488333/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4251565427/10000000000 : ℝ)^8375 ≤ (32233915607509/100000000000000 : ℝ)^6327 := by
    have hnat : (4251565427 : ℕ)^8375*100000000000000^6327 ≤ 32233915607509^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251565427 10000000000 32233915607509 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4414883479/10000000000 : ℝ)^8375 ≤ (33883042940267/100000000000000 : ℝ)^6327 := by
    have hnat : (4414883479 : ℕ)^8375*100000000000000^6327 ≤ 33883042940267^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4414883479 10000000000 33883042940267 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (441488333/1000000000 : ℝ)^8375 ≤ (16941520713289/50000000000000 : ℝ)^6327 := by
    have hnat : (441488333 : ℕ)^8375*50000000000000^6327 ≤ 16941520713289^6327*1000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441488333 1000000000 16941520713289 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4251565427/10000000000 : ℝ), (4414883479/10000000000 : ℝ), (441488333/1000000000 : ℝ)] ![(32233915607509/100000000000000 : ℝ), (33883042940267/100000000000000 : ℝ), (16941520713289/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4251565427/10000000000 : ℝ)|^8375 ≤ (32233915607509/100000000000000 : ℝ)^6327
        have hw : |(4251565427/10000000000 : ℝ)|=(4251565427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4414883479/10000000000 : ℝ)|^8375 ≤ (33883042940267/100000000000000 : ℝ)^6327
        have hw : |(4414883479/10000000000 : ℝ)|=(4414883479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(441488333/1000000000 : ℝ)|^8375 ≤ (16941520713289/50000000000000 : ℝ)^6327
        have hw : |(441488333/1000000000 : ℝ)|=(441488333/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_box_8 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-222202163/1000000000 : ℝ)*x 0 + (5217552863/10000000000 : ℝ)*x 1 + (5385344253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (222202163/1000000000 : ℝ)^8375 ≤ (1365513044563/10000000000000 : ℝ)^6327 := by
    have hnat : (222202163 : ℕ)^8375*10000000000000^6327 ≤ 1365513044563^6327*1000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222202163 1000000000 1365513044563 10000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217552863/10000000000 : ℝ)^8375 ≤ (10567034292261/25000000000000 : ℝ)^6327 := by
    have hnat : (5217552863 : ℕ)^8375*25000000000000^6327 ≤ 10567034292261^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217552863 10000000000 10567034292261 25000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5385344253/10000000000 : ℝ)^8375 ≤ (11019183092967/25000000000000 : ℝ)^6327 := by
    have hnat : (5385344253 : ℕ)^8375*25000000000000^6327 ≤ 11019183092967^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385344253 10000000000 11019183092967 25000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-222202163/1000000000 : ℝ), (5217552863/10000000000 : ℝ), (5385344253/10000000000 : ℝ)] ![(1365513044563/10000000000000 : ℝ), (10567034292261/25000000000000 : ℝ), (11019183092967/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-222202163/1000000000 : ℝ)|^8375 ≤ (1365513044563/10000000000000 : ℝ)^6327
        have hw : |(-222202163/1000000000 : ℝ)|=(222202163/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217552863/10000000000 : ℝ)|^8375 ≤ (10567034292261/25000000000000 : ℝ)^6327
        have hw : |(5217552863/10000000000 : ℝ)|=(5217552863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5385344253/10000000000 : ℝ)|^8375 ≤ (11019183092967/25000000000000 : ℝ)^6327
        have hw : |(5385344253/10000000000 : ℝ)|=(5385344253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_box_9 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5289549169/10000000000 : ℝ)*x 0 + (-212622639/1000000000 : ℝ)*x 1 + (5385343941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289549169/10000000000 : ℝ)^8375 ≤ (21520951259217/50000000000000 : ℝ)^6327 := by
    have hnat : (5289549169 : ℕ)^8375*50000000000000^6327 ≤ 21520951259217^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289549169 10000000000 21520951259217 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (212622639/1000000000 : ℝ)^8375 ≤ (12881368480193/100000000000000 : ℝ)^6327 := by
    have hnat : (212622639 : ℕ)^8375*100000000000000^6327 ≤ 12881368480193^6327*1000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212622639 1000000000 12881368480193 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5385343941/10000000000 : ℝ)^8375 ≤ (22038364495853/50000000000000 : ℝ)^6327 := by
    have hnat : (5385343941 : ℕ)^8375*50000000000000^6327 ≤ 22038364495853^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385343941 10000000000 22038364495853 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289549169/10000000000 : ℝ), (-212622639/1000000000 : ℝ), (5385343941/10000000000 : ℝ)] ![(21520951259217/50000000000000 : ℝ), (12881368480193/100000000000000 : ℝ), (22038364495853/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289549169/10000000000 : ℝ)|^8375 ≤ (21520951259217/50000000000000 : ℝ)^6327
        have hw : |(5289549169/10000000000 : ℝ)|=(5289549169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-212622639/1000000000 : ℝ)|^8375 ≤ (12881368480193/100000000000000 : ℝ)^6327
        have hw : |(-212622639/1000000000 : ℝ)|=(212622639/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5385343941/10000000000 : ℝ)|^8375 ≤ (22038364495853/50000000000000 : ℝ)^6327
        have hw : |(5385343941/10000000000 : ℝ)|=(5385343941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_box_10 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5289549121/10000000000 : ℝ)*x 0 + (2692671839/5000000000 : ℝ)*x 1 + (-212622681/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289549121/10000000000 : ℝ)^8375 ≤ (21520951000711/50000000000000 : ℝ)^6327 := by
    have hnat : (5289549121 : ℕ)^8375*50000000000000^6327 ≤ 21520951000711^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289549121 10000000000 21520951000711 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2692671839/5000000000 : ℝ)^8375 ≤ (44076726142403/100000000000000 : ℝ)^6327 := by
    have hnat : (2692671839 : ℕ)^8375*100000000000000^6327 ≤ 44076726142403^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692671839 5000000000 44076726142403 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (212622681/1000000000 : ℝ)^8375 ≤ (6440685924161/50000000000000 : ℝ)^6327 := by
    have hnat : (212622681 : ℕ)^8375*50000000000000^6327 ≤ 6440685924161^6327*1000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212622681 1000000000 6440685924161 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289549121/10000000000 : ℝ), (2692671839/5000000000 : ℝ), (-212622681/1000000000 : ℝ)] ![(21520951000711/50000000000000 : ℝ), (44076726142403/100000000000000 : ℝ), (6440685924161/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289549121/10000000000 : ℝ)|^8375 ≤ (21520951000711/50000000000000 : ℝ)^6327
        have hw : |(5289549121/10000000000 : ℝ)|=(5289549121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2692671839/5000000000 : ℝ)|^8375 ≤ (44076726142403/100000000000000 : ℝ)^6327
        have hw : |(2692671839/5000000000 : ℝ)|=(2692671839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-212622681/1000000000 : ℝ)|^8375 ≤ (6440685924161/50000000000000 : ℝ)^6327
        have hw : |(-212622681/1000000000 : ℝ)|=(212622681/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_box_11 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4487846281/10000000000 : ℝ)*x 0 + (4296622953/10000000000 : ℝ)*x 1 + (2148311497/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4487846281/10000000000 : ℝ)^8375 ≤ (6925249183359/20000000000000 : ℝ)^6327 := by
    have hnat : (4487846281 : ℕ)^8375*20000000000000^6327 ≤ 6925249183359^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487846281 10000000000 6925249183359 20000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4296622953/10000000000 : ℝ)^8375 ≤ (4085859603987/12500000000000 : ℝ)^6327 := by
    have hnat : (4296622953 : ℕ)^8375*12500000000000^6327 ≤ 4085859603987^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4296622953 10000000000 4085859603987 12500000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2148311497/5000000000 : ℝ)^8375 ≤ (3268687724477/10000000000000 : ℝ)^6327 := by
    have hnat : (2148311497 : ℕ)^8375*10000000000000^6327 ≤ 3268687724477^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148311497 5000000000 3268687724477 10000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4487846281/10000000000 : ℝ), (4296622953/10000000000 : ℝ), (2148311497/5000000000 : ℝ)] ![(6925249183359/20000000000000 : ℝ), (4085859603987/12500000000000 : ℝ), (3268687724477/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4487846281/10000000000 : ℝ)|^8375 ≤ (6925249183359/20000000000000 : ℝ)^6327
        have hw : |(4487846281/10000000000 : ℝ)|=(4487846281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4296622953/10000000000 : ℝ)|^8375 ≤ (4085859603987/12500000000000 : ℝ)^6327
        have hw : |(4296622953/10000000000 : ℝ)|=(4296622953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2148311497/5000000000 : ℝ)|^8375 ≤ (3268687724477/10000000000000 : ℝ)^6327
        have hw : |(2148311497/5000000000 : ℝ)|=(2148311497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_box_12 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1037735493/5000000000 : ℝ)*x 0 + (5438559197/10000000000 : ℝ)*x 1 + (659196567/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1037735493/5000000000 : ℝ)^8375 ≤ (12475923908329/100000000000000 : ℝ)^6327 := by
    have hnat : (1037735493 : ℕ)^8375*100000000000000^6327 ≤ 12475923908329^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037735493 5000000000 12475923908329 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438559197/10000000000 : ℝ)^8375 ≤ (44654175174607/100000000000000 : ℝ)^6327 := by
    have hnat : (5438559197 : ℕ)^8375*100000000000000^6327 ≤ 44654175174607^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438559197 10000000000 44654175174607 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (659196567/1250000000 : ℝ)^8375 ≤ (10717475224023/25000000000000 : ℝ)^6327 := by
    have hnat : (659196567 : ℕ)^8375*25000000000000^6327 ≤ 10717475224023^6327*1250000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659196567 1250000000 10717475224023 25000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1037735493/5000000000 : ℝ), (5438559197/10000000000 : ℝ), (659196567/1250000000 : ℝ)] ![(12475923908329/100000000000000 : ℝ), (44654175174607/100000000000000 : ℝ), (10717475224023/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1037735493/5000000000 : ℝ)|^8375 ≤ (12475923908329/100000000000000 : ℝ)^6327
        have hw : |(-1037735493/5000000000 : ℝ)|=(1037735493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438559197/10000000000 : ℝ)|^8375 ≤ (44654175174607/100000000000000 : ℝ)^6327
        have hw : |(5438559197/10000000000 : ℝ)|=(5438559197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(659196567/1250000000 : ℝ)|^8375 ≤ (10717475224023/25000000000000 : ℝ)^6327
        have hw : |(659196567/1250000000 : ℝ)|=(659196567/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_box_13 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5368445551/10000000000 : ℝ)*x 0 + (-2170344693/10000000000 : ℝ)*x 1 + (2636786279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368445551/10000000000 : ℝ)^8375 ≤ (21946873688783/50000000000000 : ℝ)^6327 := by
    have hnat : (5368445551 : ℕ)^8375*50000000000000^6327 ≤ 21946873688783^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368445551 10000000000 21946873688783 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2170344693/10000000000 : ℝ)^8375 ≤ (6618175741757/50000000000000 : ℝ)^6327 := by
    have hnat : (2170344693 : ℕ)^8375*50000000000000^6327 ≤ 6618175741757^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170344693 10000000000 6618175741757 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2636786279/5000000000 : ℝ)^8375 ≤ (5358737641603/12500000000000 : ℝ)^6327 := by
    have hnat : (2636786279 : ℕ)^8375*12500000000000^6327 ≤ 5358737641603^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636786279 5000000000 5358737641603 12500000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368445551/10000000000 : ℝ), (-2170344693/10000000000 : ℝ), (2636786279/5000000000 : ℝ)] ![(21946873688783/50000000000000 : ℝ), (6618175741757/50000000000000 : ℝ), (5358737641603/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368445551/10000000000 : ℝ)|^8375 ≤ (21946873688783/50000000000000 : ℝ)^6327
        have hw : |(5368445551/10000000000 : ℝ)|=(5368445551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2170344693/10000000000 : ℝ)|^8375 ≤ (6618175741757/50000000000000 : ℝ)^6327
        have hw : |(-2170344693/10000000000 : ℝ)|=(2170344693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2636786279/5000000000 : ℝ)|^8375 ≤ (5358737641603/12500000000000 : ℝ)^6327
        have hw : |(2636786279/5000000000 : ℝ)|=(2636786279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_box_14 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5368445563/10000000000 : ℝ)*x 0 + (2636786559/5000000000 : ℝ)*x 1 + (-2170343929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368445563/10000000000 : ℝ)^8375 ≤ (548671843843/1250000000000 : ℝ)^6327 := by
    have hnat : (5368445563 : ℕ)^8375*1250000000000^6327 ≤ 548671843843^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368445563 10000000000 548671843843 1250000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2636786559/5000000000 : ℝ)^8375 ≤ (42869907158733/100000000000000 : ℝ)^6327 := by
    have hnat : (2636786559 : ℕ)^8375*100000000000000^6327 ≤ 42869907158733^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636786559 5000000000 42869907158733 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2170343929/10000000000 : ℝ)^8375 ≤ (13236345315861/100000000000000 : ℝ)^6327 := by
    have hnat : (2170343929 : ℕ)^8375*100000000000000^6327 ≤ 13236345315861^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170343929 10000000000 13236345315861 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368445563/10000000000 : ℝ), (2636786559/5000000000 : ℝ), (-2170343929/10000000000 : ℝ)] ![(548671843843/1250000000000 : ℝ), (42869907158733/100000000000000 : ℝ), (13236345315861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368445563/10000000000 : ℝ)|^8375 ≤ (548671843843/1250000000000 : ℝ)^6327
        have hw : |(5368445563/10000000000 : ℝ)|=(5368445563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2636786559/5000000000 : ℝ)|^8375 ≤ (42869907158733/100000000000000 : ℝ)^6327
        have hw : |(2636786559/5000000000 : ℝ)|=(2636786559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2170343929/10000000000 : ℝ)|^8375 ≤ (13236345315861/100000000000000 : ℝ)^6327
        have hw : |(-2170343929/10000000000 : ℝ)|=(2170343929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_box_15 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2116479763/5000000000 : ℝ)*x 0 + (55300801/125000000 : ℝ)*x 1 + (4424063787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2116479763/5000000000 : ℝ)^8375 ≤ (32047323242117/100000000000000 : ℝ)^6327 := by
    have hnat : (2116479763 : ℕ)^8375*100000000000000^6327 ≤ 32047323242117^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116479763 5000000000 32047323242117 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (55300801/125000000 : ℝ)^8375 ≤ (33976339864137/100000000000000 : ℝ)^6327 := by
    have hnat : (55300801 : ℕ)^8375*100000000000000^6327 ≤ 33976339864137^6327*125000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55300801 125000000 33976339864137 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4424063787/10000000000 : ℝ)^8375 ≤ (33976336885553/100000000000000 : ℝ)^6327 := by
    have hnat : (4424063787 : ℕ)^8375*100000000000000^6327 ≤ 33976336885553^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4424063787 10000000000 33976336885553 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2116479763/5000000000 : ℝ), (55300801/125000000 : ℝ), (4424063787/10000000000 : ℝ)] ![(32047323242117/100000000000000 : ℝ), (33976339864137/100000000000000 : ℝ), (33976336885553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2116479763/5000000000 : ℝ)|^8375 ≤ (32047323242117/100000000000000 : ℝ)^6327
        have hw : |(2116479763/5000000000 : ℝ)|=(2116479763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(55300801/125000000 : ℝ)|^8375 ≤ (33976339864137/100000000000000 : ℝ)^6327
        have hw : |(55300801/125000000 : ℝ)|=(55300801/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4424063787/10000000000 : ℝ)|^8375 ≤ (33976336885553/100000000000000 : ℝ)^6327
        have hw : |(4424063787/10000000000 : ℝ)|=(4424063787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1182_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150254753/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14071/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2281/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(15559/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(5933/10000 : ℝ) ∧ (7993/10000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (41607/50000 : ℝ) := by
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
  have lower0 : (2281/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14071/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2281/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14071/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2281/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14071/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2281/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14071/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2281/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14071/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2281/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2281/20000 : ℝ) ^ (4187/1024 : ℝ) ≤ (3487609704374499/25000000000000000000 : ℝ) := by
    have hpowers : (2281/20000 : ℝ)^4187 ≤ (3487609704374499/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2281 : ℕ)^4187*25000000000000000000^1024 ≤ 3487609704374499^1024*20000^4187 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2281 20000 3487609704374499 25000000000000000000 4187 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2281/20000 : ℝ)) (X := (3487609704374499/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14071/100000 : ℝ) ^ (4187/1024 : ℝ) ≤ (16465840010382847/50000000000000000000 : ℝ) := by
    have hpowers : (14071/100000 : ℝ)^4187 ≤ (16465840010382847/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14071 : ℕ)^4187*50000000000000000000^1024 ≤ 16465840010382847^1024*100000^4187 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14071 100000 16465840010382847 50000000000000000000 4187 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14071/100000 : ℝ)) (X := (16465840010382847/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503487609704374499/12500000000000000000 : ℝ) ≤ (1000068229014213/1000000000000000 : ℝ) ^ (4187/1024 : ℝ) := by
    have hpowers : (12503487609704374499/12500000000000000000 : ℝ)^1024 ≤ (1000068229014213/1000000000000000 : ℝ)^4187 := by
      have hnat : (12503487609704374499 : ℕ)^1024*1000000000000000^4187 ≤ 1000068229014213^4187*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503487609704374499 12500000000000000000 1000068229014213 1000000000000000 1024 4187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000068229014213/1000000000000000 : ℝ)) (X := (12503487609704374499/12500000000000000000 : ℝ)) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004688211883826369/10000000000000000000 : ℝ) ≤ (10001146376661417/10000000000000000 : ℝ) ^ (4187/1024 : ℝ) := by
    have hpowers : (10004688211883826369/10000000000000000000 : ℝ)^1024 ≤ (10001146376661417/10000000000000000 : ℝ)^4187 := by
      have hnat : (10004688211883826369 : ℕ)^1024*10000000000000000^4187 ≤ 10001146376661417^4187*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004688211883826369 10000000000000000000 10001146376661417 10000000000000000 1024 4187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001146376661417/10000000000000000 : ℝ)) (X := (10004688211883826369/10000000000000000000 : ℝ)) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016465840010382847/25000000000000000000 : ℝ) ≤ (312550326974397/312500000000000 : ℝ) ^ (4187/1024 : ℝ) := by
    have hpowers : (25016465840010382847/25000000000000000000 : ℝ)^1024 ≤ (312550326974397/312500000000000 : ℝ)^4187 := by
      have hnat : (25016465840010382847 : ℕ)^1024*312500000000000^4187 ≤ 312550326974397^4187*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016465840010382847 25000000000000000000 312550326974397 312500000000000 1024 4187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312550326974397/312500000000000 : ℝ)) (X := (25016465840010382847/25000000000000000000 : ℝ)) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3487609704374499/25000000000000000000 : ℝ) ≤ ((2665123317201398211/2666000000000000000 : ℝ)+2*(464086519287/266600000000000 : ℝ)*(2281/20000 : ℝ))^(4187/1024 : ℝ) := by
    rw [show (2665123317201398211/2666000000000000000 : ℝ)+2*(464086519287/266600000000000 : ℝ)*(2281/20000 : ℝ)=(1000068229014213/1000000000000000 : ℝ) by norm_num, show 1+2*(3487609704374499/25000000000000000000 : ℝ)=(12503487609704374499/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16465840010382847/50000000000000000000 : ℝ)+(3487609704374499/25000000000000000000 : ℝ) ≤ ((2665123317201398211/2666000000000000000 : ℝ)+(464086519287/266600000000000 : ℝ)*((14071/100000 : ℝ)+(2281/20000 : ℝ)))^(4187/1024 : ℝ) := by
    rw [show (2665123317201398211/2666000000000000000 : ℝ)+(464086519287/266600000000000 : ℝ)*((14071/100000 : ℝ)+(2281/20000 : ℝ))=(10001146376661417/10000000000000000 : ℝ) by norm_num, show 1+(16465840010382847/50000000000000000000 : ℝ)+(3487609704374499/25000000000000000000 : ℝ)=(10004688211883826369/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16465840010382847/50000000000000000000 : ℝ) ≤ ((2665123317201398211/2666000000000000000 : ℝ)+2*(464086519287/266600000000000 : ℝ)*(14071/100000 : ℝ))^(4187/1024 : ℝ) := by
    rw [show (2665123317201398211/2666000000000000000 : ℝ)+2*(464086519287/266600000000000 : ℝ)*(14071/100000 : ℝ)=(312550326974397/312500000000000 : ℝ) by norm_num, show 1+2*(16465840010382847/50000000000000000000 : ℝ)=(25016465840010382847/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2665123317201398211/2666000000000000000 : ℝ)*(X 1 0+X 2 0)+(464086519287/266600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4187/1024 : ℝ)) (lo := (2281/20000 : ℝ)) (hi := (14071/100000 : ℝ)) (c := (2665123317201398211/2666000000000000000 : ℝ)) (alpha := (464086519287/266600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2665123317201398211/2666000000000000000 : ℝ)*(X 0 1+X 2 1)+(464086519287/266600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4187/1024 : ℝ)) (lo := (2281/20000 : ℝ)) (hi := (14071/100000 : ℝ)) (c := (2665123317201398211/2666000000000000000 : ℝ)) (alpha := (464086519287/266600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2665123317201398211/2666000000000000000 : ℝ)*(X 0 2+X 1 2)+(464086519287/266600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4187/1024 : ℝ)) (lo := (2281/20000 : ℝ)) (hi := (14071/100000 : ℝ)) (c := (2665123317201398211/2666000000000000000 : ℝ)) (alpha := (464086519287/266600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2022315241/10000000000 : ℝ)*X 0 0+(2687866411/5000000000 : ℝ)*X 0 1+(5375732773/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((8275527/15625000 : ℝ)*X 1 0+(-17040697/80000000 : ℝ)*X 1 1+(5375732369/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((529633673/1000000000 : ℝ)*X 2 0+(2687866331/5000000000 : ℝ)*X 2 1+(-532521867/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4466197013/10000000000 : ℝ)*X 0 0+(861517587/2000000000 : ℝ)*X 0 1+(2153794183/5000000000 : ℝ)*X 0 2+(4466197013/10000000000 : ℝ)*X 1 0+(861517587/2000000000 : ℝ)*X 1 1+(2153794183/5000000000 : ℝ)*X 1 2+(4466197013/10000000000 : ℝ)*X 2 0+(861517587/2000000000 : ℝ)*X 2 1+(2153794183/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-284360257/1250000000 : ℝ)*X 0 0+(1320407223/2500000000 : ℝ)*X 0 1+(264081443/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5362761323/10000000000 : ℝ)*X 1 0+(-433444401/2000000000 : ℝ)*X 1 1+(1320407223/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1340690317/2500000000 : ℝ)*X 2 0+(5281628883/10000000000 : ℝ)*X 2 1+(-216722209/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4251565427/10000000000 : ℝ)*X 0 0+(4414883479/10000000000 : ℝ)*X 0 1+(441488333/1000000000 : ℝ)*X 0 2+(4251565427/10000000000 : ℝ)*X 1 0+(4414883479/10000000000 : ℝ)*X 1 1+(441488333/1000000000 : ℝ)*X 1 2+(4251565427/10000000000 : ℝ)*X 2 0+(4414883479/10000000000 : ℝ)*X 2 1+(441488333/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-222202163/1000000000 : ℝ)*X 0 0+(5217552863/10000000000 : ℝ)*X 0 1+(5385344253/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5289549169/10000000000 : ℝ)*X 1 0+(-212622639/1000000000 : ℝ)*X 1 1+(5385343941/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5289549121/10000000000 : ℝ)*X 2 0+(2692671839/5000000000 : ℝ)*X 2 1+(-212622681/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4487846281/10000000000 : ℝ)*X 0 0+(4296622953/10000000000 : ℝ)*X 0 1+(2148311497/5000000000 : ℝ)*X 0 2+(4487846281/10000000000 : ℝ)*X 1 0+(4296622953/10000000000 : ℝ)*X 1 1+(2148311497/5000000000 : ℝ)*X 1 2+(4487846281/10000000000 : ℝ)*X 2 0+(4296622953/10000000000 : ℝ)*X 2 1+(2148311497/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1037735493/5000000000 : ℝ)*X 0 0+(5438559197/10000000000 : ℝ)*X 0 1+(659196567/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5368445551/10000000000 : ℝ)*X 1 0+(-2170344693/10000000000 : ℝ)*X 1 1+(2636786279/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5368445563/10000000000 : ℝ)*X 2 0+(2636786559/5000000000 : ℝ)*X 2 1+(-2170343929/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2116479763/5000000000 : ℝ)*X 0 0+(55300801/125000000 : ℝ)*X 0 1+(4424063787/10000000000 : ℝ)*X 0 2+(2116479763/5000000000 : ℝ)*X 1 0+(55300801/125000000 : ℝ)*X 1 1+(4424063787/10000000000 : ℝ)*X 1 2+(2116479763/5000000000 : ℝ)*X 2 0+(55300801/125000000 : ℝ)*X 2 1+(4424063787/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15559/25000 : ℝ) ≤ (-82957815195654336533444965881501/133300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17206457/50000000000000 : ℝ)*(upper1) + (35942229/100000000000000 : ℝ)*(upper3) + (36406147/100000000000000 : ℝ)*(lower4) + (154347/1562500000000 : ℝ)*(lower5) + (3953705431023797/100000000000000 : ℝ)*(major0) + (3953705431023797/100000000000000 : ℝ)*(major1) + (3953705431023797/100000000000000 : ℝ)*(major2) + (2049221531/100000000000000 : ℝ)*(sp3) + (5296820817356729/100000000000000 : ℝ)*(sp4) + (5296801676506013/100000000000000 : ℝ)*(sp5) + (2648407236373321/50000000000000 : ℝ)*(sp6) + (263133263542821/10000000000000 : ℝ)*(sp7) + (4785212679/25000000000000 : ℝ)*(sp13) + (3172305043/50000000000000 : ℝ)*(sp14) + (2631334684649741/100000000000000 : ℝ)*(f.failure) + (5296820817356729/100000000000000 : ℝ)*(f.sum) + (35640603421431/13330000000000000000000000000 : ℝ)*base66 + (127179212835413457/8600000000000000000000000000000 : ℝ)*base67 + (231300273854386543/8600000000000000000000000000000 : ℝ)*base70 + (98413959108413457/8600000000000000000000000000000 : ℝ)*base71 + (16585309195479/13330000000000000000000000000 : ℝ)*base73 + (487091623436786543/8600000000000000000000000000000 : ℝ)*base76 + (137219646581013457/8600000000000000000000000000000 : ℝ)*base77 + (131541865847813457/8600000000000000000000000000000 : ℝ)*base79 + (1541184526294021/13330000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (25468973/10000000000000000000000 : ℝ)*base89 + (25468973/10000000000000000000000 : ℝ)*base91 + (25468973/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (5933/10000 : ℝ) ≤ (19772419487057926510036626622509/33325000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (37164393/20000000000000 : ℝ)*(lower1) + (173387299/100000000000000 : ℝ)*(lower4) + (80481503/25000000000000 : ℝ)*(lower5) + (2009266132757827/50000000000000 : ℝ)*(major0) + (2009266132757827/50000000000000 : ℝ)*(major1) + (2009266132757827/50000000000000 : ℝ)*(major2) + (2671389765828073/50000000000000 : ℝ)*(sp0) + (2671345572019201/50000000000000 : ℝ)*(sp1) + (5342801660073887/100000000000000 : ℝ)*(sp2) + (668619285856887/25000000000000 : ℝ)*(sp3) + (3103809439/50000000000000 : ℝ)*(sp6) + (2156082967/100000000000000 : ℝ)*(sp7) + (58361827181/50000000000000 : ℝ)*(sp9) + (14168018309/50000000000000 : ℝ)*(sp12) + (1337239649755257/50000000000000 : ℝ)*(f.failure) + (1068561573538553/20000000000000 : ℝ)*(f.sum) + (14700113300743/3332500000000000000000000000 : ℝ)*base66 + (70617730687910887/4300000000000000000000000000000 : ℝ)*base67 + (9868588640010887/4300000000000000000000000000000 : ℝ)*base69 + (18538657195910887/4300000000000000000000000000000 : ℝ)*base71 + (33409060918127/3332500000000000000000000000 : ℝ)*base73 + (27106605481810887/4300000000000000000000000000000 : ℝ)*base75 + (8342513630889113/4300000000000000000000000000000 : ℝ)*base78 + (32101982634910887/4300000000000000000000000000000 : ℝ)*base79 + (56713223598081/6665000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (49013479/5000000000000000000000 : ℝ)*base90 + (49013479/5000000000000000000000 : ℝ)*base92 + (49013479/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (7993/10000 : ℝ) ≤ (53274828430554980496952510648983/66650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (154009359/50000000000000 : ℝ)*(upper0) + (141761461/100000000000000 : ℝ)*(upper1) + (3402749/5000000000000 : ℝ)*(upper2) + (381890163/100000000000000 : ℝ)*(lower5) + (4486003374843049/100000000000000 : ℝ)*(major0) + (4486003374843049/100000000000000 : ℝ)*(major1) + (4486003374843049/100000000000000 : ℝ)*(major2) + (3632095761/6250000000000 : ℝ)*(sp1) + (1880596357/50000000000000 : ℝ)*(sp3) + (1205696467/12500000000000 : ℝ)*(sp4) + (5959754713169711/100000000000000 : ℝ)*(sp8) + (5959706245209271/100000000000000 : ℝ)*(sp9) + (5959764358741447/100000000000000 : ℝ)*(sp10) + (2985594554517837/100000000000000 : ℝ)*(sp11) + (373199789463819/12500000000000 : ℝ)*(f.failure) + (5959764358741447/100000000000000 : ℝ)*(f.sum) + (3397954477173/13330000000000000000000000000 : ℝ)*base65 + (101460416910497269/8600000000000000000000000000000 : ℝ)*base67 + (19544696325097269/8600000000000000000000000000000 : ℝ)*base69 + (58548160973297269/8600000000000000000000000000000 : ℝ)*base71 + (390796315352067/13330000000000000000000000000 : ℝ)*base74 + (65144819361897269/8600000000000000000000000000000 : ℝ)*base75 + (26146362304497269/8600000000000000000000000000000 : ℝ)*base77 + (375744062554102731/8600000000000000000000000000000 : ℝ)*base80 + (54658939656497/13330000000000000000000000000 : ℝ)*base82 + (13781707/1250000000000000000000 : ℝ)*base89 + (13781707/1250000000000000000000 : ℝ)*base91 + (13781707/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-41607/50000 : ℝ) ≤ (-11092049909338464928769282652819/13330000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (88964127/25000000000000 : ℝ)*(lower0) + (134307881/100000000000000 : ℝ)*(lower2) + (65922303/100000000000000 : ℝ)*(upper3) + (145378729/20000000000000 : ℝ)*(upper5) + (452115687379243/10000000000000 : ℝ)*(major0) + (452115687379243/10000000000000 : ℝ)*(major1) + (452115687379243/10000000000000 : ℝ)*(major2) + (12476469723/100000000000000 : ℝ)*(sp0) + (22348612947/10000000000000 : ℝ)*(sp5) + (96722465229/100000000000000 : ℝ)*(sp7) + (151526102075863/2500000000000 : ℝ)*(sp12) + (6060833073374773/100000000000000 : ℝ)*(sp13) + (3030528279752121/50000000000000 : ℝ)*(sp14) + (3008897524653483/100000000000000 : ℝ)*(sp15) + (376124280889839/12500000000000 : ℝ)*(f.failure) + (3030528279752121/50000000000000 : ℝ)*(f.sum) + (3377142316367/1333000000000000000000000000 : ℝ)*base65 + (7586940274300783/860000000000000000000000000000 : ℝ)*base67 + (10621917931120783/860000000000000000000000000000 : ℝ)*base69 + (1230355493119217/860000000000000000000000000000 : ℝ)*base72 + (8230327689101/266600000000000000000000000 : ℝ)*base73 + (1299102767379217/860000000000000000000000000000 : ℝ)*base76 + (17611724625700783/860000000000000000000000000000 : ℝ)*base77 + (11901269757700783/860000000000000000000000000000 : ℝ)*base79 + (287750358621/166625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (4154767/1250000000000000000000 : ℝ)*base89 + (4154767/1250000000000000000000 : ℝ)*base91 + (4154767/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1182_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150254753/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14071/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2281/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15559/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(5933/10000 : ℝ) else (7993/10000 : ℝ) ≤ X j i ∧ X j i ≤ (41607/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1182_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1182_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150254753/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14071/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2281/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15559/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(5933/10000 : ℝ) else (7993/10000 : ℝ) ≤ X j i ∧ X j i ≤ (41607/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1182_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150254753/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14071/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2281/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15559/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(5933/10000 : ℝ) else (7993/10000 : ℝ) ≤ X j i ∧ X j i ≤ (41607/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1182_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

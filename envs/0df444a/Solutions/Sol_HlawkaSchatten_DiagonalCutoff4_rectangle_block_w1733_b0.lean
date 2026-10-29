-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1733_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:07:24.81899+00:00
-- url     : https://prove2.me/submissions/71eed143-5a40-4fa8-8e47-460694969427

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
theorem support_rectangle_w1733_s0_0 (p : ℝ) (hpa : (5487/1024 : ℝ) ≤ p) (hpb : p ≤ (5503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-315854193/2500000000 : ℝ)*x 0 + (2843465161/5000000000 : ℝ)*x 1 + (4949375829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (315854193/2500000000 : ℝ)^5503 ≤ (3936497899773/50000000000000 : ℝ)^4479 := by
    have hnat : (315854193 : ℕ)^5503*50000000000000^4479 ≤ 3936497899773^4479*2500000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315854193 2500000000 3936497899773 50000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2843465161/5000000000 : ℝ)^5503 ≤ (12496186547867/25000000000000 : ℝ)^4479 := by
    have hnat : (2843465161 : ℕ)^5503*25000000000000^4479 ≤ 12496186547867^4479*5000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2843465161 5000000000 12496186547867 25000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4949375829/10000000000 : ℝ)^5503 ≤ (42142257996113/100000000000000 : ℝ)^4479 := by
    have hnat : (4949375829 : ℕ)^5503*100000000000000^4479 ≤ 42142257996113^4479*10000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4949375829 10000000000 42142257996113 100000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5503/1024 : ℝ)) 5503 4479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-315854193/2500000000 : ℝ), (2843465161/5000000000 : ℝ), (4949375829/10000000000 : ℝ)] ![(3936497899773/50000000000000 : ℝ), (12496186547867/25000000000000 : ℝ), (42142257996113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-315854193/2500000000 : ℝ)|^5503 ≤ (3936497899773/50000000000000 : ℝ)^4479
        have hw : |(-315854193/2500000000 : ℝ)|=(315854193/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2843465161/5000000000 : ℝ)|^5503 ≤ (12496186547867/25000000000000 : ℝ)^4479
        have hw : |(2843465161/5000000000 : ℝ)|=(2843465161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4949375829/10000000000 : ℝ)|^5503 ≤ (42142257996113/100000000000000 : ℝ)^4479
        have hw : |(4949375829/10000000000 : ℝ)|=(4949375829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1733_s0_1 (p : ℝ) (hpa : (5487/1024 : ℝ) ≤ p) (hpb : p ≤ (5503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (107852027/200000000 : ℝ)*x 0 + (-103917517/625000000 : ℝ)*x 1 + (1237343991/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107852027/200000000 : ℝ)^5503 ≤ (23412694139/50000000000 : ℝ)^4479 := by
    have hnat : (107852027 : ℕ)^5503*50000000000^4479 ≤ 23412694139^4479*200000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107852027 200000000 23412694139 50000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103917517/625000000 : ℝ)^5503 ≤ (11032352297/100000000000 : ℝ)^4479 := by
    have hnat : (103917517 : ℕ)^5503*100000000000^4479 ≤ 11032352297^4479*625000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103917517 625000000 11032352297 100000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1237343991/2500000000 : ℝ)^5503 ≤ (42142259408389/100000000000000 : ℝ)^4479 := by
    have hnat : (1237343991 : ℕ)^5503*100000000000000^4479 ≤ 42142259408389^4479*2500000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1237343991 2500000000 42142259408389 100000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5503/1024 : ℝ)) 5503 4479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107852027/200000000 : ℝ), (-103917517/625000000 : ℝ), (1237343991/2500000000 : ℝ)] ![(23412694139/50000000000 : ℝ), (11032352297/100000000000 : ℝ), (42142259408389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107852027/200000000 : ℝ)|^5503 ≤ (23412694139/50000000000 : ℝ)^4479
        have hw : |(107852027/200000000 : ℝ)|=(107852027/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-103917517/625000000 : ℝ)|^5503 ≤ (11032352297/100000000000 : ℝ)^4479
        have hw : |(-103917517/625000000 : ℝ)|=(103917517/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1237343991/2500000000 : ℝ)|^5503 ≤ (42142259408389/100000000000000 : ℝ)^4479
        have hw : |(1237343991/2500000000 : ℝ)|=(1237343991/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1733_s0_2 (p : ℝ) (hpa : (5487/1024 : ℝ) ≤ p) (hpb : p ≤ (5503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5392600961/10000000000 : ℝ)*x 0 + (989875249/2000000000 : ℝ)*x 1 + (-1662680421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5392600961/10000000000 : ℝ)^5503 ≤ (46825384127971/100000000000000 : ℝ)^4479 := by
    have hnat : (5392600961 : ℕ)^5503*100000000000000^4479 ≤ 46825384127971^4479*10000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392600961 10000000000 46825384127971 100000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (989875249/2000000000 : ℝ)^5503 ≤ (8428452469603/20000000000000 : ℝ)^4479 := by
    have hnat : (989875249 : ℕ)^5503*20000000000000^4479 ≤ 8428452469603^4479*2000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      989875249 2000000000 8428452469603 20000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1662680421/10000000000 : ℝ)^5503 ≤ (11032353511687/100000000000000 : ℝ)^4479 := by
    have hnat : (1662680421 : ℕ)^5503*100000000000000^4479 ≤ 11032353511687^4479*10000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1662680421 10000000000 11032353511687 100000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5503/1024 : ℝ)) 5503 4479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5392600961/10000000000 : ℝ), (989875249/2000000000 : ℝ), (-1662680421/10000000000 : ℝ)] ![(46825384127971/100000000000000 : ℝ), (8428452469603/20000000000000 : ℝ), (11032353511687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5392600961/10000000000 : ℝ)|^5503 ≤ (46825384127971/100000000000000 : ℝ)^4479
        have hw : |(5392600961/10000000000 : ℝ)|=(5392600961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(989875249/2000000000 : ℝ)|^5503 ≤ (8428452469603/20000000000000 : ℝ)^4479
        have hw : |(989875249/2000000000 : ℝ)|=(989875249/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1662680421/10000000000 : ℝ)|^5503 ≤ (11032353511687/100000000000000 : ℝ)^4479
        have hw : |(-1662680421/10000000000 : ℝ)|=(1662680421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1733_s0_3 (p : ℝ) (hpa : (5487/1024 : ℝ) ≤ p) (hpb : p ≤ (5503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (800660633/2000000000 : ℝ)*x 0 + (1484328701/5000000000 : ℝ)*x 1 + (1306107889/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (800660633/2000000000 : ℝ)^5503 ≤ (32473000154019/100000000000000 : ℝ)^4479 := by
    have hnat : (800660633 : ℕ)^5503*100000000000000^4479 ≤ 32473000154019^4479*2000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      800660633 2000000000 32473000154019 100000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1484328701/5000000000 : ℝ)^5503 ≤ (1124463785269/5000000000000 : ℝ)^4479 := by
    have hnat : (1484328701 : ℕ)^5503*5000000000000^4479 ≤ 1124463785269^4479*5000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1484328701 5000000000 1124463785269 5000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1306107889/2500000000 : ℝ)^5503 ≤ (45037724137061/100000000000000 : ℝ)^4479 := by
    have hnat : (1306107889 : ℕ)^5503*100000000000000^4479 ≤ 45037724137061^4479*2500000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306107889 2500000000 45037724137061 100000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5503/1024 : ℝ)) 5503 4479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(800660633/2000000000 : ℝ), (1484328701/5000000000 : ℝ), (1306107889/2500000000 : ℝ)] ![(32473000154019/100000000000000 : ℝ), (1124463785269/5000000000000 : ℝ), (45037724137061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(800660633/2000000000 : ℝ)|^5503 ≤ (32473000154019/100000000000000 : ℝ)^4479
        have hw : |(800660633/2000000000 : ℝ)|=(800660633/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1484328701/5000000000 : ℝ)|^5503 ≤ (1124463785269/5000000000000 : ℝ)^4479
        have hw : |(1484328701/5000000000 : ℝ)|=(1484328701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1306107889/2500000000 : ℝ)|^5503 ≤ (45037724137061/100000000000000 : ℝ)^4479
        have hw : |(1306107889/2500000000 : ℝ)|=(1306107889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1733_s0_4 (p : ℝ) (hpa : (5487/1024 : ℝ) ≤ p) (hpb : p ≤ (5503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-316300073/2500000000 : ℝ)*x 0 + (993736443/2000000000 : ℝ)*x 1 + (283347319/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (316300073/2500000000 : ℝ)^5503 ≤ (3943326471427/50000000000000 : ℝ)^4479 := by
    have hnat : (316300073 : ℕ)^5503*50000000000000^4479 ≤ 3943326471427^4479*2500000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      316300073 2500000000 3943326471427 50000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (993736443/2000000000 : ℝ)^5503 ≤ (21172158968041/50000000000000 : ℝ)^4479 := by
    have hnat : (993736443 : ℕ)^5503*50000000000000^4479 ≤ 21172158968041^4479*2000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      993736443 2000000000 21172158968041 50000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (283347319/500000000 : ℝ)^5503 ≤ (6221128637887/12500000000000 : ℝ)^4479 := by
    have hnat : (283347319 : ℕ)^5503*12500000000000^4479 ≤ 6221128637887^4479*500000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283347319 500000000 6221128637887 12500000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5503/1024 : ℝ)) 5503 4479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-316300073/2500000000 : ℝ), (993736443/2000000000 : ℝ), (283347319/500000000 : ℝ)] ![(3943326471427/50000000000000 : ℝ), (21172158968041/50000000000000 : ℝ), (6221128637887/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-316300073/2500000000 : ℝ)|^5503 ≤ (3943326471427/50000000000000 : ℝ)^4479
        have hw : |(-316300073/2500000000 : ℝ)|=(316300073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(993736443/2000000000 : ℝ)|^5503 ≤ (21172158968041/50000000000000 : ℝ)^4479
        have hw : |(993736443/2000000000 : ℝ)|=(993736443/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(283347319/500000000 : ℝ)|^5503 ≤ (6221128637887/12500000000000 : ℝ)^4479
        have hw : |(283347319/500000000 : ℝ)|=(283347319/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1733_s0_5 (p : ℝ) (hpa : (5487/1024 : ℝ) ≤ p) (hpb : p ≤ (5503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2597190759/5000000000 : ℝ)*x 0 + (-945110169/10000000000 : ℝ)*x 1 + (2833473311/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2597190759/5000000000 : ℝ)^5503 ≤ (44719659927309/100000000000000 : ℝ)^4479 := by
    have hnat : (2597190759 : ℕ)^5503*100000000000000^4479 ≤ 44719659927309^4479*5000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597190759 5000000000 44719659927309 100000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (945110169/10000000000 : ℝ)^5503 ≤ (172228385929/3125000000000 : ℝ)^4479 := by
    have hnat : (945110169 : ℕ)^5503*3125000000000^4479 ≤ 172228385929^4479*10000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      945110169 10000000000 172228385929 3125000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2833473311/5000000000 : ℝ)^5503 ≤ (24884515857159/50000000000000 : ℝ)^4479 := by
    have hnat : (2833473311 : ℕ)^5503*50000000000000^4479 ≤ 24884515857159^4479*5000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2833473311 5000000000 24884515857159 50000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5503/1024 : ℝ)) 5503 4479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2597190759/5000000000 : ℝ), (-945110169/10000000000 : ℝ), (2833473311/5000000000 : ℝ)] ![(44719659927309/100000000000000 : ℝ), (172228385929/3125000000000 : ℝ), (24884515857159/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2597190759/5000000000 : ℝ)|^5503 ≤ (44719659927309/100000000000000 : ℝ)^4479
        have hw : |(2597190759/5000000000 : ℝ)|=(2597190759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-945110169/10000000000 : ℝ)|^5503 ≤ (172228385929/3125000000000 : ℝ)^4479
        have hw : |(-945110169/10000000000 : ℝ)|=(945110169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2833473311/5000000000 : ℝ)|^5503 ≤ (24884515857159/50000000000000 : ℝ)^4479
        have hw : |(2833473311/5000000000 : ℝ)|=(2833473311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1733_s0_6 (p : ℝ) (hpa : (5487/1024 : ℝ) ≤ p) (hpb : p ≤ (5503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (649297727/1250000000 : ℝ)*x 0 + (566694639/1000000000 : ℝ)*x 1 + (-945110077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (649297727/1250000000 : ℝ)^5503 ≤ (11179915769851/25000000000000 : ℝ)^4479 := by
    have hnat : (649297727 : ℕ)^5503*25000000000000^4479 ≤ 11179915769851^4479*1250000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649297727 1250000000 11179915769851 25000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (566694639/1000000000 : ℝ)^5503 ≤ (49769029210997/100000000000000 : ℝ)^4479 := by
    have hnat : (566694639 : ℕ)^5503*100000000000000^4479 ≤ 49769029210997^4479*1000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566694639 1000000000 49769029210997 100000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (945110077/10000000000 : ℝ)^5503 ≤ (5511307690587/100000000000000 : ℝ)^4479 := by
    have hnat : (945110077 : ℕ)^5503*100000000000000^4479 ≤ 5511307690587^4479*10000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      945110077 10000000000 5511307690587 100000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5503/1024 : ℝ)) 5503 4479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(649297727/1250000000 : ℝ), (566694639/1000000000 : ℝ), (-945110077/10000000000 : ℝ)] ![(11179915769851/25000000000000 : ℝ), (49769029210997/100000000000000 : ℝ), (5511307690587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(649297727/1250000000 : ℝ)|^5503 ≤ (11179915769851/25000000000000 : ℝ)^4479
        have hw : |(649297727/1250000000 : ℝ)|=(649297727/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(566694639/1000000000 : ℝ)|^5503 ≤ (49769029210997/100000000000000 : ℝ)^4479
        have hw : |(566694639/1000000000 : ℝ)|=(566694639/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-945110077/10000000000 : ℝ)|^5503 ≤ (5511307690587/100000000000000 : ℝ)^4479
        have hw : |(-945110077/10000000000 : ℝ)|=(945110077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1733_s0_7 (p : ℝ) (hpa : (5487/1024 : ℝ) ≤ p) (hpb : p ≤ (5503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4008758103/10000000000 : ℝ)*x 0 + (322836597/625000000 : ℝ)*x 1 + (3029776681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4008758103/10000000000 : ℝ)^5503 ≤ (16263686359521/50000000000000 : ℝ)^4479 := by
    have hnat : (4008758103 : ℕ)^5503*50000000000000^4479 ≤ 16263686359521^4479*10000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4008758103 10000000000 16263686359521 50000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (322836597/625000000 : ℝ)^5503 ≤ (8882630208693/20000000000000 : ℝ)^4479 := by
    have hnat : (322836597 : ℕ)^5503*20000000000000^4479 ≤ 8882630208693^4479*625000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      322836597 625000000 8882630208693 20000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3029776681/10000000000 : ℝ)^5503 ≤ (23059476220991/100000000000000 : ℝ)^4479 := by
    have hnat : (3029776681 : ℕ)^5503*100000000000000^4479 ≤ 23059476220991^4479*10000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3029776681 10000000000 23059476220991 100000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5503/1024 : ℝ)) 5503 4479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4008758103/10000000000 : ℝ), (322836597/625000000 : ℝ), (3029776681/10000000000 : ℝ)] ![(16263686359521/50000000000000 : ℝ), (8882630208693/20000000000000 : ℝ), (23059476220991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4008758103/10000000000 : ℝ)|^5503 ≤ (16263686359521/50000000000000 : ℝ)^4479
        have hw : |(4008758103/10000000000 : ℝ)|=(4008758103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(322836597/625000000 : ℝ)|^5503 ≤ (8882630208693/20000000000000 : ℝ)^4479
        have hw : |(322836597/625000000 : ℝ)|=(322836597/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3029776681/10000000000 : ℝ)|^5503 ≤ (23059476220991/100000000000000 : ℝ)^4479
        have hw : |(3029776681/10000000000 : ℝ)|=(3029776681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1733_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5487/1024 : ℝ) ≤ p) (hpb : p ≤ (5503/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (101461327/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (149/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (21837/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (5487/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5487 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5487*1^1024 ≤ 0^1024*1^5487 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5487 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5487 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5487/1024 : ℝ) ≤ (147471763943913929/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5487 ≤ (147471763943913929/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5487*20000000000000000000^1024 ≤ 147471763943913929^1024*5^5487 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 147471763943913929 20000000000000000000 5487 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (147471763943913929/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5487 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5487/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5487 := by
      have hnat : (1 : ℕ)^1024*1^5487 ≤ 1^5487*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5487 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5487 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20147471763943913929/20000000000000000000 : ℝ) ≤ (625857482738443/625000000000000 : ℝ) ^ (5487/1024 : ℝ) := by
    have hpowers : (20147471763943913929/20000000000000000000 : ℝ)^1024 ≤ (625857482738443/625000000000000 : ℝ)^5487 := by
      have hnat : (20147471763943913929 : ℕ)^1024*625000000000000^5487 ≤ 625857482738443^5487*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20147471763943913929 20000000000000000000 625857482738443 625000000000000 1024 5487 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625857482738443/625000000000000 : ℝ)) (X := (20147471763943913929/20000000000000000000 : ℝ)) (by norm_num) 5487 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10147471763943913929/10000000000000000000 : ℝ) ≤ (313357482738443/312500000000000 : ℝ) ^ (5487/1024 : ℝ) := by
    have hpowers : (10147471763943913929/10000000000000000000 : ℝ)^1024 ≤ (313357482738443/312500000000000 : ℝ)^5487 := by
      have hnat : (10147471763943913929 : ℕ)^1024*312500000000000^5487 ≤ 313357482738443^5487*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10147471763943913929 10000000000000000000 313357482738443 312500000000000 1024 5487 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (313357482738443/312500000000000 : ℝ)) (X := (10147471763943913929/10000000000000000000 : ℝ)) (by norm_num) 5487 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(857482738443/250000000000000 : ℝ)*(0 : ℝ))^(5487/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(857482738443/250000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(147471763943913929/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(857482738443/250000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5487/1024 : ℝ) := by
    rw [show (1 : ℝ)+(857482738443/250000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(625857482738443/625000000000000 : ℝ) by norm_num, show 1+(147471763943913929/20000000000000000000 : ℝ)+(0 : ℝ)=(20147471763943913929/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(147471763943913929/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(857482738443/250000000000000 : ℝ)*(2/5 : ℝ))^(5487/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(857482738443/250000000000000 : ℝ)*(2/5 : ℝ)=(313357482738443/312500000000000 : ℝ) by norm_num, show 1+2*(147471763943913929/20000000000000000000 : ℝ)=(10147471763943913929/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(857482738443/250000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5487/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (857482738443/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(857482738443/250000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5487/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (857482738443/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(857482738443/250000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5487/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (857482738443/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-315854193/2500000000 : ℝ)*X 0 0+(2843465161/5000000000 : ℝ)*X 0 1+(4949375829/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1733_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((107852027/200000000 : ℝ)*X 1 0+(-103917517/625000000 : ℝ)*X 1 1+(1237343991/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1733_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5392600961/10000000000 : ℝ)*X 2 0+(989875249/2000000000 : ℝ)*X 2 1+(-1662680421/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1733_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((800660633/2000000000 : ℝ)*X 0 0+(1484328701/5000000000 : ℝ)*X 0 1+(1306107889/2500000000 : ℝ)*X 0 2+(800660633/2000000000 : ℝ)*X 1 0+(1484328701/5000000000 : ℝ)*X 1 1+(1306107889/2500000000 : ℝ)*X 1 2+(800660633/2000000000 : ℝ)*X 2 0+(1484328701/5000000000 : ℝ)*X 2 1+(1306107889/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1733_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-316300073/2500000000 : ℝ)*X 0 0+(993736443/2000000000 : ℝ)*X 0 1+(283347319/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1733_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2597190759/5000000000 : ℝ)*X 1 0+(-945110169/10000000000 : ℝ)*X 1 1+(2833473311/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1733_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((649297727/1250000000 : ℝ)*X 2 0+(566694639/1000000000 : ℝ)*X 2 1+(-945110077/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1733_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4008758103/10000000000 : ℝ)*X 0 0+(322836597/625000000 : ℝ)*X 0 1+(3029776681/10000000000 : ℝ)*X 0 2+(4008758103/10000000000 : ℝ)*X 1 0+(322836597/625000000 : ℝ)*X 1 1+(3029776681/10000000000 : ℝ)*X 1 2+(4008758103/10000000000 : ℝ)*X 2 0+(322836597/625000000 : ℝ)*X 2 1+(3029776681/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1733_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (45429601970976713841573/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (383127/1000000000000 : ℝ)*(base1) + (788142301/100000000000000 : ℝ)*(base19) + (138067541/20000000000000 : ℝ)*(base23) + (41057781/25000000000000 : ℝ)*(upper3) + (8462757/10000000000000 : ℝ)*(upper5) + (899574110138637/100000000000000 : ℝ)*(major0) + (899574110138637/100000000000000 : ℝ)*(major1) + (899574110138637/100000000000000 : ℝ)*(major2) + (1355836025027429/100000000000000 : ℝ)*(sp0) + (271167689605579/20000000000000 : ℝ)*(sp1) + (1355838545832491/100000000000000 : ℝ)*(sp2) + (443307681437027/100000000000000 : ℝ)*(sp3) + (3249455467/100000000000000 : ℝ)*(sp4) + (1143211743/100000000000000 : ℝ)*(sp7) + (44330886296147/10000000000000 : ℝ)*(f.failure) + (338959809042549/25000000000000 : ℝ)*(f.sum) + (7720590877809/12500000000000000000000000000 : ℝ)*base66 + (60369423802809/25000000000000000000000000000 : ℝ)*base68 + (65498587122191/25000000000000000000000000000 : ℝ)*base69 + (64646333672191/25000000000000000000000000000 : ℝ)*base71 + (22244529852809/12500000000000000000000000000 : ℝ)*base74 + (56327479852809/25000000000000000000000000000 : ℝ)*base76 + (12222193647191/25000000000000000000000000000 : ℝ)*base77 + (73503292602809/25000000000000000000000000000 : ℝ)*base80 + (31582260972191/12500000000000000000000000000 : ℝ)*base81 + (4607069/500000000000000000000 : ℝ)*base89 + (4607069/500000000000000000000 : ℝ)*base91 + (4607069/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (413304320832859319433/48828125000000000000000000 : ℝ) := by norm_num
    linear_combination (1317193899/100000000000000 : ℝ)*(base19) + (285113907/20000000000000 : ℝ)*(base23) + (116461093/100000000000000 : ℝ)*(base32) + (13546427/5000000000000 : ℝ)*(upper3) + (168527403/100000000000000 : ℝ)*(upper5) + (14846660519523/1562500000000 : ℝ)*(major0) + (14846660519523/1562500000000 : ℝ)*(major1) + (14846660519523/1562500000000 : ℝ)*(major2) + (2330613377/50000000000000 : ℝ)*(sp1) + (1337055653/25000000000000 : ℝ)*(sp2) + (71606089910719/5000000000000 : ℝ)*(sp4) + (1432115819793727/100000000000000 : ℝ)*(sp5) + (1432115024422233/100000000000000 : ℝ)*(sp6) + (468250349674379/100000000000000 : ℝ)*(sp7) + (29265654133467/6250000000000 : ℝ)*(f.failure) + (71606089910719/5000000000000 : ℝ)*(f.sum) + (2815590722399/3125000000000000000000000000 : ℝ)*base65 + (1861439567253/781250000000000000000000000 : ℝ)*base67 + (23733643922137/3125000000000000000000000000 : ℝ)*base69 + (17598962597137/3125000000000000000000000000 : ℝ)*base71 + (8289162965101/3125000000000000000000000000 : ℝ)*base74 + (24496654390887/3125000000000000000000000000 : ℝ)*base75 + (18421494553387/3125000000000000000000000000 : ℝ)*base77 + (11103364900131/1562500000000000000000000000 : ℝ)*base79 + (1046560315887/1562500000000000000000000000 : ℝ)*base81 + (3069291/312500000000000000000 : ℝ)*base90 + (3069291/312500000000000000000 : ℝ)*base92 + (3069291/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1733_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5487/1024 : ℝ) ≤ p) (hpb : p ≤ (5503/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (101461327/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (149/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (21837/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1733_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1733_s1_0 (p : ℝ) (hpa : (5487/1024 : ℝ) ≤ p) (hpb : p ≤ (5503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-264359351/2000000000 : ℝ)*x 0 + (1105622711/2000000000 : ℝ)*x 1 + (5069509941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264359351/2000000000 : ℝ)^5503 ≤ (832229657881/10000000000000 : ℝ)^4479 := by
    have hnat : (264359351 : ℕ)^5503*10000000000000^4479 ≤ 832229657881^4479*2000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264359351 2000000000 832229657881 10000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1105622711/2000000000 : ℝ)^5503 ≤ (48275220448649/100000000000000 : ℝ)^4479 := by
    have hnat : (1105622711 : ℕ)^5503*100000000000000^4479 ≤ 48275220448649^4479*2000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105622711 2000000000 48275220448649 100000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5069509941/10000000000 : ℝ)^5503 ≤ (43402482959687/100000000000000 : ℝ)^4479 := by
    have hnat : (5069509941 : ℕ)^5503*100000000000000^4479 ≤ 43402482959687^4479*10000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5069509941 10000000000 43402482959687 100000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5503/1024 : ℝ)) 5503 4479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-264359351/2000000000 : ℝ), (1105622711/2000000000 : ℝ), (5069509941/10000000000 : ℝ)] ![(832229657881/10000000000000 : ℝ), (48275220448649/100000000000000 : ℝ), (43402482959687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-264359351/2000000000 : ℝ)|^5503 ≤ (832229657881/10000000000000 : ℝ)^4479
        have hw : |(-264359351/2000000000 : ℝ)|=(264359351/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1105622711/2000000000 : ℝ)|^5503 ≤ (48275220448649/100000000000000 : ℝ)^4479
        have hw : |(1105622711/2000000000 : ℝ)|=(1105622711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5069509941/10000000000 : ℝ)|^5503 ≤ (43402482959687/100000000000000 : ℝ)^4479
        have hw : |(5069509941/10000000000 : ℝ)|=(5069509941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1733_s1_1 (p : ℝ) (hpa : (5487/1024 : ℝ) ≤ p) (hpb : p ≤ (5503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675116297/5000000000 : ℝ)*x 0 + (-97674627/625000000 : ℝ)*x 1 + (5069509587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675116297/5000000000 : ℝ)^5503 ≤ (46373785902957/100000000000000 : ℝ)^4479 := by
    have hnat : (2675116297 : ℕ)^5503*100000000000000^4479 ≤ 46373785902957^4479*5000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675116297 5000000000 46373785902957 100000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (97674627/625000000 : ℝ)^5503 ≤ (5111867423339/50000000000000 : ℝ)^4479 := by
    have hnat : (97674627 : ℕ)^5503*50000000000000^4479 ≤ 5111867423339^4479*625000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97674627 625000000 5111867423339 50000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5069509587/10000000000 : ℝ)^5503 ≤ (1736099169441/4000000000000 : ℝ)^4479 := by
    have hnat : (5069509587 : ℕ)^5503*4000000000000^4479 ≤ 1736099169441^4479*10000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5069509587 10000000000 1736099169441 4000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5503/1024 : ℝ)) 5503 4479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675116297/5000000000 : ℝ), (-97674627/625000000 : ℝ), (5069509587/10000000000 : ℝ)] ![(46373785902957/100000000000000 : ℝ), (5111867423339/50000000000000 : ℝ), (1736099169441/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675116297/5000000000 : ℝ)|^5503 ≤ (46373785902957/100000000000000 : ℝ)^4479
        have hw : |(2675116297/5000000000 : ℝ)|=(2675116297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-97674627/625000000 : ℝ)|^5503 ≤ (5111867423339/50000000000000 : ℝ)^4479
        have hw : |(-97674627/625000000 : ℝ)|=(97674627/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5069509587/10000000000 : ℝ)|^5503 ≤ (1736099169441/4000000000000 : ℝ)^4479
        have hw : |(5069509587/10000000000 : ℝ)|=(5069509587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1733_s1_2 (p : ℝ) (hpa : (5487/1024 : ℝ) ≤ p) (hpb : p ≤ (5503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350231993/10000000000 : ℝ)*x 0 + (506951023/1000000000 : ℝ)*x 1 + (-781396993/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350231993/10000000000 : ℝ)^5503 ≤ (2898361218923/6250000000000 : ℝ)^4479 := by
    have hnat : (5350231993 : ℕ)^5503*6250000000000^4479 ≤ 2898361218923^4479*10000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350231993 10000000000 2898361218923 6250000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (506951023/1000000000 : ℝ)^5503 ≤ (43402485999627/100000000000000 : ℝ)^4479 := by
    have hnat : (506951023 : ℕ)^5503*100000000000000^4479 ≤ 43402485999627^4479*1000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506951023 1000000000 43402485999627 100000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (781396993/5000000000 : ℝ)^5503 ≤ (2555933619237/25000000000000 : ℝ)^4479 := by
    have hnat : (781396993 : ℕ)^5503*25000000000000^4479 ≤ 2555933619237^4479*5000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      781396993 5000000000 2555933619237 25000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5503/1024 : ℝ)) 5503 4479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350231993/10000000000 : ℝ), (506951023/1000000000 : ℝ), (-781396993/5000000000 : ℝ)] ![(2898361218923/6250000000000 : ℝ), (43402485999627/100000000000000 : ℝ), (2555933619237/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350231993/10000000000 : ℝ)|^5503 ≤ (2898361218923/6250000000000 : ℝ)^4479
        have hw : |(5350231993/10000000000 : ℝ)|=(5350231993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(506951023/1000000000 : ℝ)|^5503 ≤ (43402485999627/100000000000000 : ℝ)^4479
        have hw : |(506951023/1000000000 : ℝ)|=(506951023/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-781396993/5000000000 : ℝ)|^5503 ≤ (2555933619237/25000000000000 : ℝ)^4479
        have hw : |(-781396993/5000000000 : ℝ)|=(781396993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1733_s1_3 (p : ℝ) (hpa : (5487/1024 : ℝ) ≤ p) (hpb : p ≤ (5503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4056369767/10000000000 : ℝ)*x 0 + (3390832633/10000000000 : ℝ)*x 1 + (958689757/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4056369767/10000000000 : ℝ)^5503 ≤ (4125332799701/12500000000000 : ℝ)^4479 := by
    have hnat : (4056369767 : ℕ)^5503*12500000000000^4479 ≤ 4125332799701^4479*10000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4056369767 10000000000 4125332799701 12500000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3390832633/10000000000 : ℝ)^5503 ≤ (26480357081219/100000000000000 : ℝ)^4479 := by
    have hnat : (3390832633 : ℕ)^5503*100000000000000^4479 ≤ 26480357081219^4479*10000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3390832633 10000000000 26480357081219 100000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (958689757/2000000000 : ℝ)^5503 ≤ (8103396102607/20000000000000 : ℝ)^4479 := by
    have hnat : (958689757 : ℕ)^5503*20000000000000^4479 ≤ 8103396102607^4479*2000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      958689757 2000000000 8103396102607 20000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5503/1024 : ℝ)) 5503 4479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4056369767/10000000000 : ℝ), (3390832633/10000000000 : ℝ), (958689757/2000000000 : ℝ)] ![(4125332799701/12500000000000 : ℝ), (26480357081219/100000000000000 : ℝ), (8103396102607/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4056369767/10000000000 : ℝ)|^5503 ≤ (4125332799701/12500000000000 : ℝ)^4479
        have hw : |(4056369767/10000000000 : ℝ)|=(4056369767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3390832633/10000000000 : ℝ)|^5503 ≤ (26480357081219/100000000000000 : ℝ)^4479
        have hw : |(3390832633/10000000000 : ℝ)|=(3390832633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(958689757/2000000000 : ℝ)|^5503 ≤ (8103396102607/20000000000000 : ℝ)^4479
        have hw : |(958689757/2000000000 : ℝ)|=(958689757/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1733_s1_4 (p : ℝ) (hpa : (5487/1024 : ℝ) ≤ p) (hpb : p ≤ (5503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-13222213/100000000 : ℝ)*x 0 + (203078601/400000000 : ℝ)*x 1 + (552049609/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13222213/100000000 : ℝ)^5503 ≤ (832558083201/10000000000000 : ℝ)^4479 := by
    have hnat : (13222213 : ℕ)^5503*10000000000000^4479 ≤ 832558083201^4479*100000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13222213 100000000 832558083201 10000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (203078601/400000000 : ℝ)^5503 ≤ (2717557176749/6250000000000 : ℝ)^4479 := by
    have hnat : (203078601 : ℕ)^5503*6250000000000^4479 ≤ 2717557176749^4479*400000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203078601 400000000 2717557176749 6250000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (552049609/1000000000 : ℝ)^5503 ≤ (48193504318699/100000000000000 : ℝ)^4479 := by
    have hnat : (552049609 : ℕ)^5503*100000000000000^4479 ≤ 48193504318699^4479*1000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552049609 1000000000 48193504318699 100000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5503/1024 : ℝ)) 5503 4479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-13222213/100000000 : ℝ), (203078601/400000000 : ℝ), (552049609/1000000000 : ℝ)] ![(832558083201/10000000000000 : ℝ), (2717557176749/6250000000000 : ℝ), (48193504318699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-13222213/100000000 : ℝ)|^5503 ≤ (832558083201/10000000000000 : ℝ)^4479
        have hw : |(-13222213/100000000 : ℝ)|=(13222213/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(203078601/400000000 : ℝ)|^5503 ≤ (2717557176749/6250000000000 : ℝ)^4479
        have hw : |(203078601/400000000 : ℝ)|=(203078601/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(552049609/1000000000 : ℝ)|^5503 ≤ (48193504318699/100000000000000 : ℝ)^4479
        have hw : |(552049609/1000000000 : ℝ)|=(552049609/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1733_s1_5 (p : ℝ) (hpa : (5487/1024 : ℝ) ≤ p) (hpb : p ≤ (5503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1045642939/2000000000 : ℝ)*x 0 + (-555904323/5000000000 : ℝ)*x 1 + (552049613/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1045642939/2000000000 : ℝ)^5503 ≤ (1126944910493/2500000000000 : ℝ)^4479 := by
    have hnat : (1045642939 : ℕ)^5503*2500000000000^4479 ≤ 1126944910493^4479*2000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045642939 2000000000 1126944910493 2500000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (555904323/5000000000 : ℝ)^5503 ≤ (1682174704027/25000000000000 : ℝ)^4479 := by
    have hnat : (555904323 : ℕ)^5503*25000000000000^4479 ≤ 1682174704027^4479*5000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      555904323 5000000000 1682174704027 25000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (552049613/1000000000 : ℝ)^5503 ≤ (48193504747731/100000000000000 : ℝ)^4479 := by
    have hnat : (552049613 : ℕ)^5503*100000000000000^4479 ≤ 48193504747731^4479*1000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552049613 1000000000 48193504747731 100000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5503/1024 : ℝ)) 5503 4479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1045642939/2000000000 : ℝ), (-555904323/5000000000 : ℝ), (552049613/1000000000 : ℝ)] ![(1126944910493/2500000000000 : ℝ), (1682174704027/25000000000000 : ℝ), (48193504747731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1045642939/2000000000 : ℝ)|^5503 ≤ (1126944910493/2500000000000 : ℝ)^4479
        have hw : |(1045642939/2000000000 : ℝ)|=(1045642939/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-555904323/5000000000 : ℝ)|^5503 ≤ (1682174704027/25000000000000 : ℝ)^4479
        have hw : |(-555904323/5000000000 : ℝ)|=(555904323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(552049613/1000000000 : ℝ)|^5503 ≤ (48193504747731/100000000000000 : ℝ)^4479
        have hw : |(552049613/1000000000 : ℝ)|=(552049613/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1733_s1_6 (p : ℝ) (hpa : (5487/1024 : ℝ) ≤ p) (hpb : p ≤ (5503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (65352687/125000000 : ℝ)*x 0 + (2760247993/5000000000 : ℝ)*x 1 + (-1111808477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65352687/125000000 : ℝ)^5503 ≤ (45077799226921/100000000000000 : ℝ)^4479 := by
    have hnat : (65352687 : ℕ)^5503*100000000000000^4479 ≤ 45077799226921^4479*125000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65352687 125000000 45077799226921 100000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2760247993/5000000000 : ℝ)^5503 ≤ (24096751601609/50000000000000 : ℝ)^4479 := by
    have hnat : (2760247993 : ℕ)^5503*50000000000000^4479 ≤ 24096751601609^4479*5000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2760247993 5000000000 24096751601609 50000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1111808477/10000000000 : ℝ)^5503 ≤ (3364348779741/50000000000000 : ℝ)^4479 := by
    have hnat : (1111808477 : ℕ)^5503*50000000000000^4479 ≤ 3364348779741^4479*10000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1111808477 10000000000 3364348779741 50000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5503/1024 : ℝ)) 5503 4479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(65352687/125000000 : ℝ), (2760247993/5000000000 : ℝ), (-1111808477/10000000000 : ℝ)] ![(45077799226921/100000000000000 : ℝ), (24096751601609/50000000000000 : ℝ), (3364348779741/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(65352687/125000000 : ℝ)|^5503 ≤ (45077799226921/100000000000000 : ℝ)^4479
        have hw : |(65352687/125000000 : ℝ)|=(65352687/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2760247993/5000000000 : ℝ)|^5503 ≤ (24096751601609/50000000000000 : ℝ)^4479
        have hw : |(2760247993/5000000000 : ℝ)|=(2760247993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1111808477/10000000000 : ℝ)|^5503 ≤ (3364348779741/50000000000000 : ℝ)^4479
        have hw : |(-1111808477/10000000000 : ℝ)|=(1111808477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1733_s1_7 (p : ℝ) (hpa : (5487/1024 : ℝ) ≤ p) (hpb : p ≤ (5503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2028833119/5000000000 : ℝ)*x 0 + (477064789/1000000000 : ℝ)*x 1 + (3414128953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2028833119/5000000000 : ℝ)^5503 ≤ (16507811251933/50000000000000 : ℝ)^4479 := by
    have hnat : (2028833119 : ℕ)^5503*50000000000000^4479 ≤ 16507811251933^4479*5000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2028833119 5000000000 16507811251933 50000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (477064789/1000000000 : ℝ)^5503 ≤ (10070080405093/25000000000000 : ℝ)^4479 := by
    have hnat : (477064789 : ℕ)^5503*25000000000000^4479 ≤ 10070080405093^4479*1000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      477064789 1000000000 10070080405093 25000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3414128953/10000000000 : ℝ)^5503 ≤ (1669003490853/6250000000000 : ℝ)^4479 := by
    have hnat : (3414128953 : ℕ)^5503*6250000000000^4479 ≤ 1669003490853^4479*10000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3414128953 10000000000 1669003490853 6250000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5503/1024 : ℝ)) 5503 4479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2028833119/5000000000 : ℝ), (477064789/1000000000 : ℝ), (3414128953/10000000000 : ℝ)] ![(16507811251933/50000000000000 : ℝ), (10070080405093/25000000000000 : ℝ), (1669003490853/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2028833119/5000000000 : ℝ)|^5503 ≤ (16507811251933/50000000000000 : ℝ)^4479
        have hw : |(2028833119/5000000000 : ℝ)|=(2028833119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(477064789/1000000000 : ℝ)|^5503 ≤ (10070080405093/25000000000000 : ℝ)^4479
        have hw : |(477064789/1000000000 : ℝ)|=(477064789/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3414128953/10000000000 : ℝ)|^5503 ≤ (1669003490853/6250000000000 : ℝ)^4479
        have hw : |(3414128953/10000000000 : ℝ)|=(3414128953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1733_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5487/1024 : ℝ) ≤ p) (hpb : p ≤ (5503/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (101461327/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (21837/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (149/2500 : ℝ)*pair X i i ≤ pair X i h) :
    (8661/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18459/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (21837/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (149/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (21837/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (149/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (21837/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (149/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (21837/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (149/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (21837/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (149/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (21837/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (149/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (149/2500 : ℝ) ^ (5487/1024 : ℝ) ≤ (27370420639389/100000000000000000000 : ℝ) := by
    have hpowers : (149/2500 : ℝ)^5487 ≤ (27370420639389/100000000000000000000 : ℝ)^1024 := by
      have hnat : (149 : ℕ)^5487*100000000000000000000^1024 ≤ 27370420639389^1024*2500^5487 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        149 2500 27370420639389 100000000000000000000 5487 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (149/2500 : ℝ)) (X := (27370420639389/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5487 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (21837/100000 : ℝ) ^ (5487/1024 : ℝ) ≤ (7195693786149937/25000000000000000000 : ℝ) := by
    have hpowers : (21837/100000 : ℝ)^5487 ≤ (7195693786149937/25000000000000000000 : ℝ)^1024 := by
      have hnat : (21837 : ℕ)^5487*25000000000000000000^1024 ≤ 7195693786149937^1024*100000^5487 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21837 100000 7195693786149937 25000000000000000000 5487 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21837/100000 : ℝ)) (X := (7195693786149937/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5487 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000027370420639389/50000000000000000000 : ℝ) ≤ (16000001634543/16000000000000 : ℝ) ^ (5487/1024 : ℝ) := by
    have hpowers : (50000027370420639389/50000000000000000000 : ℝ)^1024 ≤ (16000001634543/16000000000000 : ℝ)^5487 := by
      have hnat : (50000027370420639389 : ℕ)^1024*16000000000000^5487 ≤ 16000001634543^5487*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000027370420639389 50000000000000000000 16000001634543 16000000000000 1024 5487 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (16000001634543/16000000000000 : ℝ)) (X := (50000027370420639389/50000000000000000000 : ℝ)) (by norm_num) 5487 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100028810145565239137/100000000000000000000 : ℝ) ≤ (10000537600383297/10000000000000000 : ℝ) ^ (5487/1024 : ℝ) := by
    have hpowers : (100028810145565239137/100000000000000000000 : ℝ)^1024 ≤ (10000537600383297/10000000000000000 : ℝ)^5487 := by
      have hnat : (100028810145565239137 : ℕ)^1024*10000000000000000^5487 ≤ 10000537600383297^5487*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100028810145565239137 100000000000000000000 10000537600383297 10000000000000000 1024 5487 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000537600383297/10000000000000000 : ℝ)) (X := (100028810145565239137/100000000000000000000 : ℝ)) (by norm_num) 5487 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507195693786149937/12500000000000000000 : ℝ) ≤ (10001074179177219/10000000000000000 : ℝ) ^ (5487/1024 : ℝ) := by
    have hpowers : (12507195693786149937/12500000000000000000 : ℝ)^1024 ≤ (10001074179177219/10000000000000000 : ℝ)^5487 := by
      have hnat : (12507195693786149937 : ℕ)^1024*10000000000000000^5487 ≤ 10001074179177219^5487*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507195693786149937 12500000000000000000 10001074179177219 10000000000000000 1024 5487 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001074179177219/10000000000000000 : ℝ)) (X := (12507195693786149937/12500000000000000000 : ℝ)) (by norm_num) 5487 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(27370420639389/100000000000000000000 : ℝ) ≤ ((31752724040110191327/31754000000000000000 : ℝ)+2*(268289396961/793850000000000 : ℝ)*(149/2500 : ℝ))^(5487/1024 : ℝ) := by
    rw [show (31752724040110191327/31754000000000000000 : ℝ)+2*(268289396961/793850000000000 : ℝ)*(149/2500 : ℝ)=(16000001634543/16000000000000 : ℝ) by norm_num, show 1+2*(27370420639389/100000000000000000000 : ℝ)=(50000027370420639389/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7195693786149937/25000000000000000000 : ℝ)+(27370420639389/100000000000000000000 : ℝ) ≤ ((31752724040110191327/31754000000000000000 : ℝ)+(268289396961/793850000000000 : ℝ)*((21837/100000 : ℝ)+(149/2500 : ℝ)))^(5487/1024 : ℝ) := by
    rw [show (31752724040110191327/31754000000000000000 : ℝ)+(268289396961/793850000000000 : ℝ)*((21837/100000 : ℝ)+(149/2500 : ℝ))=(10000537600383297/10000000000000000 : ℝ) by norm_num, show 1+(7195693786149937/25000000000000000000 : ℝ)+(27370420639389/100000000000000000000 : ℝ)=(100028810145565239137/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7195693786149937/25000000000000000000 : ℝ) ≤ ((31752724040110191327/31754000000000000000 : ℝ)+2*(268289396961/793850000000000 : ℝ)*(21837/100000 : ℝ))^(5487/1024 : ℝ) := by
    rw [show (31752724040110191327/31754000000000000000 : ℝ)+2*(268289396961/793850000000000 : ℝ)*(21837/100000 : ℝ)=(10001074179177219/10000000000000000 : ℝ) by norm_num, show 1+2*(7195693786149937/25000000000000000000 : ℝ)=(12507195693786149937/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (31752724040110191327/31754000000000000000 : ℝ)*(X 1 0+X 2 0)+(268289396961/793850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5487/1024 : ℝ)) (lo := (149/2500 : ℝ)) (hi := (21837/100000 : ℝ)) (c := (31752724040110191327/31754000000000000000 : ℝ)) (alpha := (268289396961/793850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (31752724040110191327/31754000000000000000 : ℝ)*(X 0 1+X 2 1)+(268289396961/793850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5487/1024 : ℝ)) (lo := (149/2500 : ℝ)) (hi := (21837/100000 : ℝ)) (c := (31752724040110191327/31754000000000000000 : ℝ)) (alpha := (268289396961/793850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (31752724040110191327/31754000000000000000 : ℝ)*(X 0 2+X 1 2)+(268289396961/793850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5487/1024 : ℝ)) (lo := (149/2500 : ℝ)) (hi := (21837/100000 : ℝ)) (c := (31752724040110191327/31754000000000000000 : ℝ)) (alpha := (268289396961/793850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-264359351/2000000000 : ℝ)*X 0 0+(1105622711/2000000000 : ℝ)*X 0 1+(5069509941/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1733_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675116297/5000000000 : ℝ)*X 1 0+(-97674627/625000000 : ℝ)*X 1 1+(5069509587/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1733_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350231993/10000000000 : ℝ)*X 2 0+(506951023/1000000000 : ℝ)*X 2 1+(-781396993/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1733_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4056369767/10000000000 : ℝ)*X 0 0+(3390832633/10000000000 : ℝ)*X 0 1+(958689757/2000000000 : ℝ)*X 0 2+(4056369767/10000000000 : ℝ)*X 1 0+(3390832633/10000000000 : ℝ)*X 1 1+(958689757/2000000000 : ℝ)*X 1 2+(4056369767/10000000000 : ℝ)*X 2 0+(3390832633/10000000000 : ℝ)*X 2 1+(958689757/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1733_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-13222213/100000000 : ℝ)*X 0 0+(203078601/400000000 : ℝ)*X 0 1+(552049609/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1733_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1045642939/2000000000 : ℝ)*X 1 0+(-555904323/5000000000 : ℝ)*X 1 1+(552049613/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1733_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((65352687/125000000 : ℝ)*X 2 0+(2760247993/5000000000 : ℝ)*X 2 1+(-1111808477/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1733_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2028833119/5000000000 : ℝ)*X 0 0+(477064789/1000000000 : ℝ)*X 0 1+(3414128953/10000000000 : ℝ)*X 0 2+(2028833119/5000000000 : ℝ)*X 1 0+(477064789/1000000000 : ℝ)*X 1 1+(3414128953/10000000000 : ℝ)*X 1 2+(2028833119/5000000000 : ℝ)*X 2 0+(477064789/1000000000 : ℝ)*X 2 1+(3414128953/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1733_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2008032723897083177991846723/198462500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2077228049/100000000000000 : ℝ)*(base19) + (421565267/25000000000000 : ℝ)*(base23) + (4882797/6250000000000 : ℝ)*(lower2) + (151467449/50000000000000 : ℝ)*(upper3) + (176315987/100000000000000 : ℝ)*(upper5) + (361690607649883/25000000000000 : ℝ)*(major0) + (361690607649883/25000000000000 : ℝ)*(major1) + (361690607649883/25000000000000 : ℝ)*(major2) + (68142116914979/3125000000000 : ℝ)*(sp0) + (2180559944944517/100000000000000 : ℝ)*(sp1) + (1090280167955749/50000000000000 : ℝ)*(sp2) + (356478808768569/50000000000000 : ℝ)*(sp3) + (7140446619/50000000000000 : ℝ)*(sp4) + (488422451/10000000000000 : ℝ)*(sp7) + (44560156360103/6250000000000 : ℝ)*(f.failure) + (1090281011086283/50000000000000 : ℝ)*(f.sum) + (182047402685553/39692500000000000000000000000 : ℝ)*base66 + (2291059306482284741/793850000000000000000000000000000 : ℝ)*base67 + (7076334322486115259/793850000000000000000000000000000 : ℝ)*base70 + (4684411001975715259/793850000000000000000000000000000 : ℝ)*base72 + (104316697778077/39692500000000000000000000000 : ℝ)*base73 + (6817813427008465259/793850000000000000000000000000000 : ℝ)*base76 + (7098642549017315259/793850000000000000000000000000000 : ℝ)*base78 + (1076875158335215259/793850000000000000000000000000000 : ℝ)*base80 + (120110646087829/19846250000000000000000000000 : ℝ)*base82 + (2736681/312500000000000000000 : ℝ)*base89 + (2736681/312500000000000000000 : ℝ)*base91 + (2736681/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (482990081285106157286019/79385000000000000000000000000 : ℝ) := by norm_num
    linear_combination (966908773/100000000000000 : ℝ)*(base19) + (1283525431/100000000000000 : ℝ)*(base23) + (10560869/12500000000000 : ℝ)*(upper2) + (216447549/100000000000000 : ℝ)*(upper3) + (56276101/25000000000000 : ℝ)*(upper5) + (747953529798181/50000000000000 : ℝ)*(major0) + (747953529798181/50000000000000 : ℝ)*(major1) + (747953529798181/50000000000000 : ℝ)*(major2) + (2502271361/50000000000000 : ℝ)*(sp1) + (6750178229/100000000000000 : ℝ)*(sp2) + (112731650510521/5000000000000 : ℝ)*(sp4) + (563656759689731/25000000000000 : ℝ)*(sp5) + (56365624412669/2500000000000 : ℝ)*(sp6) + (368590453088683/50000000000000 : ℝ)*(sp7) + (368590453088683/50000000000000 : ℝ)*(f.failure) + (112731650510521/5000000000000 : ℝ)*(f.sum) + (13461265280199/4961562500000000000000000000 : ℝ)*base65 + (5363406784923783813/1587700000000000000000000000000000 : ℝ)*base68 + (3800820004220383813/1587700000000000000000000000000000 : ℝ)*base70 + (3342714544443016187/1587700000000000000000000000000000 : ℝ)*base71 + (669649517309/4961562500000000000000000000 : ℝ)*base73 + (5744778301627816187/1587700000000000000000000000000000 : ℝ)*base75 + (3196739899715716187/1587700000000000000000000000000000 : ℝ)*base77 + (3601198756304783813/1587700000000000000000000000000000 : ℝ)*base80 + (5151071150607/2480781250000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (24137659/2500000000000000000000 : ℝ)*base90 + (24137659/2500000000000000000000 : ℝ)*base92 + (24137659/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1733_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5487/1024 : ℝ) ≤ p) (hpb : p ≤ (5503/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (101461327/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (21837/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (149/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8661/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18459/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1733_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1733_s2_0 (p : ℝ) (hpa : (5487/1024 : ℝ) ≤ p) (hpb : p ≤ (5503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-82746633/625000000 : ℝ)*x 0 + (138032157/250000000 : ℝ)*x 1 + (39647587/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82746633/625000000 : ℝ)^5503 ≤ (8338926470959/100000000000000 : ℝ)^4479 := by
    have hnat : (82746633 : ℕ)^5503*100000000000000^4479 ≤ 8338926470959^4479*625000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82746633 625000000 8338926470959 100000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (138032157/250000000 : ℝ)^5503 ≤ (12050494965199/25000000000000 : ℝ)^4479 := by
    have hnat : (138032157 : ℕ)^5503*25000000000000^4479 ≤ 12050494965199^4479*250000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138032157 250000000 12050494965199 25000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (39647587/78125000 : ℝ)^5503 ≤ (10864773412673/25000000000000 : ℝ)^4479 := by
    have hnat : (39647587 : ℕ)^5503*25000000000000^4479 ≤ 10864773412673^4479*78125000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39647587 78125000 10864773412673 25000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5503/1024 : ℝ)) 5503 4479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-82746633/625000000 : ℝ), (138032157/250000000 : ℝ), (39647587/78125000 : ℝ)] ![(8338926470959/100000000000000 : ℝ), (12050494965199/25000000000000 : ℝ), (10864773412673/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-82746633/625000000 : ℝ)|^5503 ≤ (8338926470959/100000000000000 : ℝ)^4479
        have hw : |(-82746633/625000000 : ℝ)|=(82746633/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(138032157/250000000 : ℝ)|^5503 ≤ (12050494965199/25000000000000 : ℝ)^4479
        have hw : |(138032157/250000000 : ℝ)|=(138032157/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(39647587/78125000 : ℝ)|^5503 ≤ (10864773412673/25000000000000 : ℝ)^4479
        have hw : |(39647587/78125000 : ℝ)|=(39647587/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1733_s2_1 (p : ℝ) (hpa : (5487/1024 : ℝ) ≤ p) (hpb : p ≤ (5503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (41784101/78125000 : ℝ)*x 0 + (-779111619/5000000000 : ℝ)*x 1 + (634361391/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41784101/78125000 : ℝ)^5503 ≤ (5794237185723/12500000000000 : ℝ)^4479 := by
    have hnat : (41784101 : ℕ)^5503*12500000000000^4479 ≤ 5794237185723^4479*78125000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41784101 78125000 5794237185723 12500000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (779111619/5000000000 : ℝ)^5503 ≤ (407480357351/4000000000000 : ℝ)^4479 := by
    have hnat : (779111619 : ℕ)^5503*4000000000000^4479 ≤ 407480357351^4479*5000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      779111619 5000000000 407480357351 4000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (634361391/1250000000 : ℝ)^5503 ≤ (43459093566521/100000000000000 : ℝ)^4479 := by
    have hnat : (634361391 : ℕ)^5503*100000000000000^4479 ≤ 43459093566521^4479*1250000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      634361391 1250000000 43459093566521 100000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5503/1024 : ℝ)) 5503 4479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41784101/78125000 : ℝ), (-779111619/5000000000 : ℝ), (634361391/1250000000 : ℝ)] ![(5794237185723/12500000000000 : ℝ), (407480357351/4000000000000 : ℝ), (43459093566521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41784101/78125000 : ℝ)|^5503 ≤ (5794237185723/12500000000000 : ℝ)^4479
        have hw : |(41784101/78125000 : ℝ)|=(41784101/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-779111619/5000000000 : ℝ)|^5503 ≤ (407480357351/4000000000000 : ℝ)^4479
        have hw : |(-779111619/5000000000 : ℝ)|=(779111619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(634361391/1250000000 : ℝ)|^5503 ≤ (43459093566521/100000000000000 : ℝ)^4479
        have hw : |(634361391/1250000000 : ℝ)|=(634361391/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1733_s2_2 (p : ℝ) (hpa : (5487/1024 : ℝ) ≤ p) (hpb : p ≤ (5503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337091233/2500000000 : ℝ)*x 0 + (5074891097/10000000000 : ℝ)*x 1 + (-1558223273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337091233/2500000000 : ℝ)^5503 ≤ (23176948764189/50000000000000 : ℝ)^4479 := by
    have hnat : (1337091233 : ℕ)^5503*50000000000000^4479 ≤ 23176948764189^4479*2500000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337091233 2500000000 23176948764189 50000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5074891097/10000000000 : ℝ)^5503 ≤ (21729546620179/50000000000000 : ℝ)^4479 := by
    have hnat : (5074891097 : ℕ)^5503*50000000000000^4479 ≤ 21729546620179^4479*10000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5074891097 10000000000 21729546620179 50000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1558223273/10000000000 : ℝ)^5503 ≤ (5093504607451/50000000000000 : ℝ)^4479 := by
    have hnat : (1558223273 : ℕ)^5503*50000000000000^4479 ≤ 5093504607451^4479*10000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1558223273 10000000000 5093504607451 50000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5503/1024 : ℝ)) 5503 4479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337091233/2500000000 : ℝ), (5074891097/10000000000 : ℝ), (-1558223273/10000000000 : ℝ)] ![(23176948764189/50000000000000 : ℝ), (21729546620179/50000000000000 : ℝ), (5093504607451/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337091233/2500000000 : ℝ)|^5503 ≤ (23176948764189/50000000000000 : ℝ)^4479
        have hw : |(1337091233/2500000000 : ℝ)|=(1337091233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5074891097/10000000000 : ℝ)|^5503 ≤ (21729546620179/50000000000000 : ℝ)^4479
        have hw : |(5074891097/10000000000 : ℝ)|=(5074891097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1558223273/10000000000 : ℝ)|^5503 ≤ (5093504607451/50000000000000 : ℝ)^4479
        have hw : |(-1558223273/10000000000 : ℝ)|=(1558223273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1733_s2_3 (p : ℝ) (hpa : (5487/1024 : ℝ) ≤ p) (hpb : p ≤ (5503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2029055717/5000000000 : ℝ)*x 0 + (3409358371/10000000000 : ℝ)*x 1 + (4774637073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2029055717/5000000000 : ℝ)^5503 ≤ (6604014620273/20000000000000 : ℝ)^4479 := by
    have hnat : (2029055717 : ℕ)^5503*20000000000000^4479 ≤ 6604014620273^4479*5000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2029055717 5000000000 6604014620273 20000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3409358371/10000000000 : ℝ)^5503 ≤ (26658218691351/100000000000000 : ℝ)^4479 := by
    have hnat : (3409358371 : ℕ)^5503*100000000000000^4479 ≤ 26658218691351^4479*10000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3409358371 10000000000 26658218691351 100000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4774637073/10000000000 : ℝ)^5503 ≤ (20160854097229/50000000000000 : ℝ)^4479 := by
    have hnat : (4774637073 : ℕ)^5503*50000000000000^4479 ≤ 20160854097229^4479*10000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4774637073 10000000000 20160854097229 50000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5503/1024 : ℝ)) 5503 4479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2029055717/5000000000 : ℝ), (3409358371/10000000000 : ℝ), (4774637073/10000000000 : ℝ)] ![(6604014620273/20000000000000 : ℝ), (26658218691351/100000000000000 : ℝ), (20160854097229/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2029055717/5000000000 : ℝ)|^5503 ≤ (6604014620273/20000000000000 : ℝ)^4479
        have hw : |(2029055717/5000000000 : ℝ)|=(2029055717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3409358371/10000000000 : ℝ)|^5503 ≤ (26658218691351/100000000000000 : ℝ)^4479
        have hw : |(3409358371/10000000000 : ℝ)|=(3409358371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4774637073/10000000000 : ℝ)|^5503 ≤ (20160854097229/50000000000000 : ℝ)^4479
        have hw : |(4774637073/10000000000 : ℝ)|=(4774637073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1733_s2_4 (p : ℝ) (hpa : (5487/1024 : ℝ) ≤ p) (hpb : p ≤ (5503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-52973541/400000000 : ℝ)*x 0 + (19851381/39062500 : ℝ)*x 1 + (5514073409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52973541/400000000 : ℝ)^5503 ≤ (8341963148461/100000000000000 : ℝ)^4479 := by
    have hnat : (52973541 : ℕ)^5503*100000000000000^4479 ≤ 8341963148461^4479*400000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52973541 400000000 8341963148461 100000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (19851381/39062500 : ℝ)^5503 ≤ (43533411606151/100000000000000 : ℝ)^4479 := by
    have hnat : (19851381 : ℕ)^5503*100000000000000^4479 ≤ 43533411606151^4479*39062500^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19851381 39062500 43533411606151 100000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5514073409/10000000000 : ℝ)^5503 ≤ (24062312612559/50000000000000 : ℝ)^4479 := by
    have hnat : (5514073409 : ℕ)^5503*50000000000000^4479 ≤ 24062312612559^4479*10000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5514073409 10000000000 24062312612559 50000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5503/1024 : ℝ)) 5503 4479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-52973541/400000000 : ℝ), (19851381/39062500 : ℝ), (5514073409/10000000000 : ℝ)] ![(8341963148461/100000000000000 : ℝ), (43533411606151/100000000000000 : ℝ), (24062312612559/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-52973541/400000000 : ℝ)|^5503 ≤ (8341963148461/100000000000000 : ℝ)^4479
        have hw : |(-52973541/400000000 : ℝ)|=(52973541/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(19851381/39062500 : ℝ)|^5503 ≤ (43533411606151/100000000000000 : ℝ)^4479
        have hw : |(19851381/39062500 : ℝ)|=(19851381/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5514073409/10000000000 : ℝ)|^5503 ≤ (24062312612559/50000000000000 : ℝ)^4479
        have hw : |(5514073409/10000000000 : ℝ)|=(5514073409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1733_s2_5 (p : ℝ) (hpa : (5487/1024 : ℝ) ≤ p) (hpb : p ≤ (5503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1307408789/2500000000 : ℝ)*x 0 + (-1119042623/10000000000 : ℝ)*x 1 + (137851841/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1307408789/2500000000 : ℝ)^5503 ≤ (11273211033323/25000000000000 : ℝ)^4479 := by
    have hnat : (1307408789 : ℕ)^5503*25000000000000^4479 ≤ 11273211033323^4479*2500000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307408789 2500000000 11273211033323 25000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1119042623/10000000000 : ℝ)^5503 ≤ (6782528145689/100000000000000 : ℝ)^4479 := by
    have hnat : (1119042623 : ℕ)^5503*100000000000000^4479 ≤ 6782528145689^4479*10000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119042623 10000000000 6782528145689 100000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (137851841/250000000 : ℝ)^5503 ≤ (48124627702113/100000000000000 : ℝ)^4479 := by
    have hnat : (137851841 : ℕ)^5503*100000000000000^4479 ≤ 48124627702113^4479*250000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137851841 250000000 48124627702113 100000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5503/1024 : ℝ)) 5503 4479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1307408789/2500000000 : ℝ), (-1119042623/10000000000 : ℝ), (137851841/250000000 : ℝ)] ![(11273211033323/25000000000000 : ℝ), (6782528145689/100000000000000 : ℝ), (48124627702113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1307408789/2500000000 : ℝ)|^5503 ≤ (11273211033323/25000000000000 : ℝ)^4479
        have hw : |(1307408789/2500000000 : ℝ)|=(1307408789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1119042623/10000000000 : ℝ)|^5503 ≤ (6782528145689/100000000000000 : ℝ)^4479
        have hw : |(-1119042623/10000000000 : ℝ)|=(1119042623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(137851841/250000000 : ℝ)|^5503 ≤ (48124627702113/100000000000000 : ℝ)^4479
        have hw : |(137851841/250000000 : ℝ)|=(137851841/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1733_s2_6 (p : ℝ) (hpa : (5487/1024 : ℝ) ≤ p) (hpb : p ≤ (5503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5229638749/10000000000 : ℝ)*x 0 + (1102814007/2000000000 : ℝ)*x 1 + (-1119042703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5229638749/10000000000 : ℝ)^5503 ≤ (22546441098537/50000000000000 : ℝ)^4479 := by
    have hnat : (5229638749 : ℕ)^5503*50000000000000^4479 ≤ 22546441098537^4479*10000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229638749 10000000000 22546441098537 50000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1102814007/2000000000 : ℝ)^5503 ≤ (48124589045971/100000000000000 : ℝ)^4479 := by
    have hnat : (1102814007 : ℕ)^5503*100000000000000^4479 ≤ 48124589045971^4479*2000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102814007 2000000000 48124589045971 100000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1119042703/10000000000 : ℝ)^5503 ≤ (423908046339/6250000000000 : ℝ)^4479 := by
    have hnat : (1119042703 : ℕ)^5503*6250000000000^4479 ≤ 423908046339^4479*10000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119042703 10000000000 423908046339 6250000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5503/1024 : ℝ)) 5503 4479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5229638749/10000000000 : ℝ), (1102814007/2000000000 : ℝ), (-1119042703/10000000000 : ℝ)] ![(22546441098537/50000000000000 : ℝ), (48124589045971/100000000000000 : ℝ), (423908046339/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5229638749/10000000000 : ℝ)|^5503 ≤ (22546441098537/50000000000000 : ℝ)^4479
        have hw : |(5229638749/10000000000 : ℝ)|=(5229638749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1102814007/2000000000 : ℝ)|^5503 ≤ (48124589045971/100000000000000 : ℝ)^4479
        have hw : |(1102814007/2000000000 : ℝ)|=(1102814007/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1119042703/10000000000 : ℝ)|^5503 ≤ (423908046339/6250000000000 : ℝ)^4479
        have hw : |(-1119042703/10000000000 : ℝ)|=(1119042703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1733_s2_7 (p : ℝ) (hpa : (5487/1024 : ℝ) ≤ p) (hpb : p ≤ (5503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4059308473/10000000000 : ℝ)*x 0 + (2376516791/5000000000 : ℝ)*x 1 + (1715708467/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4059308473/10000000000 : ℝ)^5503 ≤ (16516020190719/50000000000000 : ℝ)^4479 := by
    have hnat : (4059308473 : ℕ)^5503*50000000000000^4479 ≤ 16516020190719^4479*10000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4059308473 10000000000 16516020190719 50000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2376516791/5000000000 : ℝ)^5503 ≤ (40097673128829/100000000000000 : ℝ)^4479 := by
    have hnat : (2376516791 : ℕ)^5503*100000000000000^4479 ≤ 40097673128829^4479*5000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2376516791 5000000000 40097673128829 100000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1715708467/5000000000 : ℝ)^5503 ≤ (26870286471441/100000000000000 : ℝ)^4479 := by
    have hnat : (1715708467 : ℕ)^5503*100000000000000^4479 ≤ 26870286471441^4479*5000000000^5503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1715708467 5000000000 26870286471441 100000000000000 5503 4479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5503/1024 : ℝ)) 5503 4479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4059308473/10000000000 : ℝ), (2376516791/5000000000 : ℝ), (1715708467/5000000000 : ℝ)] ![(16516020190719/50000000000000 : ℝ), (40097673128829/100000000000000 : ℝ), (26870286471441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4059308473/10000000000 : ℝ)|^5503 ≤ (16516020190719/50000000000000 : ℝ)^4479
        have hw : |(4059308473/10000000000 : ℝ)|=(4059308473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2376516791/5000000000 : ℝ)|^5503 ≤ (40097673128829/100000000000000 : ℝ)^4479
        have hw : |(2376516791/5000000000 : ℝ)|=(2376516791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1715708467/5000000000 : ℝ)|^5503 ≤ (26870286471441/100000000000000 : ℝ)^4479
        have hw : |(1715708467/5000000000 : ℝ)|=(1715708467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1733_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5487/1024 : ℝ) ≤ p) (hpb : p ≤ (5503/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (101461327/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18459/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8661/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (439/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3663/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18459/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8661/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18459/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8661/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18459/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8661/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18459/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8661/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18459/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8661/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18459/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8661/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8661/100000 : ℝ) ^ (5487/1024 : ℝ) ≤ (101399600145117/50000000000000000000 : ℝ) := by
    have hpowers : (8661/100000 : ℝ)^5487 ≤ (101399600145117/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8661 : ℕ)^5487*50000000000000000000^1024 ≤ 101399600145117^1024*100000^5487 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8661 100000 101399600145117 50000000000000000000 5487 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8661/100000 : ℝ)) (X := (101399600145117/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5487 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18459/100000 : ℝ) ^ (5487/1024 : ℝ) ≤ (11696367453718651/100000000000000000000 : ℝ) := by
    have hpowers : (18459/100000 : ℝ)^5487 ≤ (11696367453718651/100000000000000000000 : ℝ)^1024 := by
      have hnat : (18459 : ℕ)^5487*100000000000000000000^1024 ≤ 11696367453718651^1024*100000^5487 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18459 100000 11696367453718651 100000000000000000000 5487 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18459/100000 : ℝ)) (X := (11696367453718651/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5487 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000101399600145117/25000000000000000000 : ℝ) ≤ (5000003784691791/5000000000000000 : ℝ) ^ (5487/1024 : ℝ) := by
    have hpowers : (25000101399600145117/25000000000000000000 : ℝ)^1024 ≤ (5000003784691791/5000000000000000 : ℝ)^5487 := by
      have hnat : (25000101399600145117 : ℕ)^1024*5000000000000000^5487 ≤ 5000003784691791^5487*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000101399600145117 25000000000000000000 5000003784691791 5000000000000000 1024 5487 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000003784691791/5000000000000000 : ℝ)) (X := (25000101399600145117/25000000000000000000 : ℝ)) (by norm_num) 5487 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20002379833330801777/20000000000000000000 : ℝ) ≤ (10000222054985333/10000000000000000 : ℝ) ^ (5487/1024 : ℝ) := by
    have hpowers : (20002379833330801777/20000000000000000000 : ℝ)^1024 ≤ (10000222054985333/10000000000000000 : ℝ)^5487 := by
      have hnat : (20002379833330801777 : ℕ)^1024*10000000000000000^5487 ≤ 10000222054985333^5487*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20002379833330801777 20000000000000000000 10000222054985333 10000000000000000 1024 5487 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000222054985333/10000000000000000 : ℝ)) (X := (20002379833330801777/20000000000000000000 : ℝ)) (by norm_num) 5487 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50011696367453718651/50000000000000000000 : ℝ) ≤ (2500109135146771/2500000000000000 : ℝ) ^ (5487/1024 : ℝ) := by
    have hpowers : (50011696367453718651/50000000000000000000 : ℝ)^1024 ≤ (2500109135146771/2500000000000000 : ℝ)^5487 := by
      have hnat : (50011696367453718651 : ℕ)^1024*2500000000000000^5487 ≤ 2500109135146771^5487*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50011696367453718651 50000000000000000000 2500109135146771 2500000000000000 1024 5487 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500109135146771/2500000000000000 : ℝ)) (X := (50011696367453718651/50000000000000000000 : ℝ)) (by norm_num) 5487 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(101399600145117/50000000000000000000 : ℝ) ≤ ((16329393140871134269/16330000000000000000 : ℝ)+2*(214485601751/979800000000000 : ℝ)*(8661/100000 : ℝ))^(5487/1024 : ℝ) := by
    rw [show (16329393140871134269/16330000000000000000 : ℝ)+2*(214485601751/979800000000000 : ℝ)*(8661/100000 : ℝ)=(5000003784691791/5000000000000000 : ℝ) by norm_num, show 1+2*(101399600145117/50000000000000000000 : ℝ)=(25000101399600145117/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11696367453718651/100000000000000000000 : ℝ)+(101399600145117/50000000000000000000 : ℝ) ≤ ((16329393140871134269/16330000000000000000 : ℝ)+(214485601751/979800000000000 : ℝ)*((18459/100000 : ℝ)+(8661/100000 : ℝ)))^(5487/1024 : ℝ) := by
    rw [show (16329393140871134269/16330000000000000000 : ℝ)+(214485601751/979800000000000 : ℝ)*((18459/100000 : ℝ)+(8661/100000 : ℝ))=(10000222054985333/10000000000000000 : ℝ) by norm_num, show 1+(11696367453718651/100000000000000000000 : ℝ)+(101399600145117/50000000000000000000 : ℝ)=(20002379833330801777/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11696367453718651/100000000000000000000 : ℝ) ≤ ((16329393140871134269/16330000000000000000 : ℝ)+2*(214485601751/979800000000000 : ℝ)*(18459/100000 : ℝ))^(5487/1024 : ℝ) := by
    rw [show (16329393140871134269/16330000000000000000 : ℝ)+2*(214485601751/979800000000000 : ℝ)*(18459/100000 : ℝ)=(2500109135146771/2500000000000000 : ℝ) by norm_num, show 1+2*(11696367453718651/100000000000000000000 : ℝ)=(50011696367453718651/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16329393140871134269/16330000000000000000 : ℝ)*(X 1 0+X 2 0)+(214485601751/979800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5487/1024 : ℝ)) (lo := (8661/100000 : ℝ)) (hi := (18459/100000 : ℝ)) (c := (16329393140871134269/16330000000000000000 : ℝ)) (alpha := (214485601751/979800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16329393140871134269/16330000000000000000 : ℝ)*(X 0 1+X 2 1)+(214485601751/979800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5487/1024 : ℝ)) (lo := (8661/100000 : ℝ)) (hi := (18459/100000 : ℝ)) (c := (16329393140871134269/16330000000000000000 : ℝ)) (alpha := (214485601751/979800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16329393140871134269/16330000000000000000 : ℝ)*(X 0 2+X 1 2)+(214485601751/979800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5487/1024 : ℝ)) (lo := (8661/100000 : ℝ)) (hi := (18459/100000 : ℝ)) (c := (16329393140871134269/16330000000000000000 : ℝ)) (alpha := (214485601751/979800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-82746633/625000000 : ℝ)*X 0 0+(138032157/250000000 : ℝ)*X 0 1+(39647587/78125000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1733_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((41784101/78125000 : ℝ)*X 1 0+(-779111619/5000000000 : ℝ)*X 1 1+(634361391/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1733_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337091233/2500000000 : ℝ)*X 2 0+(5074891097/10000000000 : ℝ)*X 2 1+(-1558223273/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1733_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2029055717/5000000000 : ℝ)*X 0 0+(3409358371/10000000000 : ℝ)*X 0 1+(4774637073/10000000000 : ℝ)*X 0 2+(2029055717/5000000000 : ℝ)*X 1 0+(3409358371/10000000000 : ℝ)*X 1 1+(4774637073/10000000000 : ℝ)*X 1 2+(2029055717/5000000000 : ℝ)*X 2 0+(3409358371/10000000000 : ℝ)*X 2 1+(4774637073/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1733_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-52973541/400000000 : ℝ)*X 0 0+(19851381/39062500 : ℝ)*X 0 1+(5514073409/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1733_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1307408789/2500000000 : ℝ)*X 1 0+(-1119042623/10000000000 : ℝ)*X 1 1+(137851841/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1733_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5229638749/10000000000 : ℝ)*X 2 0+(1102814007/2000000000 : ℝ)*X 2 1+(-1119042703/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1733_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4059308473/10000000000 : ℝ)*X 0 0+(2376516791/5000000000 : ℝ)*X 0 1+(1715708467/5000000000 : ℝ)*X 0 2+(4059308473/10000000000 : ℝ)*X 1 0+(2376516791/5000000000 : ℝ)*X 1 1+(1715708467/5000000000 : ℝ)*X 1 2+(4059308473/10000000000 : ℝ)*X 2 0+(2376516791/5000000000 : ℝ)*X 2 1+(1715708467/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1733_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6653059636286524724041813459/816500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1193127581/100000000000000 : ℝ)*(base19) + (27976527/2500000000000 : ℝ)*(base23) + (20254771/50000000000000 : ℝ)*(lower2) + (52106427/25000000000000 : ℝ)*(upper3) + (135705903/100000000000000 : ℝ)*(upper5) + (1486321323447163/100000000000000 : ℝ)*(major0) + (1486321323447163/100000000000000 : ℝ)*(major1) + (1486321323447163/100000000000000 : ℝ)*(major2) + (2240176712990491/100000000000000 : ℝ)*(sp0) + (2240184113344257/100000000000000 : ℝ)*(sp1) + (1120092093705379/50000000000000 : ℝ)*(sp2) + (146490775884507/20000000000000 : ℝ)*(sp3) + (8593481347/100000000000000 : ℝ)*(sp4) + (637878213/20000000000000 : ℝ)*(sp7) + (915571336017/125000000000 : ℝ)*(f.failure) + (1120092653235919/50000000000000 : ℝ)*(f.sum) + (33750405063533/48990000000000000000000000000 : ℝ)*base65 + (34238719594691963459/4899000000000000000000000000000000 : ℝ)*base68 + (16102754420685036541/4899000000000000000000000000000000 : ℝ)*base69 + (11587142964647963459/4899000000000000000000000000000000 : ℝ)*base72 + (180252329607097/48990000000000000000000000000 : ℝ)*base74 + (10220710317582036541/4899000000000000000000000000000000 : ℝ)*base75 + (22521066951312036541/4899000000000000000000000000000000 : ℝ)*base77 + (6958122405762036541/4899000000000000000000000000000000 : ℝ)*base79 + (63082338701723/48990000000000000000000000000 : ℝ)*base81 + (27059/6250000000000000000 : ℝ)*base89 + (27059/6250000000000000000 : ℝ)*base91 + (27059/6250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (567181316444650881307726969/204125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (466554561/100000000000000 : ℝ)*(base19) + (2134826761/100000000000000 : ℝ)*(base23) + (8054569/6250000000000 : ℝ)*(upper2) + (54977037/20000000000000 : ℝ)*(upper3) + (2197769/2500000000000 : ℝ)*(upper4) + (45816019/12500000000000 : ℝ)*(upper5) + (383853384422411/25000000000000 : ℝ)*(major0) + (383853384422411/25000000000000 : ℝ)*(major1) + (383853384422411/25000000000000 : ℝ)*(major2) + (6907581/2500000000000 : ℝ)*(sp0) + (2314177063144401/100000000000000 : ℝ)*(sp4) + (57854421822327/2500000000000 : ℝ)*(sp5) + (28927190057761/1250000000000 : ℝ)*(sp6) + (94581205413963/12500000000000 : ℝ)*(sp7) + (94581205413963/12500000000000 : ℝ)*(f.failure) + (2314177339447641/100000000000000 : ℝ)*(f.sum) + (183848310494443/24495000000000000000000000000 : ℝ)*base66 + (15255768513380157677/1224750000000000000000000000000000 : ℝ)*base67 + (9036529261735407677/1224750000000000000000000000000000 : ℝ)*base69 + (8872683079982157677/1224750000000000000000000000000000 : ℝ)*base71 + (82347602600881/12247500000000000000000000000 : ℝ)*base73 + (4185297511148157677/1224750000000000000000000000000000 : ℝ)*base75 + (4824445085642157677/1224750000000000000000000000000000 : ℝ)*base77 + (8064977532896157677/1224750000000000000000000000000000 : ℝ)*base79 + (53729334657901/12247500000000000000000000000 : ℝ)*base81 + (4691099/625000000000000000000 : ℝ)*base90 + (4691099/625000000000000000000 : ℝ)*base92 + (4691099/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1733_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5487/1024 : ℝ) ≤ p) (hpb : p ≤ (5503/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (101461327/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18459/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8661/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (439/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3663/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1733_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1733_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5487/1024 : ℝ) ≤ p) (hpb : p ≤ (5503/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (101461327/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (439/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3663/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1733_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1733_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1733_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5487/1024 : ℝ) ≤ p) (hpb : p ≤ (5503/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (101461327/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (439/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3663/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1733_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1595_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:37:46.897547+00:00
-- url     : https://prove2.me/submissions/fa6b4adb-0b66-4a20-a184-f8d310200722

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
theorem support_rectangle_w1595_box_0 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1463216751/10000000000 : ℝ)*x 0 + (5421964117/10000000000 : ℝ)*x 1 + (5421963519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1463216751/10000000000 : ℝ)^4699 ≤ (53531663849/625000000000 : ℝ)^3675 := by
    have hnat : (1463216751 : ℕ)^4699*625000000000^3675 ≤ 53531663849^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1463216751 10000000000 53531663849 625000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5421964117/10000000000 : ℝ)^4699 ≤ (45717470112041/100000000000000 : ℝ)^3675 := by
    have hnat : (5421964117 : ℕ)^4699*100000000000000^3675 ≤ 45717470112041^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421964117 10000000000 45717470112041 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5421963519/10000000000 : ℝ)^4699 ≤ (45717463664787/100000000000000 : ℝ)^3675 := by
    have hnat : (5421963519 : ℕ)^4699*100000000000000^3675 ≤ 45717463664787^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421963519 10000000000 45717463664787 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1463216751/10000000000 : ℝ), (5421964117/10000000000 : ℝ), (5421963519/10000000000 : ℝ)] ![(53531663849/625000000000 : ℝ), (45717470112041/100000000000000 : ℝ), (45717463664787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1463216751/10000000000 : ℝ)|^4699 ≤ (53531663849/625000000000 : ℝ)^3675
        have hw : |(-1463216751/10000000000 : ℝ)|=(1463216751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5421964117/10000000000 : ℝ)|^4699 ≤ (45717470112041/100000000000000 : ℝ)^3675
        have hw : |(5421964117/10000000000 : ℝ)|=(5421964117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5421963519/10000000000 : ℝ)|^4699 ≤ (45717463664787/100000000000000 : ℝ)^3675
        have hw : |(5421963519/10000000000 : ℝ)|=(5421963519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_box_1 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5250897901/10000000000 : ℝ)*x 0 + (-851628271/5000000000 : ℝ)*x 1 + (1084392739/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5250897901/10000000000 : ℝ)^4699 ≤ (5485164065597/12500000000000 : ℝ)^3675 := by
    have hnat : (5250897901 : ℕ)^4699*12500000000000^3675 ≤ 5485164065597^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5250897901 10000000000 5485164065597 12500000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (851628271/5000000000 : ℝ)^4699 ≤ (10401221895529/100000000000000 : ℝ)^3675 := by
    have hnat : (851628271 : ℕ)^4699*100000000000000^3675 ≤ 10401221895529^3675*5000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      851628271 5000000000 10401221895529 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1084392739/2000000000 : ℝ)^4699 ≤ (22858732781153/50000000000000 : ℝ)^3675 := by
    have hnat : (1084392739 : ℕ)^4699*50000000000000^3675 ≤ 22858732781153^3675*2000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084392739 2000000000 22858732781153 50000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5250897901/10000000000 : ℝ), (-851628271/5000000000 : ℝ), (1084392739/2000000000 : ℝ)] ![(5485164065597/12500000000000 : ℝ), (10401221895529/100000000000000 : ℝ), (22858732781153/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5250897901/10000000000 : ℝ)|^4699 ≤ (5485164065597/12500000000000 : ℝ)^3675
        have hw : |(5250897901/10000000000 : ℝ)|=(5250897901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-851628271/5000000000 : ℝ)|^4699 ≤ (10401221895529/100000000000000 : ℝ)^3675
        have hw : |(-851628271/5000000000 : ℝ)|=(851628271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1084392739/2000000000 : ℝ)|^4699 ≤ (22858732781153/50000000000000 : ℝ)^3675
        have hw : |(1084392739/2000000000 : ℝ)|=(1084392739/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_box_2 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625448719/5000000000 : ℝ)*x 0 + (5421963889/10000000000 : ℝ)*x 1 + (-425814227/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625448719/5000000000 : ℝ)^4699 ≤ (21940653788699/50000000000000 : ℝ)^3675 := by
    have hnat : (2625448719 : ℕ)^4699*50000000000000^3675 ≤ 21940653788699^3675*5000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625448719 5000000000 21940653788699 50000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5421963889/10000000000 : ℝ)^4699 ≤ (45717467653891/100000000000000 : ℝ)^3675 := by
    have hnat : (5421963889 : ℕ)^4699*100000000000000^3675 ≤ 45717467653891^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421963889 10000000000 45717467653891 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (425814227/2500000000 : ℝ)^4699 ≤ (520061237667/5000000000000 : ℝ)^3675 := by
    have hnat : (425814227 : ℕ)^4699*5000000000000^3675 ≤ 520061237667^3675*2500000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425814227 2500000000 520061237667 5000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625448719/5000000000 : ℝ), (5421963889/10000000000 : ℝ), (-425814227/2500000000 : ℝ)] ![(21940653788699/50000000000000 : ℝ), (45717467653891/100000000000000 : ℝ), (520061237667/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625448719/5000000000 : ℝ)|^4699 ≤ (21940653788699/50000000000000 : ℝ)^3675
        have hw : |(2625448719/5000000000 : ℝ)|=(2625448719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5421963889/10000000000 : ℝ)|^4699 ≤ (45717467653891/100000000000000 : ℝ)^3675
        have hw : |(5421963889/10000000000 : ℝ)|=(5421963889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-425814227/2500000000 : ℝ)|^4699 ≤ (520061237667/5000000000000 : ℝ)^3675
        have hw : |(-425814227/2500000000 : ℝ)|=(425814227/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_box_3 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1126581961/2500000000 : ℝ)*x 0 + (4097501937/10000000000 : ℝ)*x 1 + (2048750503/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1126581961/2500000000 : ℝ)^4699 ≤ (9022027820817/25000000000000 : ℝ)^3675 := by
    have hnat : (1126581961 : ℕ)^4699*25000000000000^3675 ≤ 9022027820817^3675*2500000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126581961 2500000000 9022027820817 25000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4097501937/10000000000 : ℝ)^4699 ≤ (15977974495877/50000000000000 : ℝ)^3675 := by
    have hnat : (4097501937 : ℕ)^4699*50000000000000^3675 ≤ 15977974495877^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4097501937 10000000000 15977974495877 50000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2048750503/5000000000 : ℝ)^4699 ≤ (31955939707857/100000000000000 : ℝ)^3675 := by
    have hnat : (2048750503 : ℕ)^4699*100000000000000^3675 ≤ 31955939707857^3675*5000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2048750503 5000000000 31955939707857 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1126581961/2500000000 : ℝ), (4097501937/10000000000 : ℝ), (2048750503/5000000000 : ℝ)] ![(9022027820817/25000000000000 : ℝ), (15977974495877/50000000000000 : ℝ), (31955939707857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1126581961/2500000000 : ℝ)|^4699 ≤ (9022027820817/25000000000000 : ℝ)^3675
        have hw : |(1126581961/2500000000 : ℝ)|=(1126581961/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4097501937/10000000000 : ℝ)|^4699 ≤ (15977974495877/50000000000000 : ℝ)^3675
        have hw : |(4097501937/10000000000 : ℝ)|=(4097501937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2048750503/5000000000 : ℝ)|^4699 ≤ (31955939707857/100000000000000 : ℝ)^3675
        have hw : |(2048750503/5000000000 : ℝ)|=(2048750503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_box_4 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1016574543/5000000000 : ℝ)*x 0 + (5213133933/10000000000 : ℝ)*x 1 + (2606567211/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1016574543/5000000000 : ℝ)^4699 ≤ (3260903026051/25000000000000 : ℝ)^3675 := by
    have hnat : (1016574543 : ℕ)^4699*25000000000000^3675 ≤ 3260903026051^3675*5000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016574543 5000000000 3260903026051 25000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5213133933/10000000000 : ℝ)^4699 ≤ (54347739163/125000000000 : ℝ)^3675 := by
    have hnat : (5213133933 : ℕ)^4699*125000000000^3675 ≤ 54347739163^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5213133933 10000000000 54347739163 125000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2606567211/5000000000 : ℝ)^4699 ≤ (43478196545103/100000000000000 : ℝ)^3675 := by
    have hnat : (2606567211 : ℕ)^4699*100000000000000^3675 ≤ 43478196545103^3675*5000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2606567211 5000000000 43478196545103 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1016574543/5000000000 : ℝ), (5213133933/10000000000 : ℝ), (2606567211/5000000000 : ℝ)] ![(3260903026051/25000000000000 : ℝ), (54347739163/125000000000 : ℝ), (43478196545103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1016574543/5000000000 : ℝ)|^4699 ≤ (3260903026051/25000000000000 : ℝ)^3675
        have hw : |(-1016574543/5000000000 : ℝ)|=(1016574543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5213133933/10000000000 : ℝ)|^4699 ≤ (54347739163/125000000000 : ℝ)^3675
        have hw : |(5213133933/10000000000 : ℝ)|=(5213133933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2606567211/5000000000 : ℝ)|^4699 ≤ (43478196545103/100000000000000 : ℝ)^3675
        have hw : |(2606567211/5000000000 : ℝ)|=(2606567211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_box_5 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5395335937/10000000000 : ℝ)*x 0 + (-895501391/5000000000 : ℝ)*x 1 + (1303283663/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5395335937/10000000000 : ℝ)^4699 ≤ (45430578712931/100000000000000 : ℝ)^3675 := by
    have hnat : (5395335937 : ℕ)^4699*100000000000000^3675 ≤ 45430578712931^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395335937 10000000000 45430578712931 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (895501391/5000000000 : ℝ)^4699 ≤ (173300348057/1562500000000 : ℝ)^3675 := by
    have hnat : (895501391 : ℕ)^4699*1562500000000^3675 ≤ 173300348057^3675*5000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895501391 5000000000 173300348057 1562500000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1303283663/2500000000 : ℝ)^4699 ≤ (21739099498913/50000000000000 : ℝ)^3675 := by
    have hnat : (1303283663 : ℕ)^4699*50000000000000^3675 ≤ 21739099498913^3675*2500000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303283663 2500000000 21739099498913 50000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5395335937/10000000000 : ℝ), (-895501391/5000000000 : ℝ), (1303283663/2500000000 : ℝ)] ![(45430578712931/100000000000000 : ℝ), (173300348057/1562500000000 : ℝ), (21739099498913/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5395335937/10000000000 : ℝ)|^4699 ≤ (45430578712931/100000000000000 : ℝ)^3675
        have hw : |(5395335937/10000000000 : ℝ)|=(5395335937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-895501391/5000000000 : ℝ)|^4699 ≤ (173300348057/1562500000000 : ℝ)^3675
        have hw : |(-895501391/5000000000 : ℝ)|=(895501391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1303283663/2500000000 : ℝ)|^4699 ≤ (21739099498913/50000000000000 : ℝ)^3675
        have hw : |(1303283663/2500000000 : ℝ)|=(1303283663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_box_6 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5395337177/10000000000 : ℝ)*x 0 + (5213133251/10000000000 : ℝ)*x 1 + (-895501491/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5395337177/10000000000 : ℝ)^4699 ≤ (22715296031747/50000000000000 : ℝ)^3675 := by
    have hnat : (5395337177 : ℕ)^4699*50000000000000^3675 ≤ 22715296031747^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395337177 10000000000 22715296031747 50000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5213133251/10000000000 : ℝ)^4699 ≤ (43478184057543/100000000000000 : ℝ)^3675 := by
    have hnat : (5213133251 : ℕ)^4699*100000000000000^3675 ≤ 43478184057543^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5213133251 10000000000 43478184057543 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (895501491/5000000000 : ℝ)^4699 ≤ (2218244771861/20000000000000 : ℝ)^3675 := by
    have hnat : (895501491 : ℕ)^4699*20000000000000^3675 ≤ 2218244771861^3675*5000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895501491 5000000000 2218244771861 20000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5395337177/10000000000 : ℝ), (5213133251/10000000000 : ℝ), (-895501491/5000000000 : ℝ)] ![(22715296031747/50000000000000 : ℝ), (43478184057543/100000000000000 : ℝ), (2218244771861/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5395337177/10000000000 : ℝ)|^4699 ≤ (22715296031747/50000000000000 : ℝ)^3675
        have hw : |(5395337177/10000000000 : ℝ)|=(5395337177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5213133251/10000000000 : ℝ)|^4699 ≤ (43478184057543/100000000000000 : ℝ)^3675
        have hw : |(5213133251/10000000000 : ℝ)|=(5213133251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-895501491/5000000000 : ℝ)|^4699 ≤ (2218244771861/20000000000000 : ℝ)^3675
        have hw : |(-895501491/5000000000 : ℝ)|=(895501491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_box_7 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3938230493/10000000000 : ℝ)*x 0 + (2190599069/5000000000 : ℝ)*x 1 + (34228117/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3938230493/10000000000 : ℝ)^4699 ≤ (15188191423491/50000000000000 : ℝ)^3675 := by
    have hnat : (3938230493 : ℕ)^4699*50000000000000^3675 ≤ 15188191423491^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3938230493 10000000000 15188191423491 50000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2190599069/5000000000 : ℝ)^4699 ≤ (17405902156969/50000000000000 : ℝ)^3675 := by
    have hnat : (2190599069 : ℕ)^4699*50000000000000^3675 ≤ 17405902156969^3675*5000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190599069 5000000000 17405902156969 50000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34228117/78125000 : ℝ)^4699 ≤ (34811812827783/100000000000000 : ℝ)^3675 := by
    have hnat : (34228117 : ℕ)^4699*100000000000000^3675 ≤ 34811812827783^3675*78125000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34228117 78125000 34811812827783 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3938230493/10000000000 : ℝ), (2190599069/5000000000 : ℝ), (34228117/78125000 : ℝ)] ![(15188191423491/50000000000000 : ℝ), (17405902156969/50000000000000 : ℝ), (34811812827783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3938230493/10000000000 : ℝ)|^4699 ≤ (15188191423491/50000000000000 : ℝ)^3675
        have hw : |(3938230493/10000000000 : ℝ)|=(3938230493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2190599069/5000000000 : ℝ)|^4699 ≤ (17405902156969/50000000000000 : ℝ)^3675
        have hw : |(2190599069/5000000000 : ℝ)|=(2190599069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(34228117/78125000 : ℝ)|^4699 ≤ (34811812827783/100000000000000 : ℝ)^3675
        have hw : |(34228117/78125000 : ℝ)|=(34228117/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_box_8 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1912157119/10000000000 : ℝ)*x 0 + (5064362177/10000000000 : ℝ)*x 1 + (1090417749/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1912157119/10000000000 : ℝ)^4699 ≤ (12059455369209/100000000000000 : ℝ)^3675 := by
    have hnat : (1912157119 : ℕ)^4699*100000000000000^3675 ≤ 12059455369209^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1912157119 10000000000 12059455369209 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5064362177/10000000000 : ℝ)^4699 ≤ (41898038896059/100000000000000 : ℝ)^3675 := by
    have hnat : (5064362177 : ℕ)^4699*100000000000000^3675 ≤ 41898038896059^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5064362177 10000000000 41898038896059 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1090417749/2000000000 : ℝ)^4699 ≤ (46042505718859/100000000000000 : ℝ)^3675 := by
    have hnat : (1090417749 : ℕ)^4699*100000000000000^3675 ≤ 46042505718859^3675*2000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090417749 2000000000 46042505718859 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1912157119/10000000000 : ℝ), (5064362177/10000000000 : ℝ), (1090417749/2000000000 : ℝ)] ![(12059455369209/100000000000000 : ℝ), (41898038896059/100000000000000 : ℝ), (46042505718859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1912157119/10000000000 : ℝ)|^4699 ≤ (12059455369209/100000000000000 : ℝ)^3675
        have hw : |(-1912157119/10000000000 : ℝ)|=(1912157119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5064362177/10000000000 : ℝ)|^4699 ≤ (41898038896059/100000000000000 : ℝ)^3675
        have hw : |(5064362177/10000000000 : ℝ)|=(5064362177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1090417749/2000000000 : ℝ)|^4699 ≤ (46042505718859/100000000000000 : ℝ)^3675
        have hw : |(1090417749/2000000000 : ℝ)|=(1090417749/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_box_9 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1307513651/2500000000 : ℝ)*x 0 + (-1690122387/10000000000 : ℝ)*x 1 + (5452088867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1307513651/2500000000 : ℝ)^4699 ≤ (21829357563883/50000000000000 : ℝ)^3675 := by
    have hnat : (1307513651 : ℕ)^4699*50000000000000^3675 ≤ 21829357563883^3675*2500000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307513651 2500000000 21829357563883 50000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1690122387/10000000000 : ℝ)^4699 ≤ (2574694455299/25000000000000 : ℝ)^3675 := by
    have hnat : (1690122387 : ℕ)^4699*25000000000000^3675 ≤ 2574694455299^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1690122387 10000000000 2574694455299 25000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5452088867/10000000000 : ℝ)^4699 ≤ (23021253518109/50000000000000 : ℝ)^3675 := by
    have hnat : (5452088867 : ℕ)^4699*50000000000000^3675 ≤ 23021253518109^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5452088867 10000000000 23021253518109 50000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1307513651/2500000000 : ℝ), (-1690122387/10000000000 : ℝ), (5452088867/10000000000 : ℝ)] ![(21829357563883/50000000000000 : ℝ), (2574694455299/25000000000000 : ℝ), (23021253518109/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1307513651/2500000000 : ℝ)|^4699 ≤ (21829357563883/50000000000000 : ℝ)^3675
        have hw : |(1307513651/2500000000 : ℝ)|=(1307513651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1690122387/10000000000 : ℝ)|^4699 ≤ (2574694455299/25000000000000 : ℝ)^3675
        have hw : |(-1690122387/10000000000 : ℝ)|=(1690122387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5452088867/10000000000 : ℝ)|^4699 ≤ (23021253518109/50000000000000 : ℝ)^3675
        have hw : |(5452088867/10000000000 : ℝ)|=(5452088867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_box_10 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (523005509/1000000000 : ℝ)*x 0 + (54520891/100000000 : ℝ)*x 1 + (-845060699/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (523005509/1000000000 : ℝ)^4699 ≤ (21829360157579/50000000000000 : ℝ)^3675 := by
    have hnat : (523005509 : ℕ)^4699*50000000000000^3675 ≤ 21829360157579^3675*1000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523005509 1000000000 21829360157579 50000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54520891/100000000 : ℝ)^4699 ≤ (46042509552157/100000000000000 : ℝ)^3675 := by
    have hnat : (54520891 : ℕ)^4699*100000000000000^3675 ≤ 46042509552157^3675*100000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54520891 100000000 46042509552157 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (845060699/5000000000 : ℝ)^4699 ≤ (20597540231/200000000000 : ℝ)^3675 := by
    have hnat : (845060699 : ℕ)^4699*200000000000^3675 ≤ 20597540231^3675*5000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845060699 5000000000 20597540231 200000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(523005509/1000000000 : ℝ), (54520891/100000000 : ℝ), (-845060699/5000000000 : ℝ)] ![(21829360157579/50000000000000 : ℝ), (46042509552157/100000000000000 : ℝ), (20597540231/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(523005509/1000000000 : ℝ)|^4699 ≤ (21829360157579/50000000000000 : ℝ)^3675
        have hw : |(523005509/1000000000 : ℝ)|=(523005509/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(54520891/100000000 : ℝ)|^4699 ≤ (46042509552157/100000000000000 : ℝ)^3675
        have hw : |(54520891/100000000 : ℝ)|=(54520891/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-845060699/5000000000 : ℝ)|^4699 ≤ (20597540231/200000000000 : ℝ)^3675
        have hw : |(-845060699/5000000000 : ℝ)|=(845060699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_box_11 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2292937293/5000000000 : ℝ)*x 0 + (4056503679/10000000000 : ℝ)*x 1 + (4056501731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2292937293/5000000000 : ℝ)^4699 ≤ (4613080626803/12500000000000 : ℝ)^3675 := by
    have hnat : (2292937293 : ℕ)^4699*12500000000000^3675 ≤ 4613080626803^3675*5000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2292937293 5000000000 4613080626803 12500000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4056503679/10000000000 : ℝ)^4699 ≤ (15773843585003/50000000000000 : ℝ)^3675 := by
    have hnat : (4056503679 : ℕ)^4699*50000000000000^3675 ≤ 15773843585003^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4056503679 10000000000 15773843585003 50000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4056501731/10000000000 : ℝ)^4699 ≤ (31547667798977/100000000000000 : ℝ)^3675 := by
    have hnat : (4056501731 : ℕ)^4699*100000000000000^3675 ≤ 31547667798977^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4056501731 10000000000 31547667798977 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2292937293/5000000000 : ℝ), (4056503679/10000000000 : ℝ), (4056501731/10000000000 : ℝ)] ![(4613080626803/12500000000000 : ℝ), (15773843585003/50000000000000 : ℝ), (31547667798977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2292937293/5000000000 : ℝ)|^4699 ≤ (4613080626803/12500000000000 : ℝ)^3675
        have hw : |(2292937293/5000000000 : ℝ)|=(2292937293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4056503679/10000000000 : ℝ)|^4699 ≤ (15773843585003/50000000000000 : ℝ)^3675
        have hw : |(4056503679/10000000000 : ℝ)|=(4056503679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4056501731/10000000000 : ℝ)|^4699 ≤ (31547667798977/100000000000000 : ℝ)^3675
        have hw : |(4056501731/10000000000 : ℝ)|=(4056501731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_box_12 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1583224501/10000000000 : ℝ)*x 0 + (5564538743/10000000000 : ℝ)*x 1 + (162289579/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1583224501/10000000000 : ℝ)^4699 ≤ (4736673665041/50000000000000 : ℝ)^3675 := by
    have hnat : (1583224501 : ℕ)^4699*50000000000000^3675 ≤ 4736673665041^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1583224501 10000000000 4736673665041 50000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5564538743/10000000000 : ℝ)^4699 ≤ (1476881719143/3125000000000 : ℝ)^3675 := by
    have hnat : (5564538743 : ℕ)^4699*3125000000000^3675 ≤ 1476881719143^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5564538743 10000000000 1476881719143 3125000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (162289579/312500000 : ℝ)^4699 ≤ (5408304706031/12500000000000 : ℝ)^3675 := by
    have hnat : (162289579 : ℕ)^4699*12500000000000^3675 ≤ 5408304706031^3675*312500000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162289579 312500000 5408304706031 12500000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1583224501/10000000000 : ℝ), (5564538743/10000000000 : ℝ), (162289579/312500000 : ℝ)] ![(4736673665041/50000000000000 : ℝ), (1476881719143/3125000000000 : ℝ), (5408304706031/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1583224501/10000000000 : ℝ)|^4699 ≤ (4736673665041/50000000000000 : ℝ)^3675
        have hw : |(-1583224501/10000000000 : ℝ)|=(1583224501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5564538743/10000000000 : ℝ)|^4699 ≤ (1476881719143/3125000000000 : ℝ)^3675
        have hw : |(5564538743/10000000000 : ℝ)|=(5564538743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(162289579/312500000 : ℝ)|^4699 ≤ (5408304706031/12500000000000 : ℝ)^3675
        have hw : |(162289579/312500000 : ℝ)|=(162289579/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_box_13 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5409083691/10000000000 : ℝ)*x 0 + (-179904193/1000000000 : ℝ)*x 1 + (1038653239/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5409083691/10000000000 : ℝ)^4699 ≤ (45578647556347/100000000000000 : ℝ)^3675 := by
    have hnat : (5409083691 : ℕ)^4699*100000000000000^3675 ≤ 45578647556347^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409083691 10000000000 45578647556347 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (179904193/1000000000 : ℝ)^4699 ≤ (11154918323273/100000000000000 : ℝ)^3675 := by
    have hnat : (179904193 : ℕ)^4699*100000000000000^3675 ≤ 11154918323273^3675*1000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179904193 1000000000 11154918323273 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1038653239/2000000000 : ℝ)^4699 ≤ (10816608525227/25000000000000 : ℝ)^3675 := by
    have hnat : (1038653239 : ℕ)^4699*25000000000000^3675 ≤ 10816608525227^3675*2000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038653239 2000000000 10816608525227 25000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5409083691/10000000000 : ℝ), (-179904193/1000000000 : ℝ), (1038653239/2000000000 : ℝ)] ![(45578647556347/100000000000000 : ℝ), (11154918323273/100000000000000 : ℝ), (10816608525227/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5409083691/10000000000 : ℝ)|^4699 ≤ (45578647556347/100000000000000 : ℝ)^3675
        have hw : |(5409083691/10000000000 : ℝ)|=(5409083691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-179904193/1000000000 : ℝ)|^4699 ≤ (11154918323273/100000000000000 : ℝ)^3675
        have hw : |(-179904193/1000000000 : ℝ)|=(179904193/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1038653239/2000000000 : ℝ)|^4699 ≤ (10816608525227/25000000000000 : ℝ)^3675
        have hw : |(1038653239/2000000000 : ℝ)|=(1038653239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_box_14 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5409083603/10000000000 : ℝ)*x 0 + (2596633171/5000000000 : ℝ)*x 1 + (-1799041853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5409083603/10000000000 : ℝ)^4699 ≤ (5697330826027/12500000000000 : ℝ)^3675 := by
    have hnat : (5409083603 : ℕ)^4699*12500000000000^3675 ≤ 5697330826027^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409083603 10000000000 5697330826027 12500000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2596633171/5000000000 : ℝ)^4699 ≤ (43266435666851/100000000000000 : ℝ)^3675 := by
    have hnat : (2596633171 : ℕ)^4699*100000000000000^3675 ≤ 43266435666851^3675*5000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596633171 5000000000 43266435666851 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1799041853/10000000000 : ℝ)^4699 ≤ (11154917712803/100000000000000 : ℝ)^3675 := by
    have hnat : (1799041853 : ℕ)^4699*100000000000000^3675 ≤ 11154917712803^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1799041853 10000000000 11154917712803 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5409083603/10000000000 : ℝ), (2596633171/5000000000 : ℝ), (-1799041853/10000000000 : ℝ)] ![(5697330826027/12500000000000 : ℝ), (43266435666851/100000000000000 : ℝ), (11154917712803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5409083603/10000000000 : ℝ)|^4699 ≤ (5697330826027/12500000000000 : ℝ)^3675
        have hw : |(5409083603/10000000000 : ℝ)|=(5409083603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2596633171/5000000000 : ℝ)|^4699 ≤ (43266435666851/100000000000000 : ℝ)^3675
        have hw : |(2596633171/5000000000 : ℝ)|=(2596633171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1799041853/10000000000 : ℝ)|^4699 ≤ (11154917712803/100000000000000 : ℝ)^3675
        have hw : |(-1799041853/10000000000 : ℝ)|=(1799041853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1595_box_15 (p : ℝ) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3882561989/10000000000 : ℝ)*x 0 + (4408141829/10000000000 : ℝ)*x 1 + (1102035459/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3882561989/10000000000 : ℝ)^4699 ≤ (5965688436681/20000000000000 : ℝ)^3675 := by
    have hnat : (3882561989 : ℕ)^4699*20000000000000^3675 ≤ 5965688436681^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3882561989 10000000000 5965688436681 20000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4408141829/10000000000 : ℝ)^4699 ≤ (35085778864747/100000000000000 : ℝ)^3675 := by
    have hnat : (4408141829 : ℕ)^4699*100000000000000^3675 ≤ 35085778864747^3675*10000000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4408141829 10000000000 35085778864747 100000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1102035459/2500000000 : ℝ)^4699 ≤ (17542889467993/50000000000000 : ℝ)^3675 := by
    have hnat : (1102035459 : ℕ)^4699*50000000000000^3675 ≤ 17542889467993^3675*2500000000^4699 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102035459 2500000000 17542889467993 50000000000000 4699 3675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4699/1024 : ℝ)) 4699 3675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3882561989/10000000000 : ℝ), (4408141829/10000000000 : ℝ), (1102035459/2500000000 : ℝ)] ![(5965688436681/20000000000000 : ℝ), (35085778864747/100000000000000 : ℝ), (17542889467993/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3882561989/10000000000 : ℝ)|^4699 ≤ (5965688436681/20000000000000 : ℝ)^3675
        have hw : |(3882561989/10000000000 : ℝ)|=(3882561989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4408141829/10000000000 : ℝ)|^4699 ≤ (35085778864747/100000000000000 : ℝ)^3675
        have hw : |(4408141829/10000000000 : ℝ)|=(4408141829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1102035459/2500000000 : ℝ)|^4699 ≤ (17542889467993/50000000000000 : ℝ)^3675
        have hw : |(1102035459/2500000000 : ℝ)|=(1102035459/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1595_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170443833/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8183/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2583/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(32437/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(3627/6250 : ℝ) ∧ (2504/3125 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (87669/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8183/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2583/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8183/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2583/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8183/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2583/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8183/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2583/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8183/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2583/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8183/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2583/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2583/25000 : ℝ) ^ (4695/1024 : ℝ) ≤ (3020466135801493/100000000000000000000 : ℝ) := by
    have hpowers : (2583/25000 : ℝ)^4695 ≤ (3020466135801493/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2583 : ℕ)^4695*100000000000000000000^1024 ≤ 3020466135801493^1024*25000^4695 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2583 25000 3020466135801493 100000000000000000000 4695 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2583/25000 : ℝ)) (X := (3020466135801493/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4695 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8183/50000 : ℝ) ^ (4695/1024 : ℝ) ≤ (1555382828360859/6250000000000000000 : ℝ) := by
    have hpowers : (8183/50000 : ℝ)^4695 ≤ (1555382828360859/6250000000000000000 : ℝ)^1024 := by
      have hnat : (8183 : ℕ)^4695*6250000000000000000^1024 ≤ 1555382828360859^1024*50000^4695 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8183 50000 1555382828360859 6250000000000000000 4695 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8183/50000 : ℝ)) (X := (1555382828360859/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4695 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50003020466135801493/50000000000000000000 : ℝ) ≤ (1250016469032373/1250000000000000 : ℝ) ^ (4695/1024 : ℝ) := by
    have hpowers : (50003020466135801493/50000000000000000000 : ℝ)^1024 ≤ (1250016469032373/1250000000000000 : ℝ)^4695 := by
      have hnat : (50003020466135801493 : ℕ)^1024*1250000000000000^4695 ≤ 1250016469032373^4695*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50003020466135801493 50000000000000000000 1250016469032373 1250000000000000 1024 4695 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250016469032373/1250000000000000 : ℝ)) (X := (50003020466135801493/50000000000000000000 : ℝ)) (by norm_num) 4695 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100027906591389575237/100000000000000000000 : ℝ) ≤ (10000608588549817/10000000000000000 : ℝ) ^ (4695/1024 : ℝ) := by
    have hpowers : (100027906591389575237/100000000000000000000 : ℝ)^1024 ≤ (10000608588549817/10000000000000000 : ℝ)^4695 := by
      have hnat : (100027906591389575237 : ℕ)^1024*10000000000000000^4695 ≤ 10000608588549817^4695*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100027906591389575237 100000000000000000000 10000608588549817 10000000000000000 1024 4695 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000608588549817/10000000000000000 : ℝ)) (X := (100027906591389575237/100000000000000000000 : ℝ)) (by norm_num) 4695 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3126555382828360859/3125000000000000000 : ℝ) ≤ (200021708496813/200000000000000 : ℝ) ^ (4695/1024 : ℝ) := by
    have hpowers : (3126555382828360859/3125000000000000000 : ℝ)^1024 ≤ (200021708496813/200000000000000 : ℝ)^4695 := by
      have hnat : (3126555382828360859 : ℕ)^1024*200000000000000^4695 ≤ 200021708496813^4695*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126555382828360859 3125000000000000000 200021708496813 200000000000000 1024 4695 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200021708496813/200000000000000 : ℝ)) (X := (3126555382828360859/3125000000000000000 : ℝ)) (by norm_num) 4695 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3020466135801493/100000000000000000000 : ℝ) ≤ ((1077338243714588149/1077500000000000000 : ℝ)+2*(68119470119/86200000000000 : ℝ)*(2583/25000 : ℝ))^(4695/1024 : ℝ) := by
    rw [show (1077338243714588149/1077500000000000000 : ℝ)+2*(68119470119/86200000000000 : ℝ)*(2583/25000 : ℝ)=(1250016469032373/1250000000000000 : ℝ) by norm_num, show 1+2*(3020466135801493/100000000000000000000 : ℝ)=(50003020466135801493/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1555382828360859/6250000000000000000 : ℝ)+(3020466135801493/100000000000000000000 : ℝ) ≤ ((1077338243714588149/1077500000000000000 : ℝ)+(68119470119/86200000000000 : ℝ)*((8183/50000 : ℝ)+(2583/25000 : ℝ)))^(4695/1024 : ℝ) := by
    rw [show (1077338243714588149/1077500000000000000 : ℝ)+(68119470119/86200000000000 : ℝ)*((8183/50000 : ℝ)+(2583/25000 : ℝ))=(10000608588549817/10000000000000000 : ℝ) by norm_num, show 1+(1555382828360859/6250000000000000000 : ℝ)+(3020466135801493/100000000000000000000 : ℝ)=(100027906591389575237/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1555382828360859/6250000000000000000 : ℝ) ≤ ((1077338243714588149/1077500000000000000 : ℝ)+2*(68119470119/86200000000000 : ℝ)*(8183/50000 : ℝ))^(4695/1024 : ℝ) := by
    rw [show (1077338243714588149/1077500000000000000 : ℝ)+2*(68119470119/86200000000000 : ℝ)*(8183/50000 : ℝ)=(200021708496813/200000000000000 : ℝ) by norm_num, show 1+2*(1555382828360859/6250000000000000000 : ℝ)=(3126555382828360859/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1077338243714588149/1077500000000000000 : ℝ)*(X 1 0+X 2 0)+(68119470119/86200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4695/1024 : ℝ)) (lo := (2583/25000 : ℝ)) (hi := (8183/50000 : ℝ)) (c := (1077338243714588149/1077500000000000000 : ℝ)) (alpha := (68119470119/86200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1077338243714588149/1077500000000000000 : ℝ)*(X 0 1+X 2 1)+(68119470119/86200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4695/1024 : ℝ)) (lo := (2583/25000 : ℝ)) (hi := (8183/50000 : ℝ)) (c := (1077338243714588149/1077500000000000000 : ℝ)) (alpha := (68119470119/86200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1077338243714588149/1077500000000000000 : ℝ)*(X 0 2+X 1 2)+(68119470119/86200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4695/1024 : ℝ)) (lo := (2583/25000 : ℝ)) (hi := (8183/50000 : ℝ)) (c := (1077338243714588149/1077500000000000000 : ℝ)) (alpha := (68119470119/86200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1463216751/10000000000 : ℝ)*X 0 0+(5421964117/10000000000 : ℝ)*X 0 1+(5421963519/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5250897901/10000000000 : ℝ)*X 1 0+(-851628271/5000000000 : ℝ)*X 1 1+(1084392739/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2625448719/5000000000 : ℝ)*X 2 0+(5421963889/10000000000 : ℝ)*X 2 1+(-425814227/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1126581961/2500000000 : ℝ)*X 0 0+(4097501937/10000000000 : ℝ)*X 0 1+(2048750503/5000000000 : ℝ)*X 0 2+(1126581961/2500000000 : ℝ)*X 1 0+(4097501937/10000000000 : ℝ)*X 1 1+(2048750503/5000000000 : ℝ)*X 1 2+(1126581961/2500000000 : ℝ)*X 2 0+(4097501937/10000000000 : ℝ)*X 2 1+(2048750503/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1016574543/5000000000 : ℝ)*X 0 0+(5213133933/10000000000 : ℝ)*X 0 1+(2606567211/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5395335937/10000000000 : ℝ)*X 1 0+(-895501391/5000000000 : ℝ)*X 1 1+(1303283663/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5395337177/10000000000 : ℝ)*X 2 0+(5213133251/10000000000 : ℝ)*X 2 1+(-895501491/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3938230493/10000000000 : ℝ)*X 0 0+(2190599069/5000000000 : ℝ)*X 0 1+(34228117/78125000 : ℝ)*X 0 2+(3938230493/10000000000 : ℝ)*X 1 0+(2190599069/5000000000 : ℝ)*X 1 1+(34228117/78125000 : ℝ)*X 1 2+(3938230493/10000000000 : ℝ)*X 2 0+(2190599069/5000000000 : ℝ)*X 2 1+(34228117/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1912157119/10000000000 : ℝ)*X 0 0+(5064362177/10000000000 : ℝ)*X 0 1+(1090417749/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1307513651/2500000000 : ℝ)*X 1 0+(-1690122387/10000000000 : ℝ)*X 1 1+(5452088867/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((523005509/1000000000 : ℝ)*X 2 0+(54520891/100000000 : ℝ)*X 2 1+(-845060699/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2292937293/5000000000 : ℝ)*X 0 0+(4056503679/10000000000 : ℝ)*X 0 1+(4056501731/10000000000 : ℝ)*X 0 2+(2292937293/5000000000 : ℝ)*X 1 0+(4056503679/10000000000 : ℝ)*X 1 1+(4056501731/10000000000 : ℝ)*X 1 2+(2292937293/5000000000 : ℝ)*X 2 0+(4056503679/10000000000 : ℝ)*X 2 1+(4056501731/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1583224501/10000000000 : ℝ)*X 0 0+(5564538743/10000000000 : ℝ)*X 0 1+(162289579/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5409083691/10000000000 : ℝ)*X 1 0+(-179904193/1000000000 : ℝ)*X 1 1+(1038653239/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5409083603/10000000000 : ℝ)*X 2 0+(2596633171/5000000000 : ℝ)*X 2 1+(-1799041853/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3882561989/10000000000 : ℝ)*X 0 0+(4408141829/10000000000 : ℝ)*X 0 1+(1102035459/2500000000 : ℝ)*X 0 2+(3882561989/10000000000 : ℝ)*X 1 0+(4408141829/10000000000 : ℝ)*X 1 1+(1102035459/2500000000 : ℝ)*X 1 2+(3882561989/10000000000 : ℝ)*X 2 0+(4408141829/10000000000 : ℝ)*X 2 1+(1102035459/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1595_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-32437/50000 : ℝ) ≤ (-8737400524671105149804917865139/13468750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1694581/10000000000000 : ℝ)*(upper0) + (3801223/10000000000000 : ℝ)*(lower2) + (9740037/12500000000000 : ℝ)*(lower3) + (2289421/2500000000000 : ℝ)*(upper5) + (826057744865163/50000000000000 : ℝ)*(major0) + (826057744865163/50000000000000 : ℝ)*(major1) + (826057744865163/50000000000000 : ℝ)*(major2) + (1408724893/12500000000000 : ℝ)*(sp2) + (270574729/25000000000000 : ℝ)*(sp3) + (235655285875311/10000000000000 : ℝ)*(sp4) + (1178243180440237/50000000000000 : ℝ)*(sp5) + (471308317790793/20000000000000 : ℝ)*(sp6) + (193860184430207/20000000000000 : ℝ)*(sp7) + (13299574527/20000000000000 : ℝ)*(sp13) + (19386040088999/2000000000000 : ℝ)*(f.failure) + (235655285875311/10000000000000 : ℝ)*(f.sum) + (3709193391987/538750000000000000000000000 : ℝ)*base66 + (33841897626284213/53875000000000000000000000000000 : ℝ)*base68 + (619212484706784213/53875000000000000000000000000000 : ℝ)*base70 + (26221953930034213/53875000000000000000000000000000 : ℝ)*base72 + (10435270123723/2155000000000000000000000000 : ℝ)*base74 + (40600719862159213/53875000000000000000000000000000 : ℝ)*base76 + (209545646451784213/53875000000000000000000000000000 : ℝ)*base78 + (478475971369840787/53875000000000000000000000000000 : ℝ)*base79 + (16564371071073/2155000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1306833/200000000000000000000 : ℝ)*base90 + (1306833/200000000000000000000 : ℝ)*base92 + (1306833/200000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (3627/6250 : ℝ) ≤ (62531818474301101118358687/107750000000000000000000000 : ℝ) := by norm_num
    linear_combination (18318613/100000000000000 : ℝ)*(lower0) + (26381837/50000000000000 : ℝ)*(upper2) + (124171673/100000000000000 : ℝ)*(upper3) + (78935721/100000000000000 : ℝ)*(lower5) + (5421292387641/312500000000 : ℝ)*(major0) + (5421292387641/312500000000 : ℝ)*(major1) + (5421292387641/312500000000 : ℝ)*(major2) + (2432461147355971/100000000000000 : ℝ)*(sp0) + (121621706996149/5000000000000 : ℝ)*(sp1) + (2432460900409931/100000000000000 : ℝ)*(sp2) + (508910446937483/50000000000000 : ℝ)*(sp3) + (6173651/2500000000000 : ℝ)*(sp6) + (36343337/10000000000000 : ℝ)*(sp7) + (27007432991/100000000000000 : ℝ)*(sp9) + (63613828581771/6250000000000 : ℝ)*(f.failure) + (2432461147355971/100000000000000 : ℝ)*(f.sum) + (324058982089/86200000000000000000000000 : ℝ)*base65 + (2450236516255839/1346875000000000000000000000000 : ℝ)*base68 + (5249177529180839/1346875000000000000000000000000 : ℝ)*base70 + (24079044186143/673437500000000000000000000000 : ℝ)*base71 + (8671224388347/431000000000000000000000000 : ℝ)*base74 + (48081377106661/1346875000000000000000000000000 : ℝ)*base75 + (111869548139173/42089843750000000000000000000 : ℝ)*base77 + (55406755437043339/1346875000000000000000000000000 : ℝ)*base80 + (806829421/134687500000000000000000 : ℝ)*base82 + (3168243/625000000000000000000 : ℝ)*base89 + (3168243/625000000000000000000 : ℝ)*base91 + (3168243/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (2504/3125 : ℝ) ≤ (43170439760281238894315036278809/53875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (53028639/50000000000000 : ℝ)*(lower3) + (345049619/100000000000000 : ℝ)*(upper4) + (2001759/1000000000000 : ℝ)*(lower5) + (1843816895956553/100000000000000 : ℝ)*(major0) + (1843816895956553/100000000000000 : ℝ)*(major1) + (1843816895956553/100000000000000 : ℝ)*(major2) + (413533989/5000000000000 : ℝ)*(sp0) + (53921190321/100000000000000 : ℝ)*(sp1) + (31867089521/20000000000000 : ℝ)*(sp2) + (3609753621/5000000000000 : ℝ)*(sp3) + (644785343614693/25000000000000 : ℝ)*(sp8) + (257909572394823/10000000000000 : ℝ)*(sp9) + (1289495154845473/50000000000000 : ℝ)*(sp10) + (1081701702817187/100000000000000 : ℝ)*(sp11) + (1081773897889607/100000000000000 : ℝ)*(f.failure) + (322393705642319/12500000000000 : ℝ)*(f.sum) + (24038544465467/4310000000000000000000000000 : ℝ)*base65 + (164018175141472103/107750000000000000000000000000000 : ℝ)*base68 + (137430082531472103/107750000000000000000000000000000 : ℝ)*base70 + (659794170417027897/107750000000000000000000000000000 : ℝ)*base71 + (10044392935703/4310000000000000000000000000 : ℝ)*base74 + (300456807744777897/107750000000000000000000000000000 : ℝ)*base75 + (573337295602277897/107750000000000000000000000000000 : ℝ)*base77 + (493612018315777897/107750000000000000000000000000000 : ℝ)*base79 + (13952463679417/4310000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (72056369/10000000000000000000000 : ℝ)*base90 + (72056369/10000000000000000000000 : ℝ)*base92 + (72056369/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-87669/100000 : ℝ) ≤ (-11807595473529837132975761600541/13468750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (217367/3125000000000 : ℝ)*(upper1) + (28444003/100000000000000 : ℝ)*(upper3) + (43057171/100000000000000 : ℝ)*(upper5) + (942555554943647/50000000000000 : ℝ)*(major0) + (942555554943647/50000000000000 : ℝ)*(major1) + (942555554943647/50000000000000 : ℝ)*(major2) + (987918891/50000000000000 : ℝ)*(sp4) + (28966890209/50000000000000 : ℝ)*(sp5) + (40696859927/100000000000000 : ℝ)*(sp6) + (698351151/3125000000000 : ℝ)*(sp7) + (269344108530697/10000000000000 : ℝ)*(sp12) + (1346692563682167/50000000000000 : ℝ)*(sp13) + (107736094571393/4000000000000 : ℝ)*(sp14) + (552989506050439/50000000000000 : ℝ)*(sp15) + (1106001359337709/100000000000000 : ℝ)*(f.failure) + (168340191321547/6250000000000 : ℝ)*(f.sum) + (8419955028887/2155000000000000000000000000 : ℝ)*base66 + (186676467867798097/53875000000000000000000000000000 : ℝ)*base68 + (1953679935181548097/53875000000000000000000000000000 : ℝ)*base70 + (602815748630798097/53875000000000000000000000000000 : ℝ)*base72 + (4436204543217/2155000000000000000000000000 : ℝ)*base74 + (195539196398201903/53875000000000000000000000000000 : ℝ)*base75 + (531543007695048097/53875000000000000000000000000000 : ℝ)*base78 + (253826133772923097/53875000000000000000000000000000 : ℝ)*base80 + (32232657616581/1077500000000000000000000000 : ℝ)*base82 + (63398597/10000000000000000000000 : ℝ)*base89 + (63398597/10000000000000000000000 : ℝ)*base91 + (63398597/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1595_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170443833/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8183/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2583/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(32437/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(3627/6250 : ℝ) else (2504/3125 : ℝ) ≤ X j i ∧ X j i ≤ (87669/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1595_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1595_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170443833/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8183/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2583/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(32437/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(3627/6250 : ℝ) else (2504/3125 : ℝ) ≤ X j i ∧ X j i ≤ (87669/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1595_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4695/1024 : ℝ) ≤ p) (hpb : p ≤ (4699/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170443833/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8183/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2583/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(32437/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(3627/6250 : ℝ) else (2504/3125 : ℝ) ≤ X j i ∧ X j i ≤ (87669/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1595_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1213_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:08:02.448238+00:00
-- url     : https://prove2.me/submissions/1faa36ff-bc40-4f1b-b0fc-2f2ee6504579

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
theorem support_rectangle_w1213_box_0 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2008794473/10000000000 : ℝ)*x 0 + (53752743/100000000 : ℝ)*x 1 + (5375273953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2008794473/10000000000 : ℝ)^4203 ≤ (2395694063319/20000000000000 : ℝ)^3179 := by
    have hnat : (2008794473 : ℕ)^4203*20000000000000^3179 ≤ 2395694063319^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008794473 10000000000 2395694063319 20000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (53752743/100000000 : ℝ)^4203 ≤ (22005383358367/50000000000000 : ℝ)^3179 := by
    have hnat : (53752743 : ℕ)^4203*50000000000000^3179 ≤ 22005383358367^3179*100000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53752743 100000000 22005383358367 50000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5375273953/10000000000 : ℝ)^4203 ≤ (22005381480233/50000000000000 : ℝ)^3179 := by
    have hnat : (5375273953 : ℕ)^4203*50000000000000^3179 ≤ 22005381480233^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375273953 10000000000 22005381480233 50000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2008794473/10000000000 : ℝ), (53752743/100000000 : ℝ), (5375273953/10000000000 : ℝ)] ![(2395694063319/20000000000000 : ℝ), (22005383358367/50000000000000 : ℝ), (22005381480233/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2008794473/10000000000 : ℝ)|^4203 ≤ (2395694063319/20000000000000 : ℝ)^3179
        have hw : |(-2008794473/10000000000 : ℝ)|=(2008794473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(53752743/100000000 : ℝ)|^4203 ≤ (22005383358367/50000000000000 : ℝ)^3179
        have hw : |(53752743/100000000 : ℝ)|=(53752743/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5375273953/10000000000 : ℝ)|^4203 ≤ (22005381480233/50000000000000 : ℝ)^3179
        have hw : |(5375273953/10000000000 : ℝ)|=(5375273953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_box_1 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5296585137/10000000000 : ℝ)*x 0 + (-528919727/2500000000 : ℝ)*x 1 + (5375274293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296585137/10000000000 : ℝ)^4203 ≤ (10790243248937/25000000000000 : ℝ)^3179 := by
    have hnat : (5296585137 : ℕ)^4203*25000000000000^3179 ≤ 10790243248937^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296585137 10000000000 10790243248937 25000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (528919727/2500000000 : ℝ)^4203 ≤ (12828260351689/100000000000000 : ℝ)^3179 := by
    have hnat : (528919727 : ℕ)^4203*100000000000000^3179 ≤ 12828260351689^3179*2500000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528919727 2500000000 12828260351689 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5375274293/10000000000 : ℝ)^4203 ≤ (44010766640959/100000000000000 : ℝ)^3179 := by
    have hnat : (5375274293 : ℕ)^4203*100000000000000^3179 ≤ 44010766640959^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375274293 10000000000 44010766640959 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296585137/10000000000 : ℝ), (-528919727/2500000000 : ℝ), (5375274293/10000000000 : ℝ)] ![(10790243248937/25000000000000 : ℝ), (12828260351689/100000000000000 : ℝ), (44010766640959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296585137/10000000000 : ℝ)|^4203 ≤ (10790243248937/25000000000000 : ℝ)^3179
        have hw : |(5296585137/10000000000 : ℝ)|=(5296585137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-528919727/2500000000 : ℝ)|^4203 ≤ (12828260351689/100000000000000 : ℝ)^3179
        have hw : |(-528919727/2500000000 : ℝ)|=(528919727/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5375274293/10000000000 : ℝ)|^4203 ≤ (44010766640959/100000000000000 : ℝ)^3179
        have hw : |(5375274293/10000000000 : ℝ)|=(5375274293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_box_2 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5296585399/10000000000 : ℝ)*x 0 + (5375274053/10000000000 : ℝ)*x 1 + (-2115678879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296585399/10000000000 : ℝ)^4203 ≤ (10790243954613/25000000000000 : ℝ)^3179 := by
    have hnat : (5296585399 : ℕ)^4203*25000000000000^3179 ≤ 10790243954613^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296585399 10000000000 10790243954613 25000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5375274053/10000000000 : ℝ)^4203 ≤ (11002691010741/25000000000000 : ℝ)^3179 := by
    have hnat : (5375274053 : ℕ)^4203*25000000000000^3179 ≤ 11002691010741^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375274053 10000000000 11002691010741 25000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2115678879/10000000000 : ℝ)^4203 ≤ (1282826011921/10000000000000 : ℝ)^3179 := by
    have hnat : (2115678879 : ℕ)^4203*10000000000000^3179 ≤ 1282826011921^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115678879 10000000000 1282826011921 10000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296585399/10000000000 : ℝ), (5375274053/10000000000 : ℝ), (-2115678879/10000000000 : ℝ)] ![(10790243954613/25000000000000 : ℝ), (11002691010741/25000000000000 : ℝ), (1282826011921/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296585399/10000000000 : ℝ)|^4203 ≤ (10790243954613/25000000000000 : ℝ)^3179
        have hw : |(5296585399/10000000000 : ℝ)|=(5296585399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5375274053/10000000000 : ℝ)|^4203 ≤ (11002691010741/25000000000000 : ℝ)^3179
        have hw : |(5375274053/10000000000 : ℝ)|=(5375274053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2115678879/10000000000 : ℝ)|^4203 ≤ (1282826011921/10000000000000 : ℝ)^3179
        have hw : |(-2115678879/10000000000 : ℝ)|=(2115678879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_box_3 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (557696983/1250000000 : ℝ)*x 0 + (4303424271/10000000000 : ℝ)*x 1 + (2151712327/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (557696983/1250000000 : ℝ)^4203 ≤ (34401992379973/100000000000000 : ℝ)^3179 := by
    have hnat : (557696983 : ℕ)^4203*100000000000000^3179 ≤ 34401992379973^3179*1250000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      557696983 1250000000 34401992379973 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4303424271/10000000000 : ℝ)^4203 ≤ (32799001871861/100000000000000 : ℝ)^3179 := by
    have hnat : (4303424271 : ℕ)^4203*100000000000000^3179 ≤ 32799001871861^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4303424271 10000000000 32799001871861 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2151712327/5000000000 : ℝ)^4203 ≤ (3279900573121/10000000000000 : ℝ)^3179 := by
    have hnat : (2151712327 : ℕ)^4203*10000000000000^3179 ≤ 3279900573121^3179*5000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151712327 5000000000 3279900573121 10000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(557696983/1250000000 : ℝ), (4303424271/10000000000 : ℝ), (2151712327/5000000000 : ℝ)] ![(34401992379973/100000000000000 : ℝ), (32799001871861/100000000000000 : ℝ), (3279900573121/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(557696983/1250000000 : ℝ)|^4203 ≤ (34401992379973/100000000000000 : ℝ)^3179
        have hw : |(557696983/1250000000 : ℝ)|=(557696983/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4303424271/10000000000 : ℝ)|^4203 ≤ (32799001871861/100000000000000 : ℝ)^3179
        have hw : |(4303424271/10000000000 : ℝ)|=(4303424271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2151712327/5000000000 : ℝ)|^4203 ≤ (3279900573121/10000000000000 : ℝ)^3179
        have hw : |(2151712327/5000000000 : ℝ)|=(2151712327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_box_4 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-564842531/2500000000 : ℝ)*x 0 + (2640990863/5000000000 : ℝ)*x 1 + (2640990889/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (564842531/2500000000 : ℝ)^4203 ≤ (13992578618049/100000000000000 : ℝ)^3179 := by
    have hnat : (564842531 : ℕ)^4203*100000000000000^3179 ≤ 13992578618049^3179*2500000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564842531 2500000000 13992578618049 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640990863/5000000000 : ℝ)^4203 ≤ (43003710405297/100000000000000 : ℝ)^3179 := by
    have hnat : (2640990863 : ℕ)^4203*100000000000000^3179 ≤ 43003710405297^3179*5000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640990863 5000000000 43003710405297 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2640990889/5000000000 : ℝ)^4203 ≤ (43003710965031/100000000000000 : ℝ)^3179 := by
    have hnat : (2640990889 : ℕ)^4203*100000000000000^3179 ≤ 43003710965031^3179*5000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640990889 5000000000 43003710965031 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-564842531/2500000000 : ℝ), (2640990863/5000000000 : ℝ), (2640990889/5000000000 : ℝ)] ![(13992578618049/100000000000000 : ℝ), (43003710405297/100000000000000 : ℝ), (43003710965031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-564842531/2500000000 : ℝ)|^4203 ≤ (13992578618049/100000000000000 : ℝ)^3179
        have hw : |(-564842531/2500000000 : ℝ)|=(564842531/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640990863/5000000000 : ℝ)|^4203 ≤ (43003710405297/100000000000000 : ℝ)^3179
        have hw : |(2640990863/5000000000 : ℝ)|=(2640990863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2640990889/5000000000 : ℝ)|^4203 ≤ (43003710965031/100000000000000 : ℝ)^3179
        have hw : |(2640990889/5000000000 : ℝ)|=(2640990889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_box_5 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5362392267/10000000000 : ℝ)*x 0 + (-1076290679/5000000000 : ℝ)*x 1 + (660247701/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362392267/10000000000 : ℝ)^4203 ≤ (21935686400007/50000000000000 : ℝ)^3179 := by
    have hnat : (5362392267 : ℕ)^4203*50000000000000^3179 ≤ 21935686400007^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362392267 10000000000 21935686400007 50000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1076290679/5000000000 : ℝ)^4203 ≤ (1312491805291/10000000000000 : ℝ)^3179 := by
    have hnat : (1076290679 : ℕ)^4203*10000000000000^3179 ≤ 1312491805291^3179*5000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076290679 5000000000 1312491805291 10000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (660247701/1250000000 : ℝ)^4203 ≤ (43003709135133/100000000000000 : ℝ)^3179 := by
    have hnat : (660247701 : ℕ)^4203*100000000000000^3179 ≤ 43003709135133^3179*1250000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660247701 1250000000 43003709135133 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362392267/10000000000 : ℝ), (-1076290679/5000000000 : ℝ), (660247701/1250000000 : ℝ)] ![(21935686400007/50000000000000 : ℝ), (1312491805291/10000000000000 : ℝ), (43003709135133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362392267/10000000000 : ℝ)|^4203 ≤ (21935686400007/50000000000000 : ℝ)^3179
        have hw : |(5362392267/10000000000 : ℝ)|=(5362392267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1076290679/5000000000 : ℝ)|^4203 ≤ (1312491805291/10000000000000 : ℝ)^3179
        have hw : |(-1076290679/5000000000 : ℝ)|=(1076290679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(660247701/1250000000 : ℝ)|^4203 ≤ (43003709135133/100000000000000 : ℝ)^3179
        have hw : |(660247701/1250000000 : ℝ)|=(660247701/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_box_6 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5362391901/10000000000 : ℝ)*x 0 + (5281981879/10000000000 : ℝ)*x 1 + (-2152581487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362391901/10000000000 : ℝ)^4203 ≤ (10967842210283/25000000000000 : ℝ)^3179 := by
    have hnat : (5362391901 : ℕ)^4203*25000000000000^3179 ≤ 10967842210283^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362391901 10000000000 10967842210283 25000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5281981879/10000000000 : ℝ)^4203 ≤ (8600742410441/20000000000000 : ℝ)^3179 := by
    have hnat : (5281981879 : ℕ)^4203*20000000000000^3179 ≤ 8600742410441^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281981879 10000000000 8600742410441 20000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2152581487/10000000000 : ℝ)^4203 ≤ (656245954641/5000000000000 : ℝ)^3179 := by
    have hnat : (2152581487 : ℕ)^4203*5000000000000^3179 ≤ 656245954641^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152581487 10000000000 656245954641 5000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362391901/10000000000 : ℝ), (5281981879/10000000000 : ℝ), (-2152581487/10000000000 : ℝ)] ![(10967842210283/25000000000000 : ℝ), (8600742410441/20000000000000 : ℝ), (656245954641/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362391901/10000000000 : ℝ)|^4203 ≤ (10967842210283/25000000000000 : ℝ)^3179
        have hw : |(5362391901/10000000000 : ℝ)|=(5362391901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5281981879/10000000000 : ℝ)|^4203 ≤ (8600742410441/20000000000000 : ℝ)^3179
        have hw : |(5281981879/10000000000 : ℝ)|=(5281981879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2152581487/10000000000 : ℝ)|^4203 ≤ (656245954641/5000000000000 : ℝ)^3179
        have hw : |(-2152581487/10000000000 : ℝ)|=(2152581487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_box_7 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530946181/1250000000 : ℝ)*x 0 + (137825231/312500000 : ℝ)*x 1 + (4410407339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530946181/1250000000 : ℝ)^4203 ≤ (32237353467/100000000000 : ℝ)^3179 := by
    have hnat : (530946181 : ℕ)^4203*100000000000^3179 ≤ 32237353467^3179*1250000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530946181 1250000000 32237353467 100000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (137825231/312500000 : ℝ)^4203 ≤ (6776264705571/20000000000000 : ℝ)^3179 := by
    have hnat : (137825231 : ℕ)^4203*20000000000000^3179 ≤ 6776264705571^3179*312500000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137825231 312500000 6776264705571 20000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4410407339/10000000000 : ℝ)^4203 ≤ (2117582686847/6250000000000 : ℝ)^3179 := by
    have hnat : (4410407339 : ℕ)^4203*6250000000000^3179 ≤ 2117582686847^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4410407339 10000000000 2117582686847 6250000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530946181/1250000000 : ℝ), (137825231/312500000 : ℝ), (4410407339/10000000000 : ℝ)] ![(32237353467/100000000000 : ℝ), (6776264705571/20000000000000 : ℝ), (2117582686847/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530946181/1250000000 : ℝ)|^4203 ≤ (32237353467/100000000000 : ℝ)^3179
        have hw : |(530946181/1250000000 : ℝ)|=(530946181/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(137825231/312500000 : ℝ)|^4203 ≤ (6776264705571/20000000000000 : ℝ)^3179
        have hw : |(137825231/312500000 : ℝ)|=(137825231/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4410407339/10000000000 : ℝ)|^4203 ≤ (2117582686847/6250000000000 : ℝ)^3179
        have hw : |(4410407339/10000000000 : ℝ)|=(4410407339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_box_8 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-551723213/2500000000 : ℝ)*x 0 + (2609200227/5000000000 : ℝ)*x 1 + (5384886203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (551723213/2500000000 : ℝ)^4203 ≤ (13564509209217/100000000000000 : ℝ)^3179 := by
    have hnat : (551723213 : ℕ)^4203*100000000000000^3179 ≤ 13564509209217^3179*2500000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551723213 2500000000 13564509209217 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609200227/5000000000 : ℝ)^4203 ≤ (42320645431707/100000000000000 : ℝ)^3179 := by
    have hnat : (2609200227 : ℕ)^4203*100000000000000^3179 ≤ 42320645431707^3179*5000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609200227 5000000000 42320645431707 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5384886203/10000000000 : ℝ)^4203 ≤ (44114845343139/100000000000000 : ℝ)^3179 := by
    have hnat : (5384886203 : ℕ)^4203*100000000000000^3179 ≤ 44114845343139^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384886203 10000000000 44114845343139 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-551723213/2500000000 : ℝ), (2609200227/5000000000 : ℝ), (5384886203/10000000000 : ℝ)] ![(13564509209217/100000000000000 : ℝ), (42320645431707/100000000000000 : ℝ), (44114845343139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-551723213/2500000000 : ℝ)|^4203 ≤ (13564509209217/100000000000000 : ℝ)^3179
        have hw : |(-551723213/2500000000 : ℝ)|=(551723213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609200227/5000000000 : ℝ)|^4203 ≤ (42320645431707/100000000000000 : ℝ)^3179
        have hw : |(2609200227/5000000000 : ℝ)|=(2609200227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5384886203/10000000000 : ℝ)|^4203 ≤ (44114845343139/100000000000000 : ℝ)^3179
        have hw : |(5384886203/10000000000 : ℝ)|=(5384886203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_box_9 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1322450529/2500000000 : ℝ)*x 0 + (-2111808831/10000000000 : ℝ)*x 1 + (673110773/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322450529/2500000000 : ℝ)^4203 ≤ (43087909965261/100000000000000 : ℝ)^3179 := by
    have hnat : (1322450529 : ℕ)^4203*100000000000000^3179 ≤ 43087909965261^3179*2500000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322450529 2500000000 43087909965261 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2111808831/10000000000 : ℝ)^4203 ≤ (12797244875229/100000000000000 : ℝ)^3179 := by
    have hnat : (2111808831 : ℕ)^4203*100000000000000^3179 ≤ 12797244875229^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111808831 10000000000 12797244875229 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673110773/1250000000 : ℝ)^4203 ≤ (22057422568673/50000000000000 : ℝ)^3179 := by
    have hnat : (673110773 : ℕ)^4203*50000000000000^3179 ≤ 22057422568673^3179*1250000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673110773 1250000000 22057422568673 50000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322450529/2500000000 : ℝ), (-2111808831/10000000000 : ℝ), (673110773/1250000000 : ℝ)] ![(43087909965261/100000000000000 : ℝ), (12797244875229/100000000000000 : ℝ), (22057422568673/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322450529/2500000000 : ℝ)|^4203 ≤ (43087909965261/100000000000000 : ℝ)^3179
        have hw : |(1322450529/2500000000 : ℝ)|=(1322450529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2111808831/10000000000 : ℝ)|^4203 ≤ (12797244875229/100000000000000 : ℝ)^3179
        have hw : |(-2111808831/10000000000 : ℝ)|=(2111808831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673110773/1250000000 : ℝ)|^4203 ≤ (22057422568673/50000000000000 : ℝ)^3179
        have hw : |(673110773/1250000000 : ℝ)|=(673110773/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_box_10 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289802141/10000000000 : ℝ)*x 0 + (1076977241/2000000000 : ℝ)*x 1 + (-2111808769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289802141/10000000000 : ℝ)^4203 ≤ (43087910234491/100000000000000 : ℝ)^3179 := by
    have hnat : (5289802141 : ℕ)^4203*100000000000000^3179 ≤ 43087910234491^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289802141 10000000000 43087910234491 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1076977241/2000000000 : ℝ)^4203 ≤ (44114845364801/100000000000000 : ℝ)^3179 := by
    have hnat : (1076977241 : ℕ)^4203*100000000000000^3179 ≤ 44114845364801^3179*2000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076977241 2000000000 44114845364801 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2111808769/10000000000 : ℝ)^4203 ≤ (99978471707/781250000000 : ℝ)^3179 := by
    have hnat : (2111808769 : ℕ)^4203*781250000000^3179 ≤ 99978471707^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111808769 10000000000 99978471707 781250000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289802141/10000000000 : ℝ), (1076977241/2000000000 : ℝ), (-2111808769/10000000000 : ℝ)] ![(43087910234491/100000000000000 : ℝ), (44114845364801/100000000000000 : ℝ), (99978471707/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289802141/10000000000 : ℝ)|^4203 ≤ (43087910234491/100000000000000 : ℝ)^3179
        have hw : |(5289802141/10000000000 : ℝ)|=(5289802141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1076977241/2000000000 : ℝ)|^4203 ≤ (44114845364801/100000000000000 : ℝ)^3179
        have hw : |(1076977241/2000000000 : ℝ)|=(1076977241/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2111808769/10000000000 : ℝ)|^4203 ≤ (99978471707/781250000000 : ℝ)^3179
        have hw : |(-2111808769/10000000000 : ℝ)|=(2111808769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_box_11 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4483352701/10000000000 : ℝ)*x 0 + (2146197743/5000000000 : ℝ)*x 1 + (4292395551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4483352701/10000000000 : ℝ)^4203 ≤ (17312084887759/50000000000000 : ℝ)^3179 := by
    have hnat : (4483352701 : ℕ)^4203*50000000000000^3179 ≤ 17312084887759^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483352701 10000000000 17312084887759 50000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2146197743/5000000000 : ℝ)^4203 ≤ (32687914780189/100000000000000 : ℝ)^3179 := by
    have hnat : (2146197743 : ℕ)^4203*100000000000000^3179 ≤ 32687914780189^3179*5000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2146197743 5000000000 32687914780189 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4292395551/10000000000 : ℝ)^4203 ≤ (32687915434629/100000000000000 : ℝ)^3179 := by
    have hnat : (4292395551 : ℕ)^4203*100000000000000^3179 ≤ 32687915434629^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4292395551 10000000000 32687915434629 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4483352701/10000000000 : ℝ), (2146197743/5000000000 : ℝ), (4292395551/10000000000 : ℝ)] ![(17312084887759/50000000000000 : ℝ), (32687914780189/100000000000000 : ℝ), (32687915434629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4483352701/10000000000 : ℝ)|^4203 ≤ (17312084887759/50000000000000 : ℝ)^3179
        have hw : |(4483352701/10000000000 : ℝ)|=(4483352701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2146197743/5000000000 : ℝ)|^4203 ≤ (32687914780189/100000000000000 : ℝ)^3179
        have hw : |(2146197743/5000000000 : ℝ)|=(2146197743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4292395551/10000000000 : ℝ)|^4203 ≤ (32687915434629/100000000000000 : ℝ)^3179
        have hw : |(4292395551/10000000000 : ℝ)|=(4292395551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_box_12 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-3221169/15625000 : ℝ)*x 0 + (5437627443/10000000000 : ℝ)*x 1 + (5273913651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3221169/15625000 : ℝ)^4203 ≤ (12396117741013/100000000000000 : ℝ)^3179 := by
    have hnat : (3221169 : ℕ)^4203*100000000000000^3179 ≤ 12396117741013^3179*15625000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3221169 15625000 12396117741013 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5437627443/10000000000 : ℝ)^4203 ≤ (22343498036453/50000000000000 : ℝ)^3179 := by
    have hnat : (5437627443 : ℕ)^4203*50000000000000^3179 ≤ 22343498036453^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437627443 10000000000 22343498036453 50000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5273913651/10000000000 : ℝ)^4203 ≤ (8583377235387/20000000000000 : ℝ)^3179 := by
    have hnat : (5273913651 : ℕ)^4203*20000000000000^3179 ≤ 8583377235387^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273913651 10000000000 8583377235387 20000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3221169/15625000 : ℝ), (5437627443/10000000000 : ℝ), (5273913651/10000000000 : ℝ)] ![(12396117741013/100000000000000 : ℝ), (22343498036453/50000000000000 : ℝ), (8583377235387/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3221169/15625000 : ℝ)|^4203 ≤ (12396117741013/100000000000000 : ℝ)^3179
        have hw : |(-3221169/15625000 : ℝ)|=(3221169/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5437627443/10000000000 : ℝ)|^4203 ≤ (22343498036453/50000000000000 : ℝ)^3179
        have hw : |(5437627443/10000000000 : ℝ)|=(5437627443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5273913651/10000000000 : ℝ)|^4203 ≤ (8583377235387/20000000000000 : ℝ)^3179
        have hw : |(5273913651/10000000000 : ℝ)|=(5273913651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_box_13 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1342020191/2500000000 : ℝ)*x 0 + (-107785833/500000000 : ℝ)*x 1 + (1318478449/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342020191/2500000000 : ℝ)^4203 ≤ (43932913611043/100000000000000 : ℝ)^3179 := by
    have hnat : (1342020191 : ℕ)^4203*100000000000000^3179 ≤ 43932913611043^3179*2500000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342020191 2500000000 43932913611043 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107785833/500000000 : ℝ)^4203 ≤ (3287549659203/25000000000000 : ℝ)^3179 := by
    have hnat : (107785833 : ℕ)^4203*25000000000000^3179 ≤ 3287549659203^3179*500000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107785833 500000000 3287549659203 25000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1318478449/2500000000 : ℝ)^4203 ≤ (21458443868481/50000000000000 : ℝ)^3179 := by
    have hnat : (1318478449 : ℕ)^4203*50000000000000^3179 ≤ 21458443868481^3179*2500000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318478449 2500000000 21458443868481 50000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342020191/2500000000 : ℝ), (-107785833/500000000 : ℝ), (1318478449/2500000000 : ℝ)] ![(43932913611043/100000000000000 : ℝ), (3287549659203/25000000000000 : ℝ), (21458443868481/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342020191/2500000000 : ℝ)|^4203 ≤ (43932913611043/100000000000000 : ℝ)^3179
        have hw : |(1342020191/2500000000 : ℝ)|=(1342020191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-107785833/500000000 : ℝ)|^4203 ≤ (3287549659203/25000000000000 : ℝ)^3179
        have hw : |(-107785833/500000000 : ℝ)|=(107785833/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1318478449/2500000000 : ℝ)|^4203 ≤ (21458443868481/50000000000000 : ℝ)^3179
        have hw : |(1318478449/2500000000 : ℝ)|=(1318478449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_box_14 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1342020317/2500000000 : ℝ)*x 0 + (527391361/1000000000 : ℝ)*x 1 + (-269464529/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342020317/2500000000 : ℝ)^4203 ≤ (274580744153/625000000000 : ℝ)^3179 := by
    have hnat : (1342020317 : ℕ)^4203*625000000000^3179 ≤ 274580744153^3179*2500000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342020317 2500000000 274580744153 625000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (527391361/1000000000 : ℝ)^4203 ≤ (2682305358489/6250000000000 : ℝ)^3179 := by
    have hnat : (527391361 : ℕ)^4203*6250000000000^3179 ≤ 2682305358489^3179*1000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527391361 1000000000 2682305358489 6250000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269464529/1250000000 : ℝ)^4203 ≤ (13150195184951/100000000000000 : ℝ)^3179 := by
    have hnat : (269464529 : ℕ)^4203*100000000000000^3179 ≤ 13150195184951^3179*1250000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269464529 1250000000 13150195184951 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342020317/2500000000 : ℝ), (527391361/1000000000 : ℝ), (-269464529/1250000000 : ℝ)] ![(274580744153/625000000000 : ℝ), (2682305358489/6250000000000 : ℝ), (13150195184951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342020317/2500000000 : ℝ)|^4203 ≤ (274580744153/625000000000 : ℝ)^3179
        have hw : |(1342020317/2500000000 : ℝ)|=(1342020317/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(527391361/1000000000 : ℝ)|^4203 ≤ (2682305358489/6250000000000 : ℝ)^3179
        have hw : |(527391361/1000000000 : ℝ)|=(527391361/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-269464529/1250000000 : ℝ)|^4203 ≤ (13150195184951/100000000000000 : ℝ)^3179
        have hw : |(-269464529/1250000000 : ℝ)|=(269464529/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_box_15 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4228829571/10000000000 : ℝ)*x 0 + (1104913829/2500000000 : ℝ)*x 1 + (2209827081/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4228829571/10000000000 : ℝ)^4203 ≤ (16024722688757/50000000000000 : ℝ)^3179 := by
    have hnat : (4228829571 : ℕ)^4203*50000000000000^3179 ≤ 16024722688757^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228829571 10000000000 16024722688757 50000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1104913829/2500000000 : ℝ)^4203 ≤ (16987641584091/50000000000000 : ℝ)^3179 := by
    have hnat : (1104913829 : ℕ)^4203*50000000000000^3179 ≤ 16987641584091^3179*2500000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104913829 2500000000 16987641584091 50000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2209827081/5000000000 : ℝ)^4203 ≤ (33975271439497/100000000000000 : ℝ)^3179 := by
    have hnat : (2209827081 : ℕ)^4203*100000000000000^3179 ≤ 33975271439497^3179*5000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209827081 5000000000 33975271439497 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4228829571/10000000000 : ℝ), (1104913829/2500000000 : ℝ), (2209827081/5000000000 : ℝ)] ![(16024722688757/50000000000000 : ℝ), (16987641584091/50000000000000 : ℝ), (33975271439497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4228829571/10000000000 : ℝ)|^4203 ≤ (16024722688757/50000000000000 : ℝ)^3179
        have hw : |(4228829571/10000000000 : ℝ)|=(4228829571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1104913829/2500000000 : ℝ)|^4203 ≤ (16987641584091/50000000000000 : ℝ)^3179
        have hw : |(1104913829/2500000000 : ℝ)|=(1104913829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2209827081/5000000000 : ℝ)|^4203 ≤ (33975271439497/100000000000000 : ℝ)^3179
        have hw : |(2209827081/5000000000 : ℝ)|=(2209827081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1213_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37715219/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1761/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2861/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62241/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29677/50000 : ℝ) ∧ (80023/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (41641/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1761/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2861/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1761/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2861/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1761/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2861/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1761/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2861/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1761/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2861/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1761/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2861/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2861/25000 : ℝ) ^ (8405/2048 : ℝ) ≤ (2737977097682993/20000000000000000000 : ℝ) := by
    have hpowers : (2861/25000 : ℝ)^8405 ≤ (2737977097682993/20000000000000000000 : ℝ)^2048 := by
      have hnat : (2861 : ℕ)^8405*20000000000000000000^2048 ≤ 2737977097682993^2048*25000^8405 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2861 25000 2737977097682993 20000000000000000000 8405 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2861/25000 : ℝ)) (X := (2737977097682993/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8405 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1761/12500 : ℝ) ^ (8405/2048 : ℝ) ≤ (803182777435321/2500000000000000000 : ℝ) := by
    have hpowers : (1761/12500 : ℝ)^8405 ≤ (803182777435321/2500000000000000000 : ℝ)^2048 := by
      have hnat : (1761 : ℕ)^8405*2500000000000000000^2048 ≤ 803182777435321^2048*12500^8405 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1761 12500 803182777435321 2500000000000000000 8405 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1761/12500 : ℝ)) (X := (803182777435321/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8405 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002737977097682993/10000000000000000000 : ℝ) ≤ (400026683148569/400000000000000 : ℝ) ^ (8405/2048 : ℝ) := by
    have hpowers : (10002737977097682993/10000000000000000000 : ℝ)^2048 ≤ (400026683148569/400000000000000 : ℝ)^8405 := by
      have hnat : (10002737977097682993 : ℕ)^2048*400000000000000^8405 ≤ 400026683148569^8405*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002737977097682993 10000000000000000000 400026683148569 400000000000000 2048 8405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400026683148569/400000000000000 : ℝ)) (X := (10002737977097682993/10000000000000000000 : ℝ)) (by norm_num) 8405 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009163439317165561/20000000000000000000 : ℝ) ≤ (10001116208980421/10000000000000000 : ℝ) ^ (8405/2048 : ℝ) := by
    have hpowers : (20009163439317165561/20000000000000000000 : ℝ)^2048 ≤ (10001116208980421/10000000000000000 : ℝ)^8405 := by
      have hnat : (20009163439317165561 : ℕ)^2048*10000000000000000^8405 ≤ 10001116208980421^8405*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009163439317165561 20000000000000000000 10001116208980421 10000000000000000 2048 8405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001116208980421/10000000000000000 : ℝ)) (X := (20009163439317165561/20000000000000000000 : ℝ)) (by norm_num) 8405 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (1250803182777435321/1250000000000000000 : ℝ) ≤ (10001565339246617/10000000000000000 : ℝ) ^ (8405/2048 : ℝ) := by
    have hpowers : (1250803182777435321/1250000000000000000 : ℝ)^2048 ≤ (10001565339246617/10000000000000000 : ℝ)^8405 := by
      have hnat : (1250803182777435321 : ℕ)^2048*10000000000000000^8405 ≤ 10001565339246617^8405*1250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250803182777435321 1250000000000000000 10001565339246617 10000000000000000 2048 8405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001565339246617/10000000000000000 : ℝ)) (X := (1250803182777435321/1250000000000000000 : ℝ)) (by norm_num) 8405 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2737977097682993/20000000000000000000 : ℝ) ≤ ((6607871015646929213/6610000000000000000 : ℝ)+2*(112282566549/66100000000000 : ℝ)*(2861/25000 : ℝ))^(8405/2048 : ℝ) := by
    rw [show (6607871015646929213/6610000000000000000 : ℝ)+2*(112282566549/66100000000000 : ℝ)*(2861/25000 : ℝ)=(400026683148569/400000000000000 : ℝ) by norm_num, show 1+2*(2737977097682993/20000000000000000000 : ℝ)=(10002737977097682993/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(803182777435321/2500000000000000000 : ℝ)+(2737977097682993/20000000000000000000 : ℝ) ≤ ((6607871015646929213/6610000000000000000 : ℝ)+(112282566549/66100000000000 : ℝ)*((1761/12500 : ℝ)+(2861/25000 : ℝ)))^(8405/2048 : ℝ) := by
    rw [show (6607871015646929213/6610000000000000000 : ℝ)+(112282566549/66100000000000 : ℝ)*((1761/12500 : ℝ)+(2861/25000 : ℝ))=(10001116208980421/10000000000000000 : ℝ) by norm_num, show 1+(803182777435321/2500000000000000000 : ℝ)+(2737977097682993/20000000000000000000 : ℝ)=(20009163439317165561/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(803182777435321/2500000000000000000 : ℝ) ≤ ((6607871015646929213/6610000000000000000 : ℝ)+2*(112282566549/66100000000000 : ℝ)*(1761/12500 : ℝ))^(8405/2048 : ℝ) := by
    rw [show (6607871015646929213/6610000000000000000 : ℝ)+2*(112282566549/66100000000000 : ℝ)*(1761/12500 : ℝ)=(10001565339246617/10000000000000000 : ℝ) by norm_num, show 1+2*(803182777435321/2500000000000000000 : ℝ)=(1250803182777435321/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6607871015646929213/6610000000000000000 : ℝ)*(X 1 0+X 2 0)+(112282566549/66100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8405/2048 : ℝ)) (lo := (2861/25000 : ℝ)) (hi := (1761/12500 : ℝ)) (c := (6607871015646929213/6610000000000000000 : ℝ)) (alpha := (112282566549/66100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6607871015646929213/6610000000000000000 : ℝ)*(X 0 1+X 2 1)+(112282566549/66100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8405/2048 : ℝ)) (lo := (2861/25000 : ℝ)) (hi := (1761/12500 : ℝ)) (c := (6607871015646929213/6610000000000000000 : ℝ)) (alpha := (112282566549/66100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6607871015646929213/6610000000000000000 : ℝ)*(X 0 2+X 1 2)+(112282566549/66100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8405/2048 : ℝ)) (lo := (2861/25000 : ℝ)) (hi := (1761/12500 : ℝ)) (c := (6607871015646929213/6610000000000000000 : ℝ)) (alpha := (112282566549/66100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2008794473/10000000000 : ℝ)*X 0 0+(53752743/100000000 : ℝ)*X 0 1+(5375273953/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5296585137/10000000000 : ℝ)*X 1 0+(-528919727/2500000000 : ℝ)*X 1 1+(5375274293/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5296585399/10000000000 : ℝ)*X 2 0+(5375274053/10000000000 : ℝ)*X 2 1+(-2115678879/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((557696983/1250000000 : ℝ)*X 0 0+(4303424271/10000000000 : ℝ)*X 0 1+(2151712327/5000000000 : ℝ)*X 0 2+(557696983/1250000000 : ℝ)*X 1 0+(4303424271/10000000000 : ℝ)*X 1 1+(2151712327/5000000000 : ℝ)*X 1 2+(557696983/1250000000 : ℝ)*X 2 0+(4303424271/10000000000 : ℝ)*X 2 1+(2151712327/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-564842531/2500000000 : ℝ)*X 0 0+(2640990863/5000000000 : ℝ)*X 0 1+(2640990889/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5362392267/10000000000 : ℝ)*X 1 0+(-1076290679/5000000000 : ℝ)*X 1 1+(660247701/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5362391901/10000000000 : ℝ)*X 2 0+(5281981879/10000000000 : ℝ)*X 2 1+(-2152581487/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((530946181/1250000000 : ℝ)*X 0 0+(137825231/312500000 : ℝ)*X 0 1+(4410407339/10000000000 : ℝ)*X 0 2+(530946181/1250000000 : ℝ)*X 1 0+(137825231/312500000 : ℝ)*X 1 1+(4410407339/10000000000 : ℝ)*X 1 2+(530946181/1250000000 : ℝ)*X 2 0+(137825231/312500000 : ℝ)*X 2 1+(4410407339/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-551723213/2500000000 : ℝ)*X 0 0+(2609200227/5000000000 : ℝ)*X 0 1+(5384886203/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1322450529/2500000000 : ℝ)*X 1 0+(-2111808831/10000000000 : ℝ)*X 1 1+(673110773/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5289802141/10000000000 : ℝ)*X 2 0+(1076977241/2000000000 : ℝ)*X 2 1+(-2111808769/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4483352701/10000000000 : ℝ)*X 0 0+(2146197743/5000000000 : ℝ)*X 0 1+(4292395551/10000000000 : ℝ)*X 0 2+(4483352701/10000000000 : ℝ)*X 1 0+(2146197743/5000000000 : ℝ)*X 1 1+(4292395551/10000000000 : ℝ)*X 1 2+(4483352701/10000000000 : ℝ)*X 2 0+(2146197743/5000000000 : ℝ)*X 2 1+(4292395551/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-3221169/15625000 : ℝ)*X 0 0+(5437627443/10000000000 : ℝ)*X 0 1+(5273913651/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1342020191/2500000000 : ℝ)*X 1 0+(-107785833/500000000 : ℝ)*X 1 1+(1318478449/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1342020317/2500000000 : ℝ)*X 2 0+(527391361/1000000000 : ℝ)*X 2 1+(-269464529/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4228829571/10000000000 : ℝ)*X 0 0+(1104913829/2500000000 : ℝ)*X 0 1+(2209827081/5000000000 : ℝ)*X 0 2+(4228829571/10000000000 : ℝ)*X 1 0+(1104913829/2500000000 : ℝ)*X 1 1+(2209827081/5000000000 : ℝ)*X 1 2+(4228829571/10000000000 : ℝ)*X 2 0+(1104913829/2500000000 : ℝ)*X 2 1+(2209827081/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62241/100000 : ℝ) ≤ (-6428102001257103225977924812983/10328125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (121284361/100000000000000 : ℝ)*(upper1) + (51317/20000000000000 : ℝ)*(upper2) + (45105353/25000000000000 : ℝ)*(lower4) + (15111593/50000000000000 : ℝ)*(upper5) + (248719456554403/6250000000000 : ℝ)*(major0) + (248719456554403/6250000000000 : ℝ)*(major1) + (248719456554403/6250000000000 : ℝ)*(major2) + (626160937/10000000000000 : ℝ)*(sp3) + (2670950263282341/50000000000000 : ℝ)*(sp4) + (1335465689163743/25000000000000 : ℝ)*(sp5) + (2670918343243221/50000000000000 : ℝ)*(sp6) + (1318931045631639/50000000000000 : ℝ)*(sp7) + (3776990971/10000000000000 : ℝ)*(sp13) + (63840078239/100000000000000 : ℝ)*(sp14) + (329733544109081/12500000000000 : ℝ)*(f.failure) + (2670950263282341/50000000000000 : ℝ)*(f.sum) + (3288828337609/413125000000000000000000000 : ℝ)*base65 + (649933685904450161/41312500000000000000000000000000 : ℝ)*base68 + (284103171456950161/41312500000000000000000000000000 : ℝ)*base70 + (743090267117575161/41312500000000000000000000000000 : ℝ)*base72 + (4728597792301/1652500000000000000000000000 : ℝ)*base73 + (141962988171799839/41312500000000000000000000000000 : ℝ)*base75 + (257656549063200161/41312500000000000000000000000000 : ℝ)*base78 + (280976547925450161/41312500000000000000000000000000 : ℝ)*base80 + (1603767946919/413125000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (196261/312500000000000000000 : ℝ)*base90 + (196261/312500000000000000000 : ℝ)*base92 + (196261/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (29677/50000 : ℝ) ≤ (1961738513197322668185303447/3305000000000000000000000000 : ℝ) := by norm_num
    linear_combination (96295213/50000000000000 : ℝ)*(upper0) + (61866307/100000000000000 : ℝ)*(upper3) + (4762237/4000000000000 : ℝ)*(upper4) + (4044832763477149/100000000000000 : ℝ)*(major0) + (4044832763477149/100000000000000 : ℝ)*(major1) + (4044832763477149/100000000000000 : ℝ)*(major2) + (5388710642447259/100000000000000 : ℝ)*(sp0) + (336793728444331/6250000000000 : ℝ)*(sp1) + (5388703017624533/100000000000000 : ℝ)*(sp2) + (268116056494019/10000000000000 : ℝ)*(sp3) + (12818745829/100000000000000 : ℝ)*(sp5) + (147753603/1562500000000 : ℝ)*(sp6) + (915703933/50000000000000 : ℝ)*(sp8) + (6925746493/100000000000000 : ℝ)*(sp11) + (670291872671671/25000000000000 : ℝ)*(f.failure) + (43109699790841/800000000000 : ℝ)*(f.sum) + (9972503380531/3305000000000000000000000000 : ℝ)*base65 + (1529668534245846263/661000000000000000000000000000000 : ℝ)*base68 + (1578263651981846263/661000000000000000000000000000000 : ℝ)*base70 + (2554754443698153737/661000000000000000000000000000000 : ℝ)*base71 + (63134325074289/3305000000000000000000000000 : ℝ)*base74 + (4308737744216846263/661000000000000000000000000000000 : ℝ)*base76 + (1028511284294153737/661000000000000000000000000000000 : ℝ)*base77 + (21791158559021153737/661000000000000000000000000000000 : ℝ)*base79 + (20777607044741/3305000000000000000000000000 : ℝ)*base81 + (5610949/625000000000000000000 : ℝ)*base89 + (5610949/625000000000000000000 : ℝ)*base91 + (5610949/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (80023/100000 : ℝ) ≤ (264483701826181355400705430828047/330500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4014721/50000000000000 : ℝ)*(upper0) + (388771/12500000000000 : ℝ)*(lower1) + (1268489/3125000000000 : ℝ)*(lower3) + (4738657/20000000000000 : ℝ)*(upper4) + (4512023970026327/100000000000000 : ℝ)*(major0) + (4512023970026327/100000000000000 : ℝ)*(major1) + (4512023970026327/100000000000000 : ℝ)*(major2) + (6780426411/25000000000000 : ℝ)*(sp1) + (4989064337/12500000000000 : ℝ)*(sp2) + (17737841029/100000000000000 : ℝ)*(sp3) + (3003260931774133/50000000000000 : ℝ)*(sp8) + (6006494741842621/100000000000000 : ℝ)*(sp9) + (600648195103357/10000000000000 : ℝ)*(sp10) + (186927076878599/6250000000000 : ℝ)*(sp11) + (1495425483949307/50000000000000 : ℝ)*(f.failure) + (3003260931774133/50000000000000 : ℝ)*(f.sum) + (12826765349917/3305000000000000000000000000 : ℝ)*base66 + (1512688057400690651/661000000000000000000000000000000 : ℝ)*base67 + (1162147660439690651/661000000000000000000000000000000 : ℝ)*base69 + (4505495016476309349/661000000000000000000000000000000 : ℝ)*base72 + (11867238157877/3305000000000000000000000000 : ℝ)*base74 + (617824764201690651/661000000000000000000000000000000 : ℝ)*base75 + (3723163231113690651/661000000000000000000000000000000 : ℝ)*base77 + (8157459017413309349/661000000000000000000000000000000 : ℝ)*base80 + (8165957353543/3305000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (10903233/1250000000000000000000 : ℝ)*base89 + (10903233/1250000000000000000000 : ℝ)*base91 + (10903233/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-41641/50000 : ℝ) ≤ (-13761953513263207246087650725763/16525000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6055277/3125000000000 : ℝ)*(lower0) + (52842889/50000000000000 : ℝ)*(upper1) + (307852691/100000000000000 : ℝ)*(lower2) + (189653287/100000000000000 : ℝ)*(upper3) + (25169923/6250000000000 : ℝ)*(upper5) + (227367339948117/5000000000000 : ℝ)*(major0) + (227367339948117/5000000000000 : ℝ)*(major1) + (227367339948117/5000000000000 : ℝ)*(major2) + (5702961107/100000000000000 : ℝ)*(sp4) + (48276112777/20000000000000 : ℝ)*(sp7) + (6108182618334087/100000000000000 : ℝ)*(sp12) + (3054094160647597/50000000000000 : ℝ)*(sp13) + (3054094160647597/50000000000000 : ℝ)*(sp14) + (3014023761952151/100000000000000 : ℝ)*(sp15) + (753566285629009/25000000000000 : ℝ)*(f.failure) + (3054094160647597/50000000000000 : ℝ)*(f.sum) + (1730261231161/661000000000000000000000000 : ℝ)*base66 + (1860763468124991921/33050000000000000000000000000000 : ℝ)*base67 + (513232954516941921/33050000000000000000000000000000 : ℝ)*base69 + (95953352808091921/33050000000000000000000000000000 : ℝ)*base71 + (24507116811/41312500000000000000000000 : ℝ)*base73 + (443812535336891921/33050000000000000000000000000000 : ℝ)*base75 + (34024952688708079/33050000000000000000000000000000 : ℝ)*base78 + (743176961241858079/33050000000000000000000000000000 : ℝ)*base80 + (2340956777923/661000000000000000000000000 : ℝ)*base81 + (2187971/625000000000000000000 : ℝ)*base89 + (2187971/625000000000000000000 : ℝ)*base91 + (2187971/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1213_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37715219/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1761/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2861/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62241/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29677/50000 : ℝ) else (80023/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41641/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1213_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1213_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37715219/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1761/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2861/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62241/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29677/50000 : ℝ) else (80023/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41641/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1213_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37715219/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1761/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2861/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62241/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29677/50000 : ℝ) else (80023/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41641/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1213_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

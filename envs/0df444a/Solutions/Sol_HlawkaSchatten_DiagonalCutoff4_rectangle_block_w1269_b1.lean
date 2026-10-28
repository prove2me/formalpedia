-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1269_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:20:06.480915+00:00
-- url     : https://prove2.me/submissions/eefc3924-ffd3-46d4-a4e9-728eddbe4fb6

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
theorem support_rectangle_w1269_s3_0 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-420765929/2000000000 : ℝ)*x 0 + (2718614901/5000000000 : ℝ)*x 1 + (652877697/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (420765929/2000000000 : ℝ)^8463 ≤ (255805868491/2000000000000 : ℝ)^6415 := by
    have hnat : (420765929 : ℕ)^8463*2000000000000^6415 ≤ 255805868491^6415*2000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420765929 2000000000 255805868491 2000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2718614901/5000000000 : ℝ)^8463 ≤ (4476066722083/10000000000000 : ℝ)^6415 := by
    have hnat : (2718614901 : ℕ)^8463*10000000000000^6415 ≤ 4476066722083^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718614901 5000000000 4476066722083 10000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (652877697/1250000000 : ℝ)^8463 ≤ (21224519669401/50000000000000 : ℝ)^6415 := by
    have hnat : (652877697 : ℕ)^8463*50000000000000^6415 ≤ 21224519669401^6415*1250000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652877697 1250000000 21224519669401 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-420765929/2000000000 : ℝ), (2718614901/5000000000 : ℝ), (652877697/1250000000 : ℝ)] ![(255805868491/2000000000000 : ℝ), (4476066722083/10000000000000 : ℝ), (21224519669401/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-420765929/2000000000 : ℝ)|^8463 ≤ (255805868491/2000000000000 : ℝ)^6415
        have hw : |(-420765929/2000000000 : ℝ)|=(420765929/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2718614901/5000000000 : ℝ)|^8463 ≤ (4476066722083/10000000000000 : ℝ)^6415
        have hw : |(2718614901/5000000000 : ℝ)|=(2718614901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(652877697/1250000000 : ℝ)|^8463 ≤ (21224519669401/50000000000000 : ℝ)^6415
        have hw : |(652877697/1250000000 : ℝ)|=(652877697/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s3_1 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1071070389/2000000000 : ℝ)*x 0 + (-442705961/2000000000 : ℝ)*x 1 + (652877721/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071070389/2000000000 : ℝ)^8463 ≤ (43873584309559/100000000000000 : ℝ)^6415 := by
    have hnat : (1071070389 : ℕ)^8463*100000000000000^6415 ≤ 43873584309559^6415*2000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071070389 2000000000 43873584309559 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (442705961/2000000000 : ℝ)^8463 ≤ (13677374271773/100000000000000 : ℝ)^6415 := by
    have hnat : (442705961 : ℕ)^8463*100000000000000^6415 ≤ 13677374271773^6415*2000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442705961 2000000000 13677374271773 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (652877721/1250000000 : ℝ)^8463 ≤ (42449041397417/100000000000000 : ℝ)^6415 := by
    have hnat : (652877721 : ℕ)^8463*100000000000000^6415 ≤ 42449041397417^6415*1250000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652877721 1250000000 42449041397417 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071070389/2000000000 : ℝ), (-442705961/2000000000 : ℝ), (652877721/1250000000 : ℝ)] ![(43873584309559/100000000000000 : ℝ), (13677374271773/100000000000000 : ℝ), (42449041397417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071070389/2000000000 : ℝ)|^8463 ≤ (43873584309559/100000000000000 : ℝ)^6415
        have hw : |(1071070389/2000000000 : ℝ)|=(1071070389/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-442705961/2000000000 : ℝ)|^8463 ≤ (13677374271773/100000000000000 : ℝ)^6415
        have hw : |(-442705961/2000000000 : ℝ)|=(442705961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(652877721/1250000000 : ℝ)|^8463 ≤ (42449041397417/100000000000000 : ℝ)^6415
        have hw : |(652877721/1250000000 : ℝ)|=(652877721/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s3_2 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1338837981/2500000000 : ℝ)*x 0 + (2611510829/5000000000 : ℝ)*x 1 + (-2213529979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338837981/2500000000 : ℝ)^8463 ≤ (43873584082593/100000000000000 : ℝ)^6415 := by
    have hnat : (1338837981 : ℕ)^8463*100000000000000^6415 ≤ 43873584082593^6415*2500000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338837981 2500000000 43873584082593 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2611510829/5000000000 : ℝ)^8463 ≤ (21224520109001/50000000000000 : ℝ)^6415 := by
    have hnat : (2611510829 : ℕ)^8463*50000000000000^6415 ≤ 21224520109001^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2611510829 5000000000 21224520109001 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2213529979/10000000000 : ℝ)^8463 ≤ (13677375690159/100000000000000 : ℝ)^6415 := by
    have hnat : (2213529979 : ℕ)^8463*100000000000000^6415 ≤ 13677375690159^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2213529979 10000000000 13677375690159 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338837981/2500000000 : ℝ), (2611510829/5000000000 : ℝ), (-2213529979/10000000000 : ℝ)] ![(43873584082593/100000000000000 : ℝ), (21224520109001/50000000000000 : ℝ), (13677375690159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338837981/2500000000 : ℝ)|^8463 ≤ (43873584082593/100000000000000 : ℝ)^6415
        have hw : |(1338837981/2500000000 : ℝ)|=(1338837981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2611510829/5000000000 : ℝ)|^8463 ≤ (21224520109001/50000000000000 : ℝ)^6415
        have hw : |(2611510829/5000000000 : ℝ)|=(2611510829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2213529979/10000000000 : ℝ)|^8463 ≤ (13677375690159/100000000000000 : ℝ)^6415
        have hw : |(-2213529979/10000000000 : ℝ)|=(2213529979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s3_3 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1085950939/2500000000 : ℝ)*x 0 + (12908423/31250000 : ℝ)*x 1 + (4567498257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1085950939/2500000000 : ℝ)^8463 ≤ (16642923847817/50000000000000 : ℝ)^6415 := by
    have hnat : (1085950939 : ℕ)^8463*50000000000000^6415 ≤ 16642923847817^6415*2500000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085950939 2500000000 16642923847817 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (12908423/31250000 : ℝ)^8463 ≤ (7787138483769/25000000000000 : ℝ)^6415 := by
    have hnat : (12908423 : ℕ)^8463*25000000000000^6415 ≤ 7787138483769^6415*31250000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12908423 31250000 7787138483769 25000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4567498257/10000000000 : ℝ)^8463 ≤ (17782799173989/50000000000000 : ℝ)^6415 := by
    have hnat : (4567498257 : ℕ)^8463*50000000000000^6415 ≤ 17782799173989^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4567498257 10000000000 17782799173989 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1085950939/2500000000 : ℝ), (12908423/31250000 : ℝ), (4567498257/10000000000 : ℝ)] ![(16642923847817/50000000000000 : ℝ), (7787138483769/25000000000000 : ℝ), (17782799173989/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1085950939/2500000000 : ℝ)|^8463 ≤ (16642923847817/50000000000000 : ℝ)^6415
        have hw : |(1085950939/2500000000 : ℝ)|=(1085950939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(12908423/31250000 : ℝ)|^8463 ≤ (7787138483769/25000000000000 : ℝ)^6415
        have hw : |(12908423/31250000 : ℝ)|=(12908423/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4567498257/10000000000 : ℝ)|^8463 ≤ (17782799173989/50000000000000 : ℝ)^6415
        have hw : |(4567498257/10000000000 : ℝ)|=(4567498257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s3_4 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2103853869/10000000000 : ℝ)*x 0 + (2611979139/5000000000 : ℝ)*x 1 + (5436287101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2103853869/10000000000 : ℝ)^8463 ≤ (12790487711787/100000000000000 : ℝ)^6415 := by
    have hnat : (2103853869 : ℕ)^8463*100000000000000^6415 ≤ 12790487711787^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103853869 10000000000 12790487711787 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2611979139/5000000000 : ℝ)^8463 ≤ (4245908289713/10000000000000 : ℝ)^6415 := by
    have hnat : (2611979139 : ℕ)^8463*10000000000000^6415 ≤ 4245908289713^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2611979139 5000000000 4245908289713 10000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5436287101/10000000000 : ℝ)^8463 ≤ (22375214688613/50000000000000 : ℝ)^6415 := by
    have hnat : (5436287101 : ℕ)^8463*50000000000000^6415 ≤ 22375214688613^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436287101 10000000000 22375214688613 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2103853869/10000000000 : ℝ), (2611979139/5000000000 : ℝ), (5436287101/10000000000 : ℝ)] ![(12790487711787/100000000000000 : ℝ), (4245908289713/10000000000000 : ℝ), (22375214688613/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2103853869/10000000000 : ℝ)|^8463 ≤ (12790487711787/100000000000000 : ℝ)^6415
        have hw : |(-2103853869/10000000000 : ℝ)|=(2103853869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2611979139/5000000000 : ℝ)|^8463 ≤ (4245908289713/10000000000000 : ℝ)^6415
        have hw : |(2611979139/5000000000 : ℝ)|=(2611979139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5436287101/10000000000 : ℝ)|^8463 ≤ (22375214688613/50000000000000 : ℝ)^6415
        have hw : |(5436287101/10000000000 : ℝ)|=(5436287101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s3_5 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (530064837/1000000000 : ℝ)*x 0 + (-2000264049/10000000000 : ℝ)*x 1 + (5436286947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530064837/1000000000 : ℝ)^8463 ≤ (8656663564743/20000000000000 : ℝ)^6415 := by
    have hnat : (530064837 : ℕ)^8463*20000000000000^6415 ≤ 8656663564743^6415*1000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530064837 1000000000 8656663564743 20000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2000264049/10000000000 : ℝ)^8463 ≤ (2991563613797/25000000000000 : ℝ)^6415 := by
    have hnat : (2000264049 : ℕ)^8463*25000000000000^6415 ≤ 2991563613797^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2000264049 10000000000 2991563613797 25000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5436286947/10000000000 : ℝ)^8463 ≤ (22375213852407/50000000000000 : ℝ)^6415 := by
    have hnat : (5436286947 : ℕ)^8463*50000000000000^6415 ≤ 22375213852407^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436286947 10000000000 22375213852407 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530064837/1000000000 : ℝ), (-2000264049/10000000000 : ℝ), (5436286947/10000000000 : ℝ)] ![(8656663564743/20000000000000 : ℝ), (2991563613797/25000000000000 : ℝ), (22375213852407/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530064837/1000000000 : ℝ)|^8463 ≤ (8656663564743/20000000000000 : ℝ)^6415
        have hw : |(530064837/1000000000 : ℝ)|=(530064837/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2000264049/10000000000 : ℝ)|^8463 ≤ (2991563613797/25000000000000 : ℝ)^6415
        have hw : |(-2000264049/10000000000 : ℝ)|=(2000264049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5436286947/10000000000 : ℝ)|^8463 ≤ (22375213852407/50000000000000 : ℝ)^6415
        have hw : |(5436286947/10000000000 : ℝ)|=(5436286947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s3_6 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5300648017/10000000000 : ℝ)*x 0 + (339767947/625000000 : ℝ)*x 1 + (-8001057/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5300648017/10000000000 : ℝ)^8463 ≤ (21641657010499/50000000000000 : ℝ)^6415 := by
    have hnat : (5300648017 : ℕ)^8463*50000000000000^6415 ≤ 21641657010499^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5300648017 10000000000 21641657010499 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339767947/625000000 : ℝ)^8463 ≤ (11187607482769/25000000000000 : ℝ)^6415 := by
    have hnat : (339767947 : ℕ)^8463*25000000000000^6415 ≤ 11187607482769^6415*625000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339767947 625000000 11187607482769 25000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8001057/40000000 : ℝ)^8463 ≤ (5983128020761/50000000000000 : ℝ)^6415 := by
    have hnat : (8001057 : ℕ)^8463*50000000000000^6415 ≤ 5983128020761^6415*40000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8001057 40000000 5983128020761 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5300648017/10000000000 : ℝ), (339767947/625000000 : ℝ), (-8001057/40000000 : ℝ)] ![(21641657010499/50000000000000 : ℝ), (11187607482769/25000000000000 : ℝ), (5983128020761/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5300648017/10000000000 : ℝ)|^8463 ≤ (21641657010499/50000000000000 : ℝ)^6415
        have hw : |(5300648017/10000000000 : ℝ)|=(5300648017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339767947/625000000 : ℝ)|^8463 ≤ (11187607482769/25000000000000 : ℝ)^6415
        have hw : |(339767947/625000000 : ℝ)|=(339767947/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8001057/40000000 : ℝ)|^8463 ≤ (5983128020761/50000000000000 : ℝ)^6415
        have hw : |(-8001057/40000000 : ℝ)|=(8001057/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s3_7 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4343852571/10000000000 : ℝ)*x 0 + (2282793951/5000000000 : ℝ)*x 1 + (826523627/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4343852571/10000000000 : ℝ)^8463 ≤ (33286341177477/100000000000000 : ℝ)^6415 := by
    have hnat : (4343852571 : ℕ)^8463*100000000000000^6415 ≤ 33286341177477^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4343852571 10000000000 33286341177477 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2282793951/5000000000 : ℝ)^8463 ≤ (2221623461829/6250000000000 : ℝ)^6415 := by
    have hnat : (2282793951 : ℕ)^8463*6250000000000^6415 ≤ 2221623461829^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2282793951 5000000000 2221623461829 6250000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (826523627/2000000000 : ℝ)^8463 ≤ (31167683413747/100000000000000 : ℝ)^6415 := by
    have hnat : (826523627 : ℕ)^8463*100000000000000^6415 ≤ 31167683413747^6415*2000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      826523627 2000000000 31167683413747 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4343852571/10000000000 : ℝ), (2282793951/5000000000 : ℝ), (826523627/2000000000 : ℝ)] ![(33286341177477/100000000000000 : ℝ), (2221623461829/6250000000000 : ℝ), (31167683413747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4343852571/10000000000 : ℝ)|^8463 ≤ (33286341177477/100000000000000 : ℝ)^6415
        have hw : |(4343852571/10000000000 : ℝ)|=(4343852571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2282793951/5000000000 : ℝ)|^8463 ≤ (2221623461829/6250000000000 : ℝ)^6415
        have hw : |(2282793951/5000000000 : ℝ)|=(2282793951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(826523627/2000000000 : ℝ)|^8463 ≤ (31167683413747/100000000000000 : ℝ)^6415
        have hw : |(826523627/2000000000 : ℝ)|=(826523627/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1269_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75978749/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8207/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9351/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2641/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3019/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8207/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9351/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8207/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9351/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8207/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9351/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8207/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9351/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8207/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9351/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8207/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9351/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9351/100000 : ℝ) ^ (8461/2048 : ℝ) ≤ (5600887452940949/100000000000000000000 : ℝ) := by
    have hpowers : (9351/100000 : ℝ)^8461 ≤ (5600887452940949/100000000000000000000 : ℝ)^2048 := by
      have hnat : (9351 : ℕ)^8461*100000000000000000000^2048 ≤ 5600887452940949^2048*100000^8461 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9351 100000 5600887452940949 100000000000000000000 8461 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9351/100000 : ℝ)) (X := (5600887452940949/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (8207/50000 : ℝ) ^ (8461/2048 : ℝ) ≤ (57250326913893843/100000000000000000000 : ℝ) := by
    have hpowers : (8207/50000 : ℝ)^8461 ≤ (57250326913893843/100000000000000000000 : ℝ)^2048 := by
      have hnat : (8207 : ℕ)^8461*100000000000000000000^2048 ≤ 57250326913893843^2048*50000^8461 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8207 50000 57250326913893843 100000000000000000000 8461 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8207/50000 : ℝ)) (X := (57250326913893843/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005600887452940949/50000000000000000000 : ℝ) ≤ (12500338911789/12500000000000 : ℝ) ^ (8461/2048 : ℝ) := by
    have hpowers : (50005600887452940949/50000000000000000000 : ℝ)^2048 ≤ (12500338911789/12500000000000 : ℝ)^8461 := by
      have hnat : (50005600887452940949 : ℕ)^2048*12500000000000^8461 ≤ 12500338911789^8461*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005600887452940949 50000000000000000000 12500338911789 12500000000000 2048 8461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12500338911789/12500000000000 : ℝ)) (X := (50005600887452940949/50000000000000000000 : ℝ)) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12507856401795854349/12500000000000000000 : ℝ) ≤ (10001520962518433/10000000000000000 : ℝ) ^ (8461/2048 : ℝ) := by
    have hpowers : (12507856401795854349/12500000000000000000 : ℝ)^2048 ≤ (10001520962518433/10000000000000000 : ℝ)^8461 := by
      have hnat : (12507856401795854349 : ℕ)^2048*10000000000000000^8461 ≤ 10001520962518433^8461*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507856401795854349 12500000000000000000 10001520962518433 10000000000000000 2048 8461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001520962518433/10000000000000000 : ℝ)) (X := (12507856401795854349/12500000000000000000 : ℝ)) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50057250326913893843/50000000000000000000 : ℝ) ≤ (5001385397802833/5000000000000000 : ℝ) ^ (8461/2048 : ℝ) := by
    have hpowers : (50057250326913893843/50000000000000000000 : ℝ)^2048 ≤ (5001385397802833/5000000000000000 : ℝ)^8461 := by
      have hnat : (50057250326913893843 : ℕ)^2048*5000000000000000^8461 ≤ 5001385397802833^8461*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50057250326913893843 50000000000000000000 5001385397802833 5000000000000000 2048 8461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001385397802833/5000000000000000 : ℝ)) (X := (50057250326913893843/50000000000000000000 : ℝ)) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5600887452940949/100000000000000000000 : ℝ) ≤ ((35304270304387567017/35315000000000000000 : ℝ)+2*(1249833087233/706300000000000 : ℝ)*(9351/100000 : ℝ))^(8461/2048 : ℝ) := by
    rw [show (35304270304387567017/35315000000000000000 : ℝ)+2*(1249833087233/706300000000000 : ℝ)*(9351/100000 : ℝ)=(12500338911789/12500000000000 : ℝ) by norm_num, show 1+2*(5600887452940949/100000000000000000000 : ℝ)=(50005600887452940949/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(57250326913893843/100000000000000000000 : ℝ)+(5600887452940949/100000000000000000000 : ℝ) ≤ ((35304270304387567017/35315000000000000000 : ℝ)+(1249833087233/706300000000000 : ℝ)*((8207/50000 : ℝ)+(9351/100000 : ℝ)))^(8461/2048 : ℝ) := by
    rw [show (35304270304387567017/35315000000000000000 : ℝ)+(1249833087233/706300000000000 : ℝ)*((8207/50000 : ℝ)+(9351/100000 : ℝ))=(10001520962518433/10000000000000000 : ℝ) by norm_num, show 1+(57250326913893843/100000000000000000000 : ℝ)+(5600887452940949/100000000000000000000 : ℝ)=(12507856401795854349/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(57250326913893843/100000000000000000000 : ℝ) ≤ ((35304270304387567017/35315000000000000000 : ℝ)+2*(1249833087233/706300000000000 : ℝ)*(8207/50000 : ℝ))^(8461/2048 : ℝ) := by
    rw [show (35304270304387567017/35315000000000000000 : ℝ)+2*(1249833087233/706300000000000 : ℝ)*(8207/50000 : ℝ)=(5001385397802833/5000000000000000 : ℝ) by norm_num, show 1+2*(57250326913893843/100000000000000000000 : ℝ)=(50057250326913893843/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (35304270304387567017/35315000000000000000 : ℝ)*(X 1 0+X 2 0)+(1249833087233/706300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8461/2048 : ℝ)) (lo := (9351/100000 : ℝ)) (hi := (8207/50000 : ℝ)) (c := (35304270304387567017/35315000000000000000 : ℝ)) (alpha := (1249833087233/706300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (35304270304387567017/35315000000000000000 : ℝ)*(X 0 1+X 2 1)+(1249833087233/706300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8461/2048 : ℝ)) (lo := (9351/100000 : ℝ)) (hi := (8207/50000 : ℝ)) (c := (35304270304387567017/35315000000000000000 : ℝ)) (alpha := (1249833087233/706300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (35304270304387567017/35315000000000000000 : ℝ)*(X 0 2+X 1 2)+(1249833087233/706300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8461/2048 : ℝ)) (lo := (9351/100000 : ℝ)) (hi := (8207/50000 : ℝ)) (c := (35304270304387567017/35315000000000000000 : ℝ)) (alpha := (1249833087233/706300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-420765929/2000000000 : ℝ)*X 0 0+(2718614901/5000000000 : ℝ)*X 0 1+(652877697/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1071070389/2000000000 : ℝ)*X 1 0+(-442705961/2000000000 : ℝ)*X 1 1+(652877721/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338837981/2500000000 : ℝ)*X 2 0+(2611510829/5000000000 : ℝ)*X 2 1+(-2213529979/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1085950939/2500000000 : ℝ)*X 0 0+(12908423/31250000 : ℝ)*X 0 1+(4567498257/10000000000 : ℝ)*X 0 2+(1085950939/2500000000 : ℝ)*X 1 0+(12908423/31250000 : ℝ)*X 1 1+(4567498257/10000000000 : ℝ)*X 1 2+(1085950939/2500000000 : ℝ)*X 2 0+(12908423/31250000 : ℝ)*X 2 1+(4567498257/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2103853869/10000000000 : ℝ)*X 0 0+(2611979139/5000000000 : ℝ)*X 0 1+(5436287101/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((530064837/1000000000 : ℝ)*X 1 0+(-2000264049/10000000000 : ℝ)*X 1 1+(5436286947/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5300648017/10000000000 : ℝ)*X 2 0+(339767947/625000000 : ℝ)*X 2 1+(-8001057/40000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4343852571/10000000000 : ℝ)*X 0 0+(2282793951/5000000000 : ℝ)*X 0 1+(826523627/2000000000 : ℝ)*X 0 2+(4343852571/10000000000 : ℝ)*X 1 0+(2282793951/5000000000 : ℝ)*X 1 1+(826523627/2000000000 : ℝ)*X 1 2+(4343852571/10000000000 : ℝ)*X 2 0+(2282793951/5000000000 : ℝ)*X 2 1+(826523627/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1740846278504741241298498767/220718750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (602614373/50000000000000 : ℝ)*(base19) + (117025137/12500000000000 : ℝ)*(base23) + (134270157/100000000000000 : ℝ)*(lower2) + (384113621/100000000000000 : ℝ)*(upper3) + (620897/4000000000000 : ℝ)*(upper5) + (869721327839083/25000000000000 : ℝ)*(major0) + (869721327839083/25000000000000 : ℝ)*(major1) + (869721327839083/25000000000000 : ℝ)*(major2) + (4668376682428907/100000000000000 : ℝ)*(sp0) + (2334194332600991/50000000000000 : ℝ)*(sp1) + (4668388934229631/100000000000000 : ℝ)*(sp2) + (1144684318883137/50000000000000 : ℝ)*(sp3) + (659400091/5000000000000 : ℝ)*(sp4) + (5925804997/50000000000000 : ℝ)*(sp7) + (572345122344067/25000000000000 : ℝ)*(f.failure) + (4668389870430727/100000000000000 : ℝ)*(f.sum) + (152874029384389/35315000000000000000000000000 : ℝ)*base66 + (910769192779360773/126125000000000000000000000000000 : ℝ)*base67 + (615433220614110773/126125000000000000000000000000000 : ℝ)*base69 + (678946258285110773/126125000000000000000000000000000 : ℝ)*base71 + (24864458424093/17657500000000000000000000000 : ℝ)*base73 + (271727091824610773/126125000000000000000000000000000 : ℝ)*base75 + (41492991650639227/126125000000000000000000000000000 : ℝ)*base78 + (2234628169477360773/126125000000000000000000000000000 : ℝ)*base79 + (34596081218771/35315000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (8232183/1250000000000000000000 : ℝ)*base89 + (8232183/1250000000000000000000 : ℝ)*base91 + (8232183/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5940347852387561115865153767/882875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1726726649/100000000000000 : ℝ)*(base19) + (336391921/25000000000000 : ℝ)*(base23) + (1864429/25000000000000 : ℝ)*(upper2) + (10549287/10000000000000 : ℝ)*(upper3) + (210367661/100000000000000 : ℝ)*(upper5) + (1754826164636361/50000000000000 : ℝ)*(major0) + (1754826164636361/50000000000000 : ℝ)*(major1) + (1754826164636361/50000000000000 : ℝ)*(major2) + (28603197393/100000000000000 : ℝ)*(sp1) + (20697713351/100000000000000 : ℝ)*(sp2) + (4709676824265301/100000000000000 : ℝ)*(sp4) + (4709646494341259/100000000000000 : ℝ)*(sp5) + (941930956196853/20000000000000 : ℝ)*(sp6) + (1154813804999843/50000000000000 : ℝ)*(sp7) + (1154813804999843/50000000000000 : ℝ)*(f.failure) + (4709676824265301/100000000000000 : ℝ)*(f.sum) + (240534180725071/35315000000000000000000000000 : ℝ)*base65 + (1738829745170093591/252250000000000000000000000000000 : ℝ)*base67 + (1391083555407843591/252250000000000000000000000000000 : ℝ)*base69 + (3577288418610343591/252250000000000000000000000000000 : ℝ)*base71 + (16838114971343/17657500000000000000000000000 : ℝ)*base73 + (362681823341843591/252250000000000000000000000000000 : ℝ)*base75 + (6176671036728843591/252250000000000000000000000000000 : ℝ)*base77 + (2582528413160093591/252250000000000000000000000000000 : ℝ)*base79 + (136624248592039/35315000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (33663593/2500000000000000000000 : ℝ)*base90 + (33663593/2500000000000000000000 : ℝ)*base92 + (33663593/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1269_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75978749/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8207/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9351/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2641/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3019/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1269_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1269_s4_0 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1052989277/5000000000 : ℝ)*x 0 + (5420552543/10000000000 : ℝ)*x 1 + (5238291089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1052989277/5000000000 : ℝ)^8463 ≤ (12807531406841/100000000000000 : ℝ)^6415 := by
    have hnat : (1052989277 : ℕ)^8463*100000000000000^6415 ≤ 12807531406841^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052989277 5000000000 12807531406841 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5420552543/10000000000 : ℝ)^8463 ≤ (11144908489243/25000000000000 : ℝ)^6415 := by
    have hnat : (5420552543 : ℕ)^8463*25000000000000^6415 ≤ 11144908489243^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420552543 10000000000 11144908489243 25000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5238291089/10000000000 : ℝ)^8463 ≤ (10653208656489/25000000000000 : ℝ)^6415 := by
    have hnat : (5238291089 : ℕ)^8463*25000000000000^6415 ≤ 10653208656489^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238291089 10000000000 10653208656489 25000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1052989277/5000000000 : ℝ), (5420552543/10000000000 : ℝ), (5238291089/10000000000 : ℝ)] ![(12807531406841/100000000000000 : ℝ), (11144908489243/25000000000000 : ℝ), (10653208656489/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1052989277/5000000000 : ℝ)|^8463 ≤ (12807531406841/100000000000000 : ℝ)^6415
        have hw : |(-1052989277/5000000000 : ℝ)|=(1052989277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5420552543/10000000000 : ℝ)|^8463 ≤ (11144908489243/25000000000000 : ℝ)^6415
        have hw : |(5420552543/10000000000 : ℝ)|=(5420552543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5238291089/10000000000 : ℝ)|^8463 ≤ (10653208656489/25000000000000 : ℝ)^6415
        have hw : |(5238291089/10000000000 : ℝ)|=(5238291089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s4_1 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5351152009/10000000000 : ℝ)*x 0 + (-2198989547/10000000000 : ℝ)*x 1 + (2619145369/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351152009/10000000000 : ℝ)^8463 ≤ (10957049338023/25000000000000 : ℝ)^6415 := by
    have hnat : (5351152009 : ℕ)^8463*25000000000000^6415 ≤ 10957049338023^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351152009 10000000000 10957049338023 25000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2198989547/10000000000 : ℝ)^8463 ≤ (13558971778069/100000000000000 : ℝ)^6415 := by
    have hnat : (2198989547 : ℕ)^8463*100000000000000^6415 ≤ 13558971778069^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2198989547 10000000000 13558971778069 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2619145369/5000000000 : ℝ)^8463 ≤ (42612830859043/100000000000000 : ℝ)^6415 := by
    have hnat : (2619145369 : ℕ)^8463*100000000000000^6415 ≤ 42612830859043^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619145369 5000000000 42612830859043 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351152009/10000000000 : ℝ), (-2198989547/10000000000 : ℝ), (2619145369/5000000000 : ℝ)] ![(10957049338023/25000000000000 : ℝ), (13558971778069/100000000000000 : ℝ), (42612830859043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351152009/10000000000 : ℝ)|^8463 ≤ (10957049338023/25000000000000 : ℝ)^6415
        have hw : |(5351152009/10000000000 : ℝ)|=(5351152009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2198989547/10000000000 : ℝ)|^8463 ≤ (13558971778069/100000000000000 : ℝ)^6415
        have hw : |(-2198989547/10000000000 : ℝ)|=(2198989547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2619145369/5000000000 : ℝ)|^8463 ≤ (42612830859043/100000000000000 : ℝ)^6415
        have hw : |(2619145369/5000000000 : ℝ)|=(2619145369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s4_2 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5351152037/10000000000 : ℝ)*x 0 + (5238290653/10000000000 : ℝ)*x 1 + (-2198989621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351152037/10000000000 : ℝ)^8463 ≤ (21914098827319/50000000000000 : ℝ)^6415 := by
    have hnat : (5351152037 : ℕ)^8463*50000000000000^6415 ≤ 21914098827319^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351152037 10000000000 21914098827319 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5238290653/10000000000 : ℝ)^8463 ≤ (10653207486707/25000000000000 : ℝ)^6415 := by
    have hnat : (5238290653 : ℕ)^8463*25000000000000^6415 ≤ 10653207486707^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238290653 10000000000 10653207486707 25000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2198989621/10000000000 : ℝ)^8463 ≤ (13558972380023/100000000000000 : ℝ)^6415 := by
    have hnat : (2198989621 : ℕ)^8463*100000000000000^6415 ≤ 13558972380023^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2198989621 10000000000 13558972380023 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351152037/10000000000 : ℝ), (5238290653/10000000000 : ℝ), (-2198989621/10000000000 : ℝ)] ![(21914098827319/50000000000000 : ℝ), (10653207486707/25000000000000 : ℝ), (13558972380023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351152037/10000000000 : ℝ)|^8463 ≤ (21914098827319/50000000000000 : ℝ)^6415
        have hw : |(5351152037/10000000000 : ℝ)|=(5351152037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5238290653/10000000000 : ℝ)|^8463 ≤ (10653207486707/25000000000000 : ℝ)^6415
        have hw : |(5238290653/10000000000 : ℝ)|=(5238290653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2198989621/10000000000 : ℝ)|^8463 ≤ (13558972380023/100000000000000 : ℝ)^6415
        have hw : |(-2198989621/10000000000 : ℝ)|=(2198989621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s4_3 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2172549509/5000000000 : ℝ)*x 0 + (1040775839/2500000000 : ℝ)*x 1 + (4534762289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2172549509/5000000000 : ℝ)^8463 ≤ (33298942391003/100000000000000 : ℝ)^6415 := by
    have hnat : (2172549509 : ℕ)^8463*100000000000000^6415 ≤ 33298942391003^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172549509 5000000000 33298942391003 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1040775839/2500000000 : ℝ)^8463 ≤ (6294271329019/20000000000000 : ℝ)^6415 := by
    have hnat : (1040775839 : ℕ)^8463*20000000000000^6415 ≤ 6294271329019^6415*2500000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040775839 2500000000 6294271329019 20000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4534762289/10000000000 : ℝ)^8463 ≤ (35229700949191/100000000000000 : ℝ)^6415 := by
    have hnat : (4534762289 : ℕ)^8463*100000000000000^6415 ≤ 35229700949191^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4534762289 10000000000 35229700949191 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2172549509/5000000000 : ℝ), (1040775839/2500000000 : ℝ), (4534762289/10000000000 : ℝ)] ![(33298942391003/100000000000000 : ℝ), (6294271329019/20000000000000 : ℝ), (35229700949191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2172549509/5000000000 : ℝ)|^8463 ≤ (33298942391003/100000000000000 : ℝ)^6415
        have hw : |(2172549509/5000000000 : ℝ)|=(2172549509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1040775839/2500000000 : ℝ)|^8463 ≤ (6294271329019/20000000000000 : ℝ)^6415
        have hw : |(1040775839/2500000000 : ℝ)|=(1040775839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4534762289/10000000000 : ℝ)|^8463 ≤ (35229700949191/100000000000000 : ℝ)^6415
        have hw : |(4534762289/10000000000 : ℝ)|=(4534762289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s4_4 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2105993509/10000000000 : ℝ)*x 0 + (5238969769/10000000000 : ℝ)*x 1 + (5419870147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2105993509/10000000000 : ℝ)^8463 ≤ (6403825695799/50000000000000 : ℝ)^6415 := by
    have hnat : (2105993509 : ℕ)^8463*50000000000000^6415 ≤ 6403825695799^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105993509 10000000000 6403825695799 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5238969769/10000000000 : ℝ)^8463 ≤ (42620118333659/100000000000000 : ℝ)^6415 := by
    have hnat : (5238969769 : ℕ)^8463*100000000000000^6415 ≤ 42620118333659^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238969769 10000000000 42620118333659 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5419870147/10000000000 : ℝ)^8463 ≤ (44572230264611/100000000000000 : ℝ)^6415 := by
    have hnat : (5419870147 : ℕ)^8463*100000000000000^6415 ≤ 44572230264611^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419870147 10000000000 44572230264611 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2105993509/10000000000 : ℝ), (5238969769/10000000000 : ℝ), (5419870147/10000000000 : ℝ)] ![(6403825695799/50000000000000 : ℝ), (42620118333659/100000000000000 : ℝ), (44572230264611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2105993509/10000000000 : ℝ)|^8463 ≤ (6403825695799/50000000000000 : ℝ)^6415
        have hw : |(-2105993509/10000000000 : ℝ)|=(2105993509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5238969769/10000000000 : ℝ)|^8463 ≤ (42620118333659/100000000000000 : ℝ)^6415
        have hw : |(5238969769/10000000000 : ℝ)|=(5238969769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5419870147/10000000000 : ℝ)|^8463 ≤ (44572230264611/100000000000000 : ℝ)^6415
        have hw : |(5419870147/10000000000 : ℝ)|=(5419870147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s4_5 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1326152681/2500000000 : ℝ)*x 0 + (-2017410297/10000000000 : ℝ)*x 1 + (5419870243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326152681/2500000000 : ℝ)^8463 ≤ (21663003821261/50000000000000 : ℝ)^6415 := by
    have hnat : (1326152681 : ℕ)^8463*50000000000000^6415 ≤ 21663003821261^6415*2500000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326152681 2500000000 21663003821261 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2017410297/10000000000 : ℝ)^8463 ≤ (605088051679/5000000000000 : ℝ)^6415 := by
    have hnat : (2017410297 : ℕ)^8463*5000000000000^6415 ≤ 605088051679^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2017410297 10000000000 605088051679 5000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5419870243/10000000000 : ℝ)^8463 ≤ (44572231306147/100000000000000 : ℝ)^6415 := by
    have hnat : (5419870243 : ℕ)^8463*100000000000000^6415 ≤ 44572231306147^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419870243 10000000000 44572231306147 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326152681/2500000000 : ℝ), (-2017410297/10000000000 : ℝ), (5419870243/10000000000 : ℝ)] ![(21663003821261/50000000000000 : ℝ), (605088051679/5000000000000 : ℝ), (44572231306147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326152681/2500000000 : ℝ)|^8463 ≤ (21663003821261/50000000000000 : ℝ)^6415
        have hw : |(1326152681/2500000000 : ℝ)|=(1326152681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2017410297/10000000000 : ℝ)|^8463 ≤ (605088051679/5000000000000 : ℝ)^6415
        have hw : |(-2017410297/10000000000 : ℝ)|=(2017410297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5419870243/10000000000 : ℝ)|^8463 ≤ (44572231306147/100000000000000 : ℝ)^6415
        have hw : |(5419870243/10000000000 : ℝ)|=(5419870243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s4_6 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5304610561/10000000000 : ℝ)*x 0 + (541987007/1000000000 : ℝ)*x 1 + (-2017410757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304610561/10000000000 : ℝ)^8463 ≤ (1733040235447/4000000000000 : ℝ)^6415 := by
    have hnat : (5304610561 : ℕ)^8463*4000000000000^6415 ≤ 1733040235447^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304610561 10000000000 1733040235447 4000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541987007/1000000000 : ℝ)^8463 ≤ (11143057357303/25000000000000 : ℝ)^6415 := by
    have hnat : (541987007 : ℕ)^8463*25000000000000^6415 ≤ 11143057357303^6415*1000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541987007 1000000000 11143057357303 25000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2017410757/10000000000 : ℝ)^8463 ≤ (6050882336951/50000000000000 : ℝ)^6415 := by
    have hnat : (2017410757 : ℕ)^8463*50000000000000^6415 ≤ 6050882336951^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2017410757 10000000000 6050882336951 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304610561/10000000000 : ℝ), (541987007/1000000000 : ℝ), (-2017410757/10000000000 : ℝ)] ![(1733040235447/4000000000000 : ℝ), (11143057357303/25000000000000 : ℝ), (6050882336951/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304610561/10000000000 : ℝ)|^8463 ≤ (1733040235447/4000000000000 : ℝ)^6415
        have hw : |(5304610561/10000000000 : ℝ)|=(5304610561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541987007/1000000000 : ℝ)|^8463 ≤ (11143057357303/25000000000000 : ℝ)^6415
        have hw : |(541987007/1000000000 : ℝ)|=(541987007/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2017410757/10000000000 : ℝ)|^8463 ≤ (6050882336951/50000000000000 : ℝ)^6415
        have hw : |(-2017410757/10000000000 : ℝ)|=(2017410757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s4_7 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1086282373/2500000000 : ℝ)*x 0 + (906675509/2000000000 : ℝ)*x 1 + (4164495387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086282373/2500000000 : ℝ)^8463 ≤ (16649625244329/50000000000000 : ℝ)^6415 := by
    have hnat : (1086282373 : ℕ)^8463*50000000000000^6415 ≤ 16649625244329^6415*2500000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086282373 2500000000 16649625244329 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (906675509/2000000000 : ℝ)^8463 ≤ (17607754689797/50000000000000 : ℝ)^6415 := by
    have hnat : (906675509 : ℕ)^8463*50000000000000^6415 ≤ 17607754689797^6415*2000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      906675509 2000000000 17607754689797 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4164495387/10000000000 : ℝ)^8463 ≤ (15742620057713/50000000000000 : ℝ)^6415 := by
    have hnat : (4164495387 : ℕ)^8463*50000000000000^6415 ≤ 15742620057713^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4164495387 10000000000 15742620057713 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1086282373/2500000000 : ℝ), (906675509/2000000000 : ℝ), (4164495387/10000000000 : ℝ)] ![(16649625244329/50000000000000 : ℝ), (17607754689797/50000000000000 : ℝ), (15742620057713/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1086282373/2500000000 : ℝ)|^8463 ≤ (16649625244329/50000000000000 : ℝ)^6415
        have hw : |(1086282373/2500000000 : ℝ)|=(1086282373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(906675509/2000000000 : ℝ)|^8463 ≤ (17607754689797/50000000000000 : ℝ)^6415
        have hw : |(906675509/2000000000 : ℝ)|=(906675509/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4164495387/10000000000 : ℝ)|^8463 ≤ (15742620057713/50000000000000 : ℝ)^6415
        have hw : |(4164495387/10000000000 : ℝ)|=(4164495387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1269_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75978749/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3019/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2641/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1089/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14747/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3019/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2641/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3019/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2641/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3019/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2641/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3019/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2641/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3019/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2641/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3019/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2641/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2641/25000 : ℝ) ^ (8461/2048 : ℝ) ≤ (9270341168314033/100000000000000000000 : ℝ) := by
    have hpowers : (2641/25000 : ℝ)^8461 ≤ (9270341168314033/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2641 : ℕ)^8461*100000000000000000000^2048 ≤ 9270341168314033^2048*25000^8461 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2641 25000 9270341168314033 100000000000000000000 8461 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2641/25000 : ℝ)) (X := (9270341168314033/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3019/20000 : ℝ) ^ (8461/2048 : ℝ) ≤ (40501781278175009/100000000000000000000 : ℝ) := by
    have hpowers : (3019/20000 : ℝ)^8461 ≤ (40501781278175009/100000000000000000000 : ℝ)^2048 := by
      have hnat : (3019 : ℕ)^8461*100000000000000000000^2048 ≤ 40501781278175009^2048*20000^8461 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3019 20000 40501781278175009 100000000000000000000 8461 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3019/20000 : ℝ)) (X := (40501781278175009/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009270341168314033/50000000000000000000 : ℝ) ≤ (2500112187240527/2500000000000000 : ℝ) ^ (8461/2048 : ℝ) := by
    have hpowers : (50009270341168314033/50000000000000000000 : ℝ)^2048 ≤ (2500112187240527/2500000000000000 : ℝ)^8461 := by
      have hnat : (50009270341168314033 : ℕ)^2048*2500000000000000^8461 ≤ 2500112187240527^8461*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009270341168314033 50000000000000000000 2500112187240527 2500000000000000 2048 8461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500112187240527/2500000000000000 : ℝ)) (X := (50009270341168314033/50000000000000000000 : ℝ)) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024886061223244521/50000000000000000000 : ℝ) ≤ (5000602257920831/5000000000000000 : ℝ) ^ (8461/2048 : ℝ) := by
    have hpowers : (50024886061223244521/50000000000000000000 : ℝ)^2048 ≤ (5000602257920831/5000000000000000 : ℝ)^8461 := by
      have hnat : (50024886061223244521 : ℕ)^2048*5000000000000000^8461 ≤ 5000602257920831^8461*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024886061223244521 50000000000000000000 5000602257920831 5000000000000000 2048 8461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000602257920831/5000000000000000 : ℝ)) (X := (50024886061223244521/50000000000000000000 : ℝ)) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50040501781278175009/50000000000000000000 : ℝ) ≤ (156280629417519/156250000000000 : ℝ) ^ (8461/2048 : ℝ) := by
    have hpowers : (50040501781278175009/50000000000000000000 : ℝ)^2048 ≤ (156280629417519/156250000000000 : ℝ)^8461 := by
      have hnat : (50040501781278175009 : ℕ)^2048*156250000000000^8461 ≤ 156280629417519^8461*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50040501781278175009 50000000000000000000 156280629417519 156250000000000 2048 8461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156280629417519/156250000000000 : ℝ)) (X := (50040501781278175009/50000000000000000000 : ℝ)) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9270341168314033/100000000000000000000 : ℝ) ≤ ((11324016359729023609/11327500000000000000 : ℝ)+2*(377883439777/226550000000000 : ℝ)*(2641/25000 : ℝ))^(8461/2048 : ℝ) := by
    rw [show (11324016359729023609/11327500000000000000 : ℝ)+2*(377883439777/226550000000000 : ℝ)*(2641/25000 : ℝ)=(2500112187240527/2500000000000000 : ℝ) by norm_num, show 1+2*(9270341168314033/100000000000000000000 : ℝ)=(50009270341168314033/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(40501781278175009/100000000000000000000 : ℝ)+(9270341168314033/100000000000000000000 : ℝ) ≤ ((11324016359729023609/11327500000000000000 : ℝ)+(377883439777/226550000000000 : ℝ)*((3019/20000 : ℝ)+(2641/25000 : ℝ)))^(8461/2048 : ℝ) := by
    rw [show (11324016359729023609/11327500000000000000 : ℝ)+(377883439777/226550000000000 : ℝ)*((3019/20000 : ℝ)+(2641/25000 : ℝ))=(5000602257920831/5000000000000000 : ℝ) by norm_num, show 1+(40501781278175009/100000000000000000000 : ℝ)+(9270341168314033/100000000000000000000 : ℝ)=(50024886061223244521/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(40501781278175009/100000000000000000000 : ℝ) ≤ ((11324016359729023609/11327500000000000000 : ℝ)+2*(377883439777/226550000000000 : ℝ)*(3019/20000 : ℝ))^(8461/2048 : ℝ) := by
    rw [show (11324016359729023609/11327500000000000000 : ℝ)+2*(377883439777/226550000000000 : ℝ)*(3019/20000 : ℝ)=(156280629417519/156250000000000 : ℝ) by norm_num, show 1+2*(40501781278175009/100000000000000000000 : ℝ)=(50040501781278175009/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11324016359729023609/11327500000000000000 : ℝ)*(X 1 0+X 2 0)+(377883439777/226550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8461/2048 : ℝ)) (lo := (2641/25000 : ℝ)) (hi := (3019/20000 : ℝ)) (c := (11324016359729023609/11327500000000000000 : ℝ)) (alpha := (377883439777/226550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11324016359729023609/11327500000000000000 : ℝ)*(X 0 1+X 2 1)+(377883439777/226550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8461/2048 : ℝ)) (lo := (2641/25000 : ℝ)) (hi := (3019/20000 : ℝ)) (c := (11324016359729023609/11327500000000000000 : ℝ)) (alpha := (377883439777/226550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11324016359729023609/11327500000000000000 : ℝ)*(X 0 2+X 1 2)+(377883439777/226550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8461/2048 : ℝ)) (lo := (2641/25000 : ℝ)) (hi := (3019/20000 : ℝ)) (c := (11324016359729023609/11327500000000000000 : ℝ)) (alpha := (377883439777/226550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1052989277/5000000000 : ℝ)*X 0 0+(5420552543/10000000000 : ℝ)*X 0 1+(5238291089/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351152009/10000000000 : ℝ)*X 1 0+(-2198989547/10000000000 : ℝ)*X 1 1+(2619145369/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351152037/10000000000 : ℝ)*X 2 0+(5238290653/10000000000 : ℝ)*X 2 1+(-2198989621/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2172549509/5000000000 : ℝ)*X 0 0+(1040775839/2500000000 : ℝ)*X 0 1+(4534762289/10000000000 : ℝ)*X 0 2+(2172549509/5000000000 : ℝ)*X 1 0+(1040775839/2500000000 : ℝ)*X 1 1+(4534762289/10000000000 : ℝ)*X 1 2+(2172549509/5000000000 : ℝ)*X 2 0+(1040775839/2500000000 : ℝ)*X 2 1+(4534762289/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2105993509/10000000000 : ℝ)*X 0 0+(5238969769/10000000000 : ℝ)*X 0 1+(5419870147/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326152681/2500000000 : ℝ)*X 1 0+(-2017410297/10000000000 : ℝ)*X 1 1+(5419870243/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5304610561/10000000000 : ℝ)*X 2 0+(541987007/1000000000 : ℝ)*X 2 1+(-2017410757/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1086282373/2500000000 : ℝ)*X 0 0+(906675509/2000000000 : ℝ)*X 0 1+(4164495387/10000000000 : ℝ)*X 0 2+(1086282373/2500000000 : ℝ)*X 1 0+(906675509/2000000000 : ℝ)*X 1 1+(4164495387/10000000000 : ℝ)*X 1 2+(1086282373/2500000000 : ℝ)*X 2 0+(906675509/2000000000 : ℝ)*X 2 1+(4164495387/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (648052717975544629496174673/70796875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (117099627/6250000000000 : ℝ)*(base19) + (1693954719/100000000000000 : ℝ)*(base23) + (13936303/12500000000000 : ℝ)*(lower2) + (29849119/12500000000000 : ℝ)*(upper3) + (2644493/100000000000000 : ℝ)*(upper5) + (63885550652453/1562500000000 : ℝ)*(major0) + (63885550652453/1562500000000 : ℝ)*(major1) + (63885550652453/1562500000000 : ℝ)*(major2) + (5486654519174773/100000000000000 : ℝ)*(sp0) + (5486678021612207/100000000000000 : ℝ)*(sp1) + (5486678201251519/100000000000000 : ℝ)*(sp2) + (1345326224498599/50000000000000 : ℝ)*(sp3) + (12688015733/50000000000000 : ℝ)*(sp4) + (17834187507/100000000000000 : ℝ)*(sp7) + (538134056636941/20000000000000 : ℝ)*(f.failure) + (5486679895206239/100000000000000 : ℝ)*(f.sum) + (6529043114477/5663750000000000000000000000 : ℝ)*base65 + (293479684841343373/17699218750000000000000000000000 : ℝ)*base68 + (93114487900296121/35398437500000000000000000000000 : ℝ)*base70 + (264637939185798383/70796875000000000000000000000000 : ℝ)*base71 + (4511589403799/11327500000000000000000000000 : ℝ)*base73 + (385189112690857867/70796875000000000000000000000000 : ℝ)*base76 + (793012175822639117/70796875000000000000000000000000 : ℝ)*base78 + (146977574456110129/35398437500000000000000000000000 : ℝ)*base79 + (27408590247777/5663750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (4366809/1000000000000000000000 : ℝ)*base89 + (4366809/1000000000000000000000 : ℝ)*base91 + (4366809/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4709786564709639043867825899/566375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (64520141/6250000000000 : ℝ)*(base19) + (28177707/3125000000000 : ℝ)*(base23) + (9675981/20000000000000 : ℝ)*(upper3) + (1001213/1000000000000 : ℝ)*(lower4) + (125597309/50000000000000 : ℝ)*(upper5) + (4119397761018937/100000000000000 : ℝ)*(major0) + (4119397761018937/100000000000000 : ℝ)*(major1) + (4119397761018937/100000000000000 : ℝ)*(major2) + (13148647851/50000000000000 : ℝ)*(sp1) + (2313927847/25000000000000 : ℝ)*(sp2) + (5527907124659599/100000000000000 : ℝ)*(sp4) + (138196994876041/2500000000000 : ℝ)*(sp5) + (1381974241815397/25000000000000 : ℝ)*(sp6) + (2710888120189329/100000000000000 : ℝ)*(sp7) + (2710888120189329/100000000000000 : ℝ)*(f.failure) + (5527907124659599/100000000000000 : ℝ)*(f.sum) + (60408790195163/22655000000000000000000000000 : ℝ)*base65 + (167769641682466367/1132750000000000000000000000000000 : ℝ)*base68 + (15546931119092466367/1132750000000000000000000000000000 : ℝ)*base70 + (6130180339090033633/1132750000000000000000000000000000 : ℝ)*base71 + (15675201184207/22655000000000000000000000000 : ℝ)*base74 + (12025749469574283633/1132750000000000000000000000000000 : ℝ)*base75 + (824695720641466367/1132750000000000000000000000000000 : ℝ)*base78 + (8902704949228216367/1132750000000000000000000000000000 : ℝ)*base80 + (71136816698547/22655000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (10569421/5000000000000000000000 : ℝ)*base89 + (10569421/5000000000000000000000 : ℝ)*base91 + (10569421/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1269_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75978749/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3019/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2641/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1089/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14747/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1269_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1269_s5_0 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-526598419/2500000000 : ℝ)*x 0 + (2708533941/5000000000 : ℝ)*x 1 + (5241502983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (526598419/2500000000 : ℝ)^8463 ≤ (12810862053637/100000000000000 : ℝ)^6415 := by
    have hnat : (526598419 : ℕ)^8463*100000000000000^6415 ≤ 12810862053637^6415*2500000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526598419 2500000000 12810862053637 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2708533941/5000000000 : ℝ)^8463 ≤ (44541830059231/100000000000000 : ℝ)^6415 := by
    have hnat : (2708533941 : ℕ)^8463*100000000000000^6415 ≤ 44541830059231^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708533941 5000000000 44541830059231 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5241502983/10000000000 : ℝ)^8463 ≤ (21323653936019/50000000000000 : ℝ)^6415 := by
    have hnat : (5241502983 : ℕ)^8463*50000000000000^6415 ≤ 21323653936019^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241502983 10000000000 21323653936019 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-526598419/2500000000 : ℝ), (2708533941/5000000000 : ℝ), (5241502983/10000000000 : ℝ)] ![(12810862053637/100000000000000 : ℝ), (44541830059231/100000000000000 : ℝ), (21323653936019/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-526598419/2500000000 : ℝ)|^8463 ≤ (12810862053637/100000000000000 : ℝ)^6415
        have hw : |(-526598419/2500000000 : ℝ)|=(526598419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2708533941/5000000000 : ℝ)|^8463 ≤ (44541830059231/100000000000000 : ℝ)^6415
        have hw : |(2708533941/5000000000 : ℝ)|=(2708533941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5241502983/10000000000 : ℝ)|^8463 ≤ (21323653936019/50000000000000 : ℝ)^6415
        have hw : |(5241502983/10000000000 : ℝ)|=(5241502983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s5_1 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5350271053/10000000000 : ℝ)*x 0 + (-2195920641/10000000000 : ℝ)*x 1 + (1310375749/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350271053/10000000000 : ℝ)^8463 ≤ (2190933933519/5000000000000 : ℝ)^6415 := by
    have hnat : (5350271053 : ℕ)^8463*5000000000000^6415 ≤ 2190933933519^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350271053 10000000000 2190933933519 5000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2195920641/10000000000 : ℝ)^8463 ≤ (676700665091/5000000000000 : ℝ)^6415 := by
    have hnat : (2195920641 : ℕ)^8463*5000000000000^6415 ≤ 676700665091^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2195920641 10000000000 676700665091 5000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310375749/2500000000 : ℝ)^8463 ≤ (42647308011581/100000000000000 : ℝ)^6415 := by
    have hnat : (1310375749 : ℕ)^8463*100000000000000^6415 ≤ 42647308011581^6415*2500000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310375749 2500000000 42647308011581 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350271053/10000000000 : ℝ), (-2195920641/10000000000 : ℝ), (1310375749/2500000000 : ℝ)] ![(2190933933519/5000000000000 : ℝ), (676700665091/5000000000000 : ℝ), (42647308011581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350271053/10000000000 : ℝ)|^8463 ≤ (2190933933519/5000000000000 : ℝ)^6415
        have hw : |(5350271053/10000000000 : ℝ)|=(5350271053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2195920641/10000000000 : ℝ)|^8463 ≤ (676700665091/5000000000000 : ℝ)^6415
        have hw : |(-2195920641/10000000000 : ℝ)|=(2195920641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310375749/2500000000 : ℝ)|^8463 ≤ (42647308011581/100000000000000 : ℝ)^6415
        have hw : |(1310375749/2500000000 : ℝ)|=(1310375749/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s5_2 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1070054219/2000000000 : ℝ)*x 0 + (1310375749/2500000000 : ℝ)*x 1 + (-274490073/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070054219/2000000000 : ℝ)^8463 ≤ (2738667445261/6250000000000 : ℝ)^6415 := by
    have hnat : (1070054219 : ℕ)^8463*6250000000000^6415 ≤ 2738667445261^6415*2000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070054219 2000000000 2738667445261 6250000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310375749/2500000000 : ℝ)^8463 ≤ (42647308011581/100000000000000 : ℝ)^6415 := by
    have hnat : (1310375749 : ℕ)^8463*100000000000000^6415 ≤ 42647308011581^6415*2500000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310375749 2500000000 42647308011581 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (274490073/1250000000 : ℝ)^8463 ≤ (338350320959/2500000000000 : ℝ)^6415 := by
    have hnat : (274490073 : ℕ)^8463*2500000000000^6415 ≤ 338350320959^6415*1250000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274490073 1250000000 338350320959 2500000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070054219/2000000000 : ℝ), (1310375749/2500000000 : ℝ), (-274490073/1250000000 : ℝ)] ![(2738667445261/6250000000000 : ℝ), (42647308011581/100000000000000 : ℝ), (338350320959/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070054219/2000000000 : ℝ)|^8463 ≤ (2738667445261/6250000000000 : ℝ)^6415
        have hw : |(1070054219/2000000000 : ℝ)|=(1070054219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310375749/2500000000 : ℝ)|^8463 ≤ (42647308011581/100000000000000 : ℝ)^6415
        have hw : |(1310375749/2500000000 : ℝ)|=(1310375749/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-274490073/1250000000 : ℝ)|^8463 ≤ (338350320959/2500000000000 : ℝ)^6415
        have hw : |(-274490073/1250000000 : ℝ)|=(274490073/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s5_3 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (434534459/1000000000 : ℝ)*x 0 + (833979959/2000000000 : ℝ)*x 1 + (905580651/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (434534459/1000000000 : ℝ)^8463 ≤ (33301425187979/100000000000000 : ℝ)^6415 := by
    have hnat : (434534459 : ℕ)^8463*100000000000000^6415 ≤ 33301425187979^6415*1000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434534459 1000000000 33301425187979 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (833979959/2000000000 : ℝ)^8463 ≤ (31539155208821/100000000000000 : ℝ)^6415 := by
    have hnat : (833979959 : ℕ)^8463*100000000000000^6415 ≤ 31539155208821^6415*2000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833979959 2000000000 31539155208821 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (905580651/2000000000 : ℝ)^8463 ≤ (7031883917713/20000000000000 : ℝ)^6415 := by
    have hnat : (905580651 : ℕ)^8463*20000000000000^6415 ≤ 7031883917713^6415*2000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      905580651 2000000000 7031883917713 20000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(434534459/1000000000 : ℝ), (833979959/2000000000 : ℝ), (905580651/2000000000 : ℝ)] ![(33301425187979/100000000000000 : ℝ), (31539155208821/100000000000000 : ℝ), (7031883917713/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(434534459/1000000000 : ℝ)|^8463 ≤ (33301425187979/100000000000000 : ℝ)^6415
        have hw : |(434534459/1000000000 : ℝ)|=(434534459/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(833979959/2000000000 : ℝ)|^8463 ≤ (31539155208821/100000000000000 : ℝ)^6415
        have hw : |(833979959/2000000000 : ℝ)|=(833979959/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(905580651/2000000000 : ℝ)|^8463 ≤ (7031883917713/20000000000000 : ℝ)^6415
        have hw : |(905580651/2000000000 : ℝ)|=(905580651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s5_4 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-263300861/1250000000 : ℝ)*x 0 + (2621066613/5000000000 : ℝ)*x 1 + (5416434437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263300861/1250000000 : ℝ)^8463 ≤ (12810968060869/100000000000000 : ℝ)^6415 := by
    have hnat : (263300861 : ℕ)^8463*100000000000000^6415 ≤ 12810968060869^6415*1250000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263300861 1250000000 12810968060869 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621066613/5000000000 : ℝ)^8463 ≤ (21327036529711/50000000000000 : ℝ)^6415 := by
    have hnat : (2621066613 : ℕ)^8463*50000000000000^6415 ≤ 21327036529711^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621066613 5000000000 21327036529711 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416434437/10000000000 : ℝ)^8463 ≤ (71255934183/160000000000 : ℝ)^6415 := by
    have hnat : (5416434437 : ℕ)^8463*160000000000^6415 ≤ 71255934183^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416434437 10000000000 71255934183 160000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-263300861/1250000000 : ℝ), (2621066613/5000000000 : ℝ), (5416434437/10000000000 : ℝ)] ![(12810968060869/100000000000000 : ℝ), (21327036529711/50000000000000 : ℝ), (71255934183/160000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-263300861/1250000000 : ℝ)|^8463 ≤ (12810968060869/100000000000000 : ℝ)^6415
        have hw : |(-263300861/1250000000 : ℝ)|=(263300861/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621066613/5000000000 : ℝ)|^8463 ≤ (21327036529711/50000000000000 : ℝ)^6415
        have hw : |(2621066613/5000000000 : ℝ)|=(2621066613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416434437/10000000000 : ℝ)|^8463 ≤ (71255934183/160000000000 : ℝ)^6415
        have hw : |(5416434437/10000000000 : ℝ)|=(5416434437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s5_5 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1061088109/2000000000 : ℝ)*x 0 + (-1010494531/5000000000 : ℝ)*x 1 + (8463179/15625000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061088109/2000000000 : ℝ)^8463 ≤ (2166747465071/5000000000000 : ℝ)^6415 := by
    have hnat : (1061088109 : ℕ)^8463*5000000000000^6415 ≤ 2166747465071^6415*2000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061088109 2000000000 2166747465071 5000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1010494531/5000000000 : ℝ)^8463 ≤ (2426018096313/20000000000000 : ℝ)^6415 := by
    have hnat : (1010494531 : ℕ)^8463*20000000000000^6415 ≤ 2426018096313^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010494531 5000000000 2426018096313 20000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8463179/15625000 : ℝ)^8463 ≤ (44534960198573/100000000000000 : ℝ)^6415 := by
    have hnat : (8463179 : ℕ)^8463*100000000000000^6415 ≤ 44534960198573^6415*15625000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8463179 15625000 44534960198573 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061088109/2000000000 : ℝ), (-1010494531/5000000000 : ℝ), (8463179/15625000 : ℝ)] ![(2166747465071/5000000000000 : ℝ), (2426018096313/20000000000000 : ℝ), (44534960198573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061088109/2000000000 : ℝ)|^8463 ≤ (2166747465071/5000000000000 : ℝ)^6415
        have hw : |(1061088109/2000000000 : ℝ)|=(1061088109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1010494531/5000000000 : ℝ)|^8463 ≤ (2426018096313/20000000000000 : ℝ)^6415
        have hw : |(-1010494531/5000000000 : ℝ)|=(1010494531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8463179/15625000 : ℝ)|^8463 ≤ (44534960198573/100000000000000 : ℝ)^6415
        have hw : |(8463179/15625000 : ℝ)|=(8463179/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s5_6 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1326360099/2500000000 : ℝ)*x 0 + (5416434757/10000000000 : ℝ)*x 1 + (-505247249/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326360099/2500000000 : ℝ)^8463 ≤ (10833736923961/25000000000000 : ℝ)^6415 := by
    have hnat : (1326360099 : ℕ)^8463*25000000000000^6415 ≤ 10833736923961^6415*2500000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326360099 2500000000 10833736923961 25000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5416434757/10000000000 : ℝ)^8463 ≤ (2226748116773/5000000000000 : ℝ)^6415 := by
    have hnat : (5416434757 : ℕ)^8463*5000000000000^6415 ≤ 2226748116773^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416434757 10000000000 2226748116773 5000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (505247249/2500000000 : ℝ)^8463 ≤ (12130089958963/100000000000000 : ℝ)^6415 := by
    have hnat : (505247249 : ℕ)^8463*100000000000000^6415 ≤ 12130089958963^6415*2500000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505247249 2500000000 12130089958963 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326360099/2500000000 : ℝ), (5416434757/10000000000 : ℝ), (-505247249/2500000000 : ℝ)] ![(10833736923961/25000000000000 : ℝ), (2226748116773/5000000000000 : ℝ), (12130089958963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326360099/2500000000 : ℝ)|^8463 ≤ (10833736923961/25000000000000 : ℝ)^6415
        have hw : |(1326360099/2500000000 : ℝ)|=(1326360099/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5416434757/10000000000 : ℝ)|^8463 ≤ (2226748116773/5000000000000 : ℝ)^6415
        have hw : |(5416434757/10000000000 : ℝ)|=(5416434757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-505247249/2500000000 : ℝ)|^8463 ≤ (12130089958963/100000000000000 : ℝ)^6415
        have hw : |(-505247249/2500000000 : ℝ)|=(505247249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s5_7 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (869074283/2000000000 : ℝ)*x 0 + (1131654601/2500000000 : ℝ)*x 1 + (521398947/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (869074283/2000000000 : ℝ)^8463 ≤ (832542409961/2500000000000 : ℝ)^6415 := by
    have hnat : (869074283 : ℕ)^8463*2500000000000^6415 ≤ 832542409961^6415*2000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869074283 2000000000 832542409961 2500000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1131654601/2500000000 : ℝ)^8463 ≤ (17573129045137/50000000000000 : ℝ)^6415 := by
    have hnat : (1131654601 : ℕ)^8463*50000000000000^6415 ≤ 17573129045137^6415*2500000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131654601 2500000000 17573129045137 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521398947/1250000000 : ℝ)^8463 ≤ (986001421649/3125000000000 : ℝ)^6415 := by
    have hnat : (521398947 : ℕ)^8463*3125000000000^6415 ≤ 986001421649^6415*1250000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521398947 1250000000 986001421649 3125000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(869074283/2000000000 : ℝ), (1131654601/2500000000 : ℝ), (521398947/1250000000 : ℝ)] ![(832542409961/2500000000000 : ℝ), (17573129045137/50000000000000 : ℝ), (986001421649/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(869074283/2000000000 : ℝ)|^8463 ≤ (832542409961/2500000000000 : ℝ)^6415
        have hw : |(869074283/2000000000 : ℝ)|=(869074283/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1131654601/2500000000 : ℝ)|^8463 ≤ (17573129045137/50000000000000 : ℝ)^6415
        have hw : |(1131654601/2500000000 : ℝ)|=(1131654601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(521398947/1250000000 : ℝ)|^8463 ≤ (986001421649/3125000000000 : ℝ)^6415
        have hw : |(521398947/1250000000 : ℝ)|=(521398947/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1269_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75978749/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14747/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1089/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (10959/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7337/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14747/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1089/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14747/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1089/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14747/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1089/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14747/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1089/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14747/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1089/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14747/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1089/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1089/10000 : ℝ) ^ (8461/2048 : ℝ) ≤ (5255298541365597/50000000000000000000 : ℝ) := by
    have hpowers : (1089/10000 : ℝ)^8461 ≤ (5255298541365597/50000000000000000000 : ℝ)^2048 := by
      have hnat : (1089 : ℕ)^8461*50000000000000000000^2048 ≤ 5255298541365597^2048*10000^8461 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1089 10000 5255298541365597 50000000000000000000 8461 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1089/10000 : ℝ)) (X := (5255298541365597/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14747/100000 : ℝ) ^ (8461/2048 : ℝ) ≤ (36781200304845907/100000000000000000000 : ℝ) := by
    have hpowers : (14747/100000 : ℝ)^8461 ≤ (36781200304845907/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14747 : ℕ)^8461*100000000000000000000^2048 ≤ 36781200304845907^2048*100000^8461 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14747 100000 36781200304845907 100000000000000000000 8461 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14747/100000 : ℝ)) (X := (36781200304845907/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005255298541365597/25000000000000000000 : ℝ) ≤ (10000508781188843/10000000000000000 : ℝ) ^ (8461/2048 : ℝ) := by
    have hpowers : (25005255298541365597/25000000000000000000 : ℝ)^2048 ≤ (10000508781188843/10000000000000000 : ℝ)^8461 := by
      have hnat : (25005255298541365597 : ℕ)^2048*10000000000000000^8461 ≤ 10000508781188843^8461*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005255298541365597 25000000000000000000 10000508781188843 10000000000000000 2048 8461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000508781188843/10000000000000000 : ℝ)) (X := (25005255298541365597/25000000000000000000 : ℝ)) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047291797387577101/100000000000000000000 : ℝ) ≤ (10001144501210267/10000000000000000 : ℝ) ^ (8461/2048 : ℝ) := by
    have hpowers : (100047291797387577101/100000000000000000000 : ℝ)^2048 ≤ (10001144501210267/10000000000000000 : ℝ)^8461 := by
      have hnat : (100047291797387577101 : ℕ)^2048*10000000000000000^8461 ≤ 10001144501210267^8461*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047291797387577101 100000000000000000000 10001144501210267 10000000000000000 2048 8461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001144501210267/10000000000000000 : ℝ)) (X := (100047291797387577101/100000000000000000000 : ℝ)) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036781200304845907/50000000000000000000 : ℝ) ≤ (10001780221231691/10000000000000000 : ℝ) ^ (8461/2048 : ℝ) := by
    have hpowers : (50036781200304845907/50000000000000000000 : ℝ)^2048 ≤ (10001780221231691/10000000000000000 : ℝ)^8461 := by
      have hnat : (50036781200304845907 : ℕ)^2048*10000000000000000^8461 ≤ 10001780221231691^8461*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036781200304845907 50000000000000000000 10001780221231691 10000000000000000 2048 8461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001780221231691/10000000000000000 : ℝ)) (X := (50036781200304845907/50000000000000000000 : ℝ)) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5255298541365597/50000000000000000000 : ℝ) ≤ ((2029374546683092249/2030000000000000000 : ℝ)+2*(2091184281/1268750000000 : ℝ)*(1089/10000 : ℝ))^(8461/2048 : ℝ) := by
    rw [show (2029374546683092249/2030000000000000000 : ℝ)+2*(2091184281/1268750000000 : ℝ)*(1089/10000 : ℝ)=(10000508781188843/10000000000000000 : ℝ) by norm_num, show 1+2*(5255298541365597/50000000000000000000 : ℝ)=(25005255298541365597/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36781200304845907/100000000000000000000 : ℝ)+(5255298541365597/50000000000000000000 : ℝ) ≤ ((2029374546683092249/2030000000000000000 : ℝ)+(2091184281/1268750000000 : ℝ)*((14747/100000 : ℝ)+(1089/10000 : ℝ)))^(8461/2048 : ℝ) := by
    rw [show (2029374546683092249/2030000000000000000 : ℝ)+(2091184281/1268750000000 : ℝ)*((14747/100000 : ℝ)+(1089/10000 : ℝ))=(10001144501210267/10000000000000000 : ℝ) by norm_num, show 1+(36781200304845907/100000000000000000000 : ℝ)+(5255298541365597/50000000000000000000 : ℝ)=(100047291797387577101/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36781200304845907/100000000000000000000 : ℝ) ≤ ((2029374546683092249/2030000000000000000 : ℝ)+2*(2091184281/1268750000000 : ℝ)*(14747/100000 : ℝ))^(8461/2048 : ℝ) := by
    rw [show (2029374546683092249/2030000000000000000 : ℝ)+2*(2091184281/1268750000000 : ℝ)*(14747/100000 : ℝ)=(10001780221231691/10000000000000000 : ℝ) by norm_num, show 1+2*(36781200304845907/100000000000000000000 : ℝ)=(50036781200304845907/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2029374546683092249/2030000000000000000 : ℝ)*(X 1 0+X 2 0)+(2091184281/1268750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8461/2048 : ℝ)) (lo := (1089/10000 : ℝ)) (hi := (14747/100000 : ℝ)) (c := (2029374546683092249/2030000000000000000 : ℝ)) (alpha := (2091184281/1268750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2029374546683092249/2030000000000000000 : ℝ)*(X 0 1+X 2 1)+(2091184281/1268750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8461/2048 : ℝ)) (lo := (1089/10000 : ℝ)) (hi := (14747/100000 : ℝ)) (c := (2029374546683092249/2030000000000000000 : ℝ)) (alpha := (2091184281/1268750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2029374546683092249/2030000000000000000 : ℝ)*(X 0 2+X 1 2)+(2091184281/1268750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8461/2048 : ℝ)) (lo := (1089/10000 : ℝ)) (hi := (14747/100000 : ℝ)) (c := (2029374546683092249/2030000000000000000 : ℝ)) (alpha := (2091184281/1268750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-526598419/2500000000 : ℝ)*X 0 0+(2708533941/5000000000 : ℝ)*X 0 1+(5241502983/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350271053/10000000000 : ℝ)*X 1 0+(-2195920641/10000000000 : ℝ)*X 1 1+(1310375749/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070054219/2000000000 : ℝ)*X 2 0+(1310375749/2500000000 : ℝ)*X 2 1+(-274490073/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((434534459/1000000000 : ℝ)*X 0 0+(833979959/2000000000 : ℝ)*X 0 1+(905580651/2000000000 : ℝ)*X 0 2+(434534459/1000000000 : ℝ)*X 1 0+(833979959/2000000000 : ℝ)*X 1 1+(905580651/2000000000 : ℝ)*X 1 2+(434534459/1000000000 : ℝ)*X 2 0+(833979959/2000000000 : ℝ)*X 2 1+(905580651/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-263300861/1250000000 : ℝ)*X 0 0+(2621066613/5000000000 : ℝ)*X 0 1+(5416434437/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061088109/2000000000 : ℝ)*X 1 0+(-1010494531/5000000000 : ℝ)*X 1 1+(8463179/15625000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326360099/2500000000 : ℝ)*X 2 0+(5416434757/10000000000 : ℝ)*X 2 1+(-505247249/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((869074283/2000000000 : ℝ)*X 0 0+(1131654601/2500000000 : ℝ)*X 0 1+(521398947/1250000000 : ℝ)*X 0 2+(869074283/2000000000 : ℝ)*X 1 0+(1131654601/2500000000 : ℝ)*X 1 1+(521398947/1250000000 : ℝ)*X 1 2+(869074283/2000000000 : ℝ)*X 2 0+(1131654601/2500000000 : ℝ)*X 2 1+(521398947/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (249557846835583763011447209/50750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (216688499/20000000000000 : ℝ)*(base19) + (264748097/25000000000000 : ℝ)*(base23) + (37004409/100000000000000 : ℝ)*(lower2) + (3946973/2500000000000 : ℝ)*(upper3) + (90371903/50000000000000 : ℝ)*(upper5) + (2122307535859449/50000000000000 : ℝ)*(major0) + (2122307535859449/50000000000000 : ℝ)*(major1) + (2122307535859449/50000000000000 : ℝ)*(major2) + (5695918138329573/100000000000000 : ℝ)*(sp0) + (5695937924866641/100000000000000 : ℝ)*(sp1) + (1423984487329187/25000000000000 : ℝ)*(sp2) + (1396639966630521/50000000000000 : ℝ)*(sp3) + (20869979563/100000000000000 : ℝ)*(sp4) + (11037954409/100000000000000 : ℝ)*(sp7) + (55865819424309/2000000000000 : ℝ)*(f.failure) + (355996188019321/6250000000000 : ℝ)*(f.sum) + (2306087586063/1015000000000000000000000000 : ℝ)*base65 + (1282141244339289199/101500000000000000000000000000000 : ℝ)*base68 + (1484959897740289199/101500000000000000000000000000000 : ℝ)*base70 + (1264171708496289199/101500000000000000000000000000000 : ℝ)*base72 + (2605998241233/1015000000000000000000000000 : ℝ)*base73 + (1857051706059289199/101500000000000000000000000000000 : ℝ)*base76 + (1629181551326789199/101500000000000000000000000000000 : ℝ)*base78 + (736339446315289199/101500000000000000000000000000000 : ℝ)*base80 + (2449870363261/507500000000000000000000000 : ℝ)*base82 + (9441/100000000000000000000 : ℝ)*base89 + (9441/100000000000000000000 : ℝ)*base91 + (9441/100000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (288927301905496908714871029/50750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (807967049/100000000000000 : ℝ)*(base19) + (712953043/100000000000000 : ℝ)*(base23) + (18640497/10000000000000 : ℝ)*(upper3) + (9760391/100000000000000 : ℝ)*(lower4) + (56810447/100000000000000 : ℝ)*(upper5) + (2137677311018469/50000000000000 : ℝ)*(major0) + (2137677311018469/50000000000000 : ℝ)*(major1) + (2137677311018469/50000000000000 : ℝ)*(major2) + (14548514483/100000000000000 : ℝ)*(sp1) + (2019516333/10000000000000 : ℝ)*(sp2) + (5737189038306097/100000000000000 : ℝ)*(sp4) + (1147434736364913/20000000000000 : ℝ)*(sp5) + (1434292032547431/25000000000000 : ℝ)*(sp6) + (2813520015996143/100000000000000 : ℝ)*(sp7) + (2813520015996143/100000000000000 : ℝ)*(f.failure) + (5737189038306097/100000000000000 : ℝ)*(f.sum) + (5276356493113/1015000000000000000000000000 : ℝ)*base65 + (1219541781708853219/101500000000000000000000000000000 : ℝ)*base68 + (1077051926603353219/101500000000000000000000000000000 : ℝ)*base70 + (1010117458471353219/101500000000000000000000000000000 : ℝ)*base72 + (2998439055837/1015000000000000000000000000 : ℝ)*base74 + (1257619927121853219/101500000000000000000000000000000 : ℝ)*base76 + (1302690044266353219/101500000000000000000000000000000 : ℝ)*base78 + (1538261406547853219/101500000000000000000000000000000 : ℝ)*base80 + (434268694761/126875000000000000000000000 : ℝ)*base81 + (33965107/5000000000000000000000 : ℝ)*base89 + (33965107/5000000000000000000000 : ℝ)*base91 + (33965107/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1269_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75978749/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14747/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1089/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10959/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7337/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1269_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1269_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75978749/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8207/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9351/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10959/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7337/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1269_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1269_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1269_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75978749/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8207/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9351/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10959/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7337/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1269_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

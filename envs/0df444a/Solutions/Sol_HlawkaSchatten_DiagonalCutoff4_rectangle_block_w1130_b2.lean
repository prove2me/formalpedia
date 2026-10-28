-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1130_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:26:45.360226+00:00
-- url     : https://prove2.me/submissions/25190104-805f-49db-9065-af3391aca2eb

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
theorem support_rectangle_w1130_s6_0 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2172606361/10000000000 : ℝ)*x 0 + (5393624441/10000000000 : ℝ)*x 1 + (5265189729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2172606361/10000000000 : ℝ)^8323 ≤ (264008896419/2000000000000 : ℝ)^6275 := by
    have hnat : (2172606361 : ℕ)^8323*2000000000000^6275 ≤ 264008896419^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172606361 10000000000 264008896419 2000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393624441/10000000000 : ℝ)^8323 ≤ (22046690509191/50000000000000 : ℝ)^6275 := by
    have hnat : (5393624441 : ℕ)^8323*50000000000000^6275 ≤ 22046690509191^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393624441 10000000000 22046690509191 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265189729/10000000000 : ℝ)^8323 ≤ (42706174149759/100000000000000 : ℝ)^6275 := by
    have hnat : (5265189729 : ℕ)^8323*100000000000000^6275 ≤ 42706174149759^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265189729 10000000000 42706174149759 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2172606361/10000000000 : ℝ), (5393624441/10000000000 : ℝ), (5265189729/10000000000 : ℝ)] ![(264008896419/2000000000000 : ℝ), (22046690509191/50000000000000 : ℝ), (42706174149759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2172606361/10000000000 : ℝ)|^8323 ≤ (264008896419/2000000000000 : ℝ)^6275
        have hw : |(-2172606361/10000000000 : ℝ)|=(2172606361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393624441/10000000000 : ℝ)|^8323 ≤ (22046690509191/50000000000000 : ℝ)^6275
        have hw : |(5393624441/10000000000 : ℝ)|=(5393624441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265189729/10000000000 : ℝ)|^8323 ≤ (42706174149759/100000000000000 : ℝ)^6275
        have hw : |(5265189729/10000000000 : ℝ)|=(5265189729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s6_1 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344894593/10000000000 : ℝ)*x 0 + (-1118879507/5000000000 : ℝ)*x 1 + (5265189727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344894593/10000000000 : ℝ)^8323 ≤ (43565772451243/100000000000000 : ℝ)^6275 := by
    have hnat : (5344894593 : ℕ)^8323*100000000000000^6275 ≤ 43565772451243^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344894593 10000000000 43565772451243 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1118879507/5000000000 : ℝ)^8323 ≤ (343201334923/2500000000000 : ℝ)^6275 := by
    have hnat : (1118879507 : ℕ)^8323*2500000000000^6275 ≤ 343201334923^6275*5000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118879507 5000000000 343201334923 2500000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265189727/10000000000 : ℝ)^8323 ≤ (21353087064121/50000000000000 : ℝ)^6275 := by
    have hnat : (5265189727 : ℕ)^8323*50000000000000^6275 ≤ 21353087064121^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265189727 10000000000 21353087064121 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344894593/10000000000 : ℝ), (-1118879507/5000000000 : ℝ), (5265189727/10000000000 : ℝ)] ![(43565772451243/100000000000000 : ℝ), (343201334923/2500000000000 : ℝ), (21353087064121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344894593/10000000000 : ℝ)|^8323 ≤ (43565772451243/100000000000000 : ℝ)^6275
        have hw : |(5344894593/10000000000 : ℝ)|=(5344894593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1118879507/5000000000 : ℝ)|^8323 ≤ (343201334923/2500000000000 : ℝ)^6275
        have hw : |(-1118879507/5000000000 : ℝ)|=(1118879507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265189727/10000000000 : ℝ)|^8323 ≤ (21353087064121/50000000000000 : ℝ)^6275
        have hw : |(5265189727/10000000000 : ℝ)|=(5265189727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s6_2 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344894587/10000000000 : ℝ)*x 0 + (1053037947/2000000000 : ℝ)*x 1 + (-2237759013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344894587/10000000000 : ℝ)^8323 ≤ (5445721548297/12500000000000 : ℝ)^6275 := by
    have hnat : (5344894587 : ℕ)^8323*12500000000000^6275 ≤ 5445721548297^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344894587 10000000000 5445721548297 12500000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053037947/2000000000 : ℝ)^8323 ≤ (10676543553577/25000000000000 : ℝ)^6275 := by
    have hnat : (1053037947 : ℕ)^8323*25000000000000^6275 ≤ 10676543553577^6275*2000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053037947 2000000000 10676543553577 25000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2237759013/10000000000 : ℝ)^8323 ≤ (13728053388783/100000000000000 : ℝ)^6275 := by
    have hnat : (2237759013 : ℕ)^8323*100000000000000^6275 ≤ 13728053388783^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237759013 10000000000 13728053388783 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344894587/10000000000 : ℝ), (1053037947/2000000000 : ℝ), (-2237759013/10000000000 : ℝ)] ![(5445721548297/12500000000000 : ℝ), (10676543553577/25000000000000 : ℝ), (13728053388783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344894587/10000000000 : ℝ)|^8323 ≤ (5445721548297/12500000000000 : ℝ)^6275
        have hw : |(5344894587/10000000000 : ℝ)|=(5344894587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053037947/2000000000 : ℝ)|^8323 ≤ (10676543553577/25000000000000 : ℝ)^6275
        have hw : |(1053037947/2000000000 : ℝ)|=(1053037947/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2237759013/10000000000 : ℝ)|^8323 ≤ (13728053388783/100000000000000 : ℝ)^6275
        have hw : |(-2237759013/10000000000 : ℝ)|=(2237759013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s6_3 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (436634783/1000000000 : ℝ)*x 0 + (848149217/2000000000 : ℝ)*x 1 + (4495662331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436634783/1000000000 : ℝ)^8323 ≤ (16658355754693/50000000000000 : ℝ)^6275 := by
    have hnat : (436634783 : ℕ)^8323*50000000000000^6275 ≤ 16658355754693^6275*1000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436634783 1000000000 16658355754693 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (848149217/2000000000 : ℝ)^8323 ≤ (4006442730657/12500000000000 : ℝ)^6275 := by
    have hnat : (848149217 : ℕ)^8323*12500000000000^6275 ≤ 4006442730657^6275*2000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848149217 2000000000 4006442730657 12500000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4495662331/10000000000 : ℝ)^8323 ≤ (34631746629183/100000000000000 : ℝ)^6275 := by
    have hnat : (4495662331 : ℕ)^8323*100000000000000^6275 ≤ 34631746629183^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4495662331 10000000000 34631746629183 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(436634783/1000000000 : ℝ), (848149217/2000000000 : ℝ), (4495662331/10000000000 : ℝ)] ![(16658355754693/50000000000000 : ℝ), (4006442730657/12500000000000 : ℝ), (34631746629183/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(436634783/1000000000 : ℝ)|^8323 ≤ (16658355754693/50000000000000 : ℝ)^6275
        have hw : |(436634783/1000000000 : ℝ)|=(436634783/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(848149217/2000000000 : ℝ)|^8323 ≤ (4006442730657/12500000000000 : ℝ)^6275
        have hw : |(848149217/2000000000 : ℝ)|=(848149217/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4495662331/10000000000 : ℝ)|^8323 ≤ (34631746629183/100000000000000 : ℝ)^6275
        have hw : |(4495662331/10000000000 : ℝ)|=(4495662331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s6_4 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1086305713/5000000000 : ℝ)*x 0 + (329094627/625000000 : ℝ)*x 1 + (5393298907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086305713/5000000000 : ℝ)^8323 ≤ (6600242819549/50000000000000 : ℝ)^6275 := by
    have hnat : (1086305713 : ℕ)^8323*50000000000000^6275 ≤ 6600242819549^6275*5000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086305713 5000000000 6600242819549 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329094627/625000000 : ℝ)^8323 ≤ (10677415781751/25000000000000 : ℝ)^6275 := by
    have hnat : (329094627 : ℕ)^8323*25000000000000^6275 ≤ 10677415781751^6275*625000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329094627 625000000 10677415781751 25000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393298907/10000000000 : ℝ)^8323 ≤ (11022462802887/25000000000000 : ℝ)^6275 := by
    have hnat : (5393298907 : ℕ)^8323*25000000000000^6275 ≤ 11022462802887^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393298907 10000000000 11022462802887 25000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1086305713/5000000000 : ℝ), (329094627/625000000 : ℝ), (5393298907/10000000000 : ℝ)] ![(6600242819549/50000000000000 : ℝ), (10677415781751/25000000000000 : ℝ), (11022462802887/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1086305713/5000000000 : ℝ)|^8323 ≤ (6600242819549/50000000000000 : ℝ)^6275
        have hw : |(-1086305713/5000000000 : ℝ)|=(1086305713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329094627/625000000 : ℝ)|^8323 ≤ (10677415781751/25000000000000 : ℝ)^6275
        have hw : |(329094627/625000000 : ℝ)|=(329094627/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393298907/10000000000 : ℝ)|^8323 ≤ (11022462802887/25000000000000 : ℝ)^6275
        have hw : |(5393298907/10000000000 : ℝ)|=(5393298907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s6_5 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (531238423/1000000000 : ℝ)*x 0 + (-2109649837/10000000000 : ℝ)*x 1 + (5393298901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531238423/1000000000 : ℝ)^8323 ≤ (43214646946269/100000000000000 : ℝ)^6275 := by
    have hnat : (531238423 : ℕ)^8323*100000000000000^6275 ≤ 43214646946269^6275*1000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531238423 1000000000 43214646946269 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2109649837/10000000000 : ℝ)^8323 ≤ (6347750946083/50000000000000 : ℝ)^6275 := by
    have hnat : (2109649837 : ℕ)^8323*50000000000000^6275 ≤ 6347750946083^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109649837 10000000000 6347750946083 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393298901/10000000000 : ℝ)^8323 ≤ (4408985114649/10000000000000 : ℝ)^6275 := by
    have hnat : (5393298901 : ℕ)^8323*10000000000000^6275 ≤ 4408985114649^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393298901 10000000000 4408985114649 10000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531238423/1000000000 : ℝ), (-2109649837/10000000000 : ℝ), (5393298901/10000000000 : ℝ)] ![(43214646946269/100000000000000 : ℝ), (6347750946083/50000000000000 : ℝ), (4408985114649/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531238423/1000000000 : ℝ)|^8323 ≤ (43214646946269/100000000000000 : ℝ)^6275
        have hw : |(531238423/1000000000 : ℝ)|=(531238423/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2109649837/10000000000 : ℝ)|^8323 ≤ (6347750946083/50000000000000 : ℝ)^6275
        have hw : |(-2109649837/10000000000 : ℝ)|=(2109649837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393298901/10000000000 : ℝ)|^8323 ≤ (4408985114649/10000000000000 : ℝ)^6275
        have hw : |(5393298901/10000000000 : ℝ)|=(5393298901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s6_6 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (53123843/100000000 : ℝ)*x 0 + (2696649377/5000000000 : ℝ)*x 1 + (-1054824971/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53123843/100000000 : ℝ)^8323 ≤ (8642929540309/20000000000000 : ℝ)^6275 := by
    have hnat : (53123843 : ℕ)^8323*20000000000000^6275 ≤ 8642929540309^6275*100000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53123843 100000000 8642929540309 20000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696649377/5000000000 : ℝ)^8323 ≤ (22044924776283/50000000000000 : ℝ)^6275 := by
    have hnat : (2696649377 : ℕ)^8323*50000000000000^6275 ≤ 22044924776283^6275*5000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696649377 5000000000 22044924776283 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054824971/5000000000 : ℝ)^8323 ≤ (1586937841283/12500000000000 : ℝ)^6275 := by
    have hnat : (1054824971 : ℕ)^8323*12500000000000^6275 ≤ 1586937841283^6275*5000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054824971 5000000000 1586937841283 12500000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53123843/100000000 : ℝ), (2696649377/5000000000 : ℝ), (-1054824971/5000000000 : ℝ)] ![(8642929540309/20000000000000 : ℝ), (22044924776283/50000000000000 : ℝ), (1586937841283/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53123843/100000000 : ℝ)|^8323 ≤ (8642929540309/20000000000000 : ℝ)^6275
        have hw : |(53123843/100000000 : ℝ)|=(53123843/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696649377/5000000000 : ℝ)|^8323 ≤ (22044924776283/50000000000000 : ℝ)^6275
        have hw : |(2696649377/5000000000 : ℝ)|=(2696649377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1054824971/5000000000 : ℝ)|^8323 ≤ (1586937841283/12500000000000 : ℝ)^6275
        have hw : |(-1054824971/5000000000 : ℝ)|=(1054824971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s6_7 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4366357741/10000000000 : ℝ)*x 0 + (140469329/312500000 : ℝ)*x 1 + (2120696117/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4366357741/10000000000 : ℝ)^8323 ≤ (6663362363109/20000000000000 : ℝ)^6275 := by
    have hnat : (4366357741 : ℕ)^8323*20000000000000^6275 ≤ 6663362363109^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4366357741 10000000000 6663362363109 20000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (140469329/312500000 : ℝ)^8323 ≤ (3462516869199/10000000000000 : ℝ)^6275 := by
    have hnat : (140469329 : ℕ)^8323*10000000000000^6275 ≤ 3462516869199^6275*312500000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140469329 312500000 3462516869199 10000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2120696117/5000000000 : ℝ)^8323 ≤ (32058019477607/100000000000000 : ℝ)^6275 := by
    have hnat : (2120696117 : ℕ)^8323*100000000000000^6275 ≤ 32058019477607^6275*5000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120696117 5000000000 32058019477607 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4366357741/10000000000 : ℝ), (140469329/312500000 : ℝ), (2120696117/5000000000 : ℝ)] ![(6663362363109/20000000000000 : ℝ), (3462516869199/10000000000000 : ℝ), (32058019477607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4366357741/10000000000 : ℝ)|^8323 ≤ (6663362363109/20000000000000 : ℝ)^6275
        have hw : |(4366357741/10000000000 : ℝ)|=(4366357741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(140469329/312500000 : ℝ)|^8323 ≤ (3462516869199/10000000000000 : ℝ)^6275
        have hw : |(140469329/312500000 : ℝ)|=(140469329/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2120696117/5000000000 : ℝ)|^8323 ≤ (32058019477607/100000000000000 : ℝ)^6275
        have hw : |(2120696117/5000000000 : ℝ)|=(2120696117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1130_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149239627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3521/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11297/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1133/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (281/2000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3521/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11297/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3521/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11297/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3521/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11297/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3521/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11297/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3521/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11297/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3521/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11297/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11297/100000 : ℝ) ^ (4161/1024 : ℝ) ≤ (3545503174387897/25000000000000000000 : ℝ) := by
    have hpowers : (11297/100000 : ℝ)^4161 ≤ (3545503174387897/25000000000000000000 : ℝ)^1024 := by
      have hnat : (11297 : ℕ)^4161*25000000000000000000^1024 ≤ 3545503174387897^1024*100000^4161 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11297 100000 3545503174387897 25000000000000000000 4161 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11297/100000 : ℝ)) (X := (3545503174387897/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3521/25000 : ℝ) ^ (4161/1024 : ℝ) ≤ (17371532120903441/50000000000000000000 : ℝ) := by
    have hpowers : (3521/25000 : ℝ)^4161 ≤ (17371532120903441/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3521 : ℕ)^4161*50000000000000000000^1024 ≤ 17371532120903441^1024*25000^4161 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3521 25000 17371532120903441 50000000000000000000 4161 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3521/25000 : ℝ)) (X := (17371532120903441/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503545503174387897/12500000000000000000 : ℝ) ≤ (1250087243622579/1250000000000000 : ℝ) ^ (4161/1024 : ℝ) := by
    have hpowers : (12503545503174387897/12500000000000000000 : ℝ)^1024 ≤ (1250087243622579/1250000000000000 : ℝ)^4161 := by
      have hnat : (12503545503174387897 : ℕ)^1024*1250000000000000^4161 ≤ 1250087243622579^4161*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503545503174387897 12500000000000000000 1250087243622579 1250000000000000 1024 4161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250087243622579/1250000000000000 : ℝ)) (X := (12503545503174387897/12500000000000000000 : ℝ)) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004892507693935847/10000000000000000000 : ℝ) ≤ (10001203798171103/10000000000000000 : ℝ) ^ (4161/1024 : ℝ) := by
    have hpowers : (10004892507693935847/10000000000000000000 : ℝ)^1024 ≤ (10001203798171103/10000000000000000 : ℝ)^4161 := by
      have hnat : (10004892507693935847 : ℕ)^1024*10000000000000000^4161 ≤ 10001203798171103^4161*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004892507693935847 10000000000000000000 10001203798171103 10000000000000000 1024 4161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001203798171103/10000000000000000 : ℝ)) (X := (10004892507693935847/10000000000000000000 : ℝ)) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017371532120903441/25000000000000000000 : ℝ) ≤ (5000854823680787/5000000000000000 : ℝ) ^ (4161/1024 : ℝ) := by
    have hpowers : (25017371532120903441/25000000000000000000 : ℝ)^1024 ≤ (5000854823680787/5000000000000000 : ℝ)^4161 := by
      have hnat : (25017371532120903441 : ℕ)^1024*5000000000000000^4161 ≤ 5000854823680787^4161*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017371532120903441 25000000000000000000 5000854823680787 5000000000000000 1024 4161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000854823680787/5000000000000000 : ℝ)) (X := (25017371532120903441/25000000000000000000 : ℝ)) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3545503174387897/25000000000000000000 : ℝ) ≤ ((2786051602719951961/2787000000000000000 : ℝ)+2*(505849190471/278700000000000 : ℝ)*(11297/100000 : ℝ))^(4161/1024 : ℝ) := by
    rw [show (2786051602719951961/2787000000000000000 : ℝ)+2*(505849190471/278700000000000 : ℝ)*(11297/100000 : ℝ)=(1250087243622579/1250000000000000 : ℝ) by norm_num, show 1+2*(3545503174387897/25000000000000000000 : ℝ)=(12503545503174387897/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17371532120903441/50000000000000000000 : ℝ)+(3545503174387897/25000000000000000000 : ℝ) ≤ ((2786051602719951961/2787000000000000000 : ℝ)+(505849190471/278700000000000 : ℝ)*((3521/25000 : ℝ)+(11297/100000 : ℝ)))^(4161/1024 : ℝ) := by
    rw [show (2786051602719951961/2787000000000000000 : ℝ)+(505849190471/278700000000000 : ℝ)*((3521/25000 : ℝ)+(11297/100000 : ℝ))=(10001203798171103/10000000000000000 : ℝ) by norm_num, show 1+(17371532120903441/50000000000000000000 : ℝ)+(3545503174387897/25000000000000000000 : ℝ)=(10004892507693935847/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17371532120903441/50000000000000000000 : ℝ) ≤ ((2786051602719951961/2787000000000000000 : ℝ)+2*(505849190471/278700000000000 : ℝ)*(3521/25000 : ℝ))^(4161/1024 : ℝ) := by
    rw [show (2786051602719951961/2787000000000000000 : ℝ)+2*(505849190471/278700000000000 : ℝ)*(3521/25000 : ℝ)=(5000854823680787/5000000000000000 : ℝ) by norm_num, show 1+2*(17371532120903441/50000000000000000000 : ℝ)=(25017371532120903441/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2786051602719951961/2787000000000000000 : ℝ)*(X 1 0+X 2 0)+(505849190471/278700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4161/1024 : ℝ)) (lo := (11297/100000 : ℝ)) (hi := (3521/25000 : ℝ)) (c := (2786051602719951961/2787000000000000000 : ℝ)) (alpha := (505849190471/278700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2786051602719951961/2787000000000000000 : ℝ)*(X 0 1+X 2 1)+(505849190471/278700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4161/1024 : ℝ)) (lo := (11297/100000 : ℝ)) (hi := (3521/25000 : ℝ)) (c := (2786051602719951961/2787000000000000000 : ℝ)) (alpha := (505849190471/278700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2786051602719951961/2787000000000000000 : ℝ)*(X 0 2+X 1 2)+(505849190471/278700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4161/1024 : ℝ)) (lo := (11297/100000 : ℝ)) (hi := (3521/25000 : ℝ)) (c := (2786051602719951961/2787000000000000000 : ℝ)) (alpha := (505849190471/278700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2172606361/10000000000 : ℝ)*X 0 0+(5393624441/10000000000 : ℝ)*X 0 1+(5265189729/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344894593/10000000000 : ℝ)*X 1 0+(-1118879507/5000000000 : ℝ)*X 1 1+(5265189727/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344894587/10000000000 : ℝ)*X 2 0+(1053037947/2000000000 : ℝ)*X 2 1+(-2237759013/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((436634783/1000000000 : ℝ)*X 0 0+(848149217/2000000000 : ℝ)*X 0 1+(4495662331/10000000000 : ℝ)*X 0 2+(436634783/1000000000 : ℝ)*X 1 0+(848149217/2000000000 : ℝ)*X 1 1+(4495662331/10000000000 : ℝ)*X 1 2+(436634783/1000000000 : ℝ)*X 2 0+(848149217/2000000000 : ℝ)*X 2 1+(4495662331/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1086305713/5000000000 : ℝ)*X 0 0+(329094627/625000000 : ℝ)*X 0 1+(5393298907/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((531238423/1000000000 : ℝ)*X 1 0+(-2109649837/10000000000 : ℝ)*X 1 1+(5393298901/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((53123843/100000000 : ℝ)*X 2 0+(2696649377/5000000000 : ℝ)*X 2 1+(-1054824971/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4366357741/10000000000 : ℝ)*X 0 0+(140469329/312500000 : ℝ)*X 0 1+(2120696117/5000000000 : ℝ)*X 0 2+(4366357741/10000000000 : ℝ)*X 1 0+(140469329/312500000 : ℝ)*X 1 1+(2120696117/5000000000 : ℝ)*X 1 2+(4366357741/10000000000 : ℝ)*X 2 0+(140469329/312500000 : ℝ)*X 2 1+(2120696117/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3556031230327870862871249/929000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (400446397/50000000000000 : ℝ)*(base19) + (181951127/25000000000000 : ℝ)*(base23) + (17196629/50000000000000 : ℝ)*(lower2) + (100661507/100000000000000 : ℝ)*(upper3) + (27012387/50000000000000 : ℝ)*(upper5) + (117089811749391/2000000000000 : ℝ)*(major0) + (117089811749391/2000000000000 : ℝ)*(major1) + (117089811749391/2000000000000 : ℝ)*(major2) + (1946520005964723/25000000000000 : ℝ)*(sp0) + (973262605534409/12500000000000 : ℝ)*(sp1) + (3893050458681779/50000000000000 : ℝ)*(sp2) + (980716900293019/25000000000000 : ℝ)*(sp3) + (21621309173/100000000000000 : ℝ)*(sp4) + (2950251359/25000000000000 : ℝ)*(sp7) + (3922879402177513/100000000000000 : ℝ)*(f.failure) + (1557220329033613/20000000000000 : ℝ)*(f.sum) + (160456483149/14515625000000000000000000 : ℝ)*base65 + (10193735040663917/1858000000000000000000000000000 : ℝ)*base67 + (14118738147849917/1858000000000000000000000000000 : ℝ)*base69 + (114902080944083/1858000000000000000000000000000 : ℝ)*base72 + (595411544293/92900000000000000000000000 : ℝ)*base73 + (14012936189920083/1858000000000000000000000000000 : ℝ)*base76 + (1466523006555917/1858000000000000000000000000000 : ℝ)*base77 + (575831072187917/1858000000000000000000000000000 : ℝ)*base79 + (281565389613/29031250000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (27907651/10000000000000000000000 : ℝ)*base89 + (27907651/10000000000000000000000 : ℝ)*base91 + (27907651/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8856290222539750436573/2322500000000000000000000000 : ℝ) := by norm_num
    linear_combination (466221091/50000000000000 : ℝ)*(base19) + (515979607/50000000000000 : ℝ)*(base23) + (21656593/100000000000000 : ℝ)*(upper2) + (14589491/20000000000000 : ℝ)*(upper3) + (133857409/100000000000000 : ℝ)*(upper5) + (2942115761203607/50000000000000 : ℝ)*(major0) + (2942115761203607/50000000000000 : ℝ)*(major1) + (2942115761203607/50000000000000 : ℝ)*(major2) + (27469179809/100000000000000 : ℝ)*(sp1) + (5054892207/25000000000000 : ℝ)*(sp2) + (7825655205912773/100000000000000 : ℝ)*(sp4) + (7825626804290781/100000000000000 : ℝ)*(sp5) + (1956408488596183/25000000000000 : ℝ)*(sp6) + (3942807711793071/100000000000000 : ℝ)*(sp7) + (3942807711793071/100000000000000 : ℝ)*(f.failure) + (7825655205912773/100000000000000 : ℝ)*(f.sum) + (13410874483861/13935000000000000000000000000 : ℝ)*base66 + (1813552384831109/46450000000000000000000000000000 : ℝ)*base67 + (343978210563381109/46450000000000000000000000000000 : ℝ)*base69 + (299894003738468891/46450000000000000000000000000000 : ℝ)*base72 + (24752211148019/13935000000000000000000000000 : ℝ)*base73 + (243826682144531109/46450000000000000000000000000000 : ℝ)*base75 + (304538319483518891/46450000000000000000000000000000 : ℝ)*base78 + (74562964324568891/46450000000000000000000000000000 : ℝ)*base80 + (3467732315921/3483750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (17224517/10000000000000000000000 : ℝ)*base89 + (17224517/10000000000000000000000 : ℝ)*base91 + (17224517/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1130_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149239627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3521/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11297/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1133/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (281/2000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1130_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1130_s7_0 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-217263453/1000000000 : ℝ)*x 0 + (5393280097/10000000000 : ℝ)*x 1 + (1316378921/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (217263453/1000000000 : ℝ)^8323 ≤ (1650083978937/12500000000000 : ℝ)^6275 := by
    have hnat : (217263453 : ℕ)^8323*12500000000000^6275 ≤ 1650083978937^6275*1000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217263453 1000000000 1650083978937 12500000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393280097/10000000000 : ℝ)^8323 ≤ (11022411813609/25000000000000 : ℝ)^6275 := by
    have hnat : (5393280097 : ℕ)^8323*25000000000000^6275 ≤ 11022411813609^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393280097 10000000000 11022411813609 25000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316378921/2500000000 : ℝ)^8323 ≤ (1067742022501/2500000000000 : ℝ)^6275 := by
    have hnat : (1316378921 : ℕ)^8323*2500000000000^6275 ≤ 1067742022501^6275*2500000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316378921 2500000000 1067742022501 2500000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-217263453/1000000000 : ℝ), (5393280097/10000000000 : ℝ), (1316378921/2500000000 : ℝ)] ![(1650083978937/12500000000000 : ℝ), (11022411813609/25000000000000 : ℝ), (1067742022501/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-217263453/1000000000 : ℝ)|^8323 ≤ (1650083978937/12500000000000 : ℝ)^6275
        have hw : |(-217263453/1000000000 : ℝ)|=(217263453/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393280097/10000000000 : ℝ)|^8323 ≤ (11022411813609/25000000000000 : ℝ)^6275
        have hw : |(5393280097/10000000000 : ℝ)|=(5393280097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316378921/2500000000 : ℝ)|^8323 ≤ (1067742022501/2500000000000 : ℝ)^6275
        have hw : |(1316378921/2500000000 : ℝ)|=(1316378921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s7_1 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (267240429/500000000 : ℝ)*x 0 + (-279680289/1250000000 : ℝ)*x 1 + (526551569/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267240429/500000000 : ℝ)^8323 ≤ (2722802659567/6250000000000 : ℝ)^6275 := by
    have hnat : (267240429 : ℕ)^8323*6250000000000^6275 ≤ 2722802659567^6275*500000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267240429 500000000 2722802659567 6250000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (279680289/1250000000 : ℝ)^8323 ≤ (686273823357/5000000000000 : ℝ)^6275 := by
    have hnat : (279680289 : ℕ)^8323*5000000000000^6275 ≤ 686273823357^6275*1250000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279680289 1250000000 686273823357 5000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526551569/1000000000 : ℝ)^8323 ≤ (42709680964591/100000000000000 : ℝ)^6275 := by
    have hnat : (526551569 : ℕ)^8323*100000000000000^6275 ≤ 42709680964591^6275*1000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526551569 1000000000 42709680964591 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267240429/500000000 : ℝ), (-279680289/1250000000 : ℝ), (526551569/1000000000 : ℝ)] ![(2722802659567/6250000000000 : ℝ), (686273823357/5000000000000 : ℝ), (42709680964591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267240429/500000000 : ℝ)|^8323 ≤ (2722802659567/6250000000000 : ℝ)^6275
        have hw : |(267240429/500000000 : ℝ)|=(267240429/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-279680289/1250000000 : ℝ)|^8323 ≤ (686273823357/5000000000000 : ℝ)^6275
        have hw : |(-279680289/1250000000 : ℝ)|=(279680289/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526551569/1000000000 : ℝ)|^8323 ≤ (42709680964591/100000000000000 : ℝ)^6275
        have hw : |(526551569/1000000000 : ℝ)|=(526551569/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s7_2 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (267240429/500000000 : ℝ)*x 0 + (5265515689/10000000000 : ℝ)*x 1 + (-1118721157/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267240429/500000000 : ℝ)^8323 ≤ (2722802659567/6250000000000 : ℝ)^6275 := by
    have hnat : (267240429 : ℕ)^8323*6250000000000^6275 ≤ 2722802659567^6275*500000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267240429 500000000 2722802659567 6250000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265515689/10000000000 : ℝ)^8323 ≤ (5338710119229/12500000000000 : ℝ)^6275 := by
    have hnat : (5265515689 : ℕ)^8323*12500000000000^6275 ≤ 5338710119229^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265515689 10000000000 5338710119229 12500000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1118721157/5000000000 : ℝ)^8323 ≤ (6862738241707/50000000000000 : ℝ)^6275 := by
    have hnat : (1118721157 : ℕ)^8323*50000000000000^6275 ≤ 6862738241707^6275*5000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118721157 5000000000 6862738241707 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267240429/500000000 : ℝ), (5265515689/10000000000 : ℝ), (-1118721157/5000000000 : ℝ)] ![(2722802659567/6250000000000 : ℝ), (5338710119229/12500000000000 : ℝ), (6862738241707/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267240429/500000000 : ℝ)|^8323 ≤ (2722802659567/6250000000000 : ℝ)^6275
        have hw : |(267240429/500000000 : ℝ)|=(267240429/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265515689/10000000000 : ℝ)|^8323 ≤ (5338710119229/12500000000000 : ℝ)^6275
        have hw : |(5265515689/10000000000 : ℝ)|=(5265515689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1118721157/5000000000 : ℝ)|^8323 ≤ (6862738241707/50000000000000 : ℝ)^6275
        have hw : |(-1118721157/5000000000 : ℝ)|=(1118721157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s7_3 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2183182461/5000000000 : ℝ)*x 0 + (4241409043/10000000000 : ℝ)*x 1 + (2247497461/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183182461/5000000000 : ℝ)^8323 ≤ (16658442246133/50000000000000 : ℝ)^6275 := by
    have hnat : (2183182461 : ℕ)^8323*50000000000000^6275 ≤ 16658442246133^6275*5000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183182461 5000000000 16658442246133 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4241409043/10000000000 : ℝ)^8323 ≤ (6411637598367/20000000000000 : ℝ)^6275 := by
    have hnat : (4241409043 : ℕ)^8323*20000000000000^6275 ≤ 6411637598367^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241409043 10000000000 6411637598367 20000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2247497461/5000000000 : ℝ)^8323 ≤ (34624927507927/100000000000000 : ℝ)^6275 := by
    have hnat : (2247497461 : ℕ)^8323*100000000000000^6275 ≤ 34624927507927^6275*5000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247497461 5000000000 34624927507927 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2183182461/5000000000 : ℝ), (4241409043/10000000000 : ℝ), (2247497461/5000000000 : ℝ)] ![(16658442246133/50000000000000 : ℝ), (6411637598367/20000000000000 : ℝ), (34624927507927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2183182461/5000000000 : ℝ)|^8323 ≤ (16658442246133/50000000000000 : ℝ)^6275
        have hw : |(2183182461/5000000000 : ℝ)|=(2183182461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4241409043/10000000000 : ℝ)|^8323 ≤ (6411637598367/20000000000000 : ℝ)^6275
        have hw : |(4241409043/10000000000 : ℝ)|=(4241409043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2247497461/5000000000 : ℝ)|^8323 ≤ (34624927507927/100000000000000 : ℝ)^6275
        have hw : |(2247497461/5000000000 : ℝ)|=(2247497461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s7_4 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1086319151/5000000000 : ℝ)*x 0 + (5265838807/10000000000 : ℝ)*x 1 + (5392956683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086319151/5000000000 : ℝ)^8323 ≤ (6600351114829/50000000000000 : ℝ)^6275 := by
    have hnat : (1086319151 : ℕ)^8323*50000000000000^6275 ≤ 6600351114829^6275*5000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086319151 5000000000 6600351114829 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265838807/10000000000 : ℝ)^8323 ≤ (2669572328281/6250000000000 : ℝ)^6275 := by
    have hnat : (5265838807 : ℕ)^8323*6250000000000^6275 ≤ 2669572328281^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265838807 10000000000 2669572328281 6250000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392956683/10000000000 : ℝ)^8323 ≤ (22043070253941/50000000000000 : ℝ)^6275 := by
    have hnat : (5392956683 : ℕ)^8323*50000000000000^6275 ≤ 22043070253941^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392956683 10000000000 22043070253941 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1086319151/5000000000 : ℝ), (5265838807/10000000000 : ℝ), (5392956683/10000000000 : ℝ)] ![(6600351114829/50000000000000 : ℝ), (2669572328281/6250000000000 : ℝ), (22043070253941/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1086319151/5000000000 : ℝ)|^8323 ≤ (6600351114829/50000000000000 : ℝ)^6275
        have hw : |(-1086319151/5000000000 : ℝ)|=(1086319151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265838807/10000000000 : ℝ)|^8323 ≤ (2669572328281/6250000000000 : ℝ)^6275
        have hw : |(5265838807/10000000000 : ℝ)|=(5265838807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392956683/10000000000 : ℝ)|^8323 ≤ (22043070253941/50000000000000 : ℝ)^6275
        have hw : |(5392956683/10000000000 : ℝ)|=(5392956683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s7_5 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312466919/10000000000 : ℝ)*x 0 + (-2109999551/10000000000 : ℝ)*x 1 + (5392959173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312466919/10000000000 : ℝ)^8323 ≤ (10803884783629/25000000000000 : ℝ)^6275 := by
    have hnat : (5312466919 : ℕ)^8323*25000000000000^6275 ≤ 10803884783629^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312466919 10000000000 10803884783629 25000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2109999551/10000000000 : ℝ)^8323 ≤ (6349146672933/50000000000000 : ℝ)^6275 := by
    have hnat : (2109999551 : ℕ)^8323*50000000000000^6275 ≤ 6349146672933^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109999551 10000000000 6349146672933 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392959173/10000000000 : ℝ)^8323 ≤ (2755385469153/6250000000000 : ℝ)^6275 := by
    have hnat : (5392959173 : ℕ)^8323*6250000000000^6275 ≤ 2755385469153^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392959173 10000000000 2755385469153 6250000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312466919/10000000000 : ℝ), (-2109999551/10000000000 : ℝ), (5392959173/10000000000 : ℝ)] ![(10803884783629/25000000000000 : ℝ), (6349146672933/50000000000000 : ℝ), (2755385469153/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312466919/10000000000 : ℝ)|^8323 ≤ (10803884783629/25000000000000 : ℝ)^6275
        have hw : |(5312466919/10000000000 : ℝ)|=(5312466919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2109999551/10000000000 : ℝ)|^8323 ≤ (6349146672933/50000000000000 : ℝ)^6275
        have hw : |(-2109999551/10000000000 : ℝ)|=(2109999551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392959173/10000000000 : ℝ)|^8323 ≤ (2755385469153/6250000000000 : ℝ)^6275
        have hw : |(5392959173/10000000000 : ℝ)|=(5392959173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s7_6 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328116493/2500000000 : ℝ)*x 0 + (5392959911/10000000000 : ℝ)*x 1 + (-2109999829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328116493/2500000000 : ℝ)^8323 ≤ (43215528916659/100000000000000 : ℝ)^6275 := by
    have hnat : (1328116493 : ℕ)^8323*100000000000000^6275 ≤ 43215528916659^6275*2500000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328116493 2500000000 43215528916659 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392959911/10000000000 : ℝ)^8323 ≤ (44086175508433/100000000000000 : ℝ)^6275 := by
    have hnat : (5392959911 : ℕ)^8323*100000000000000^6275 ≤ 44086175508433^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392959911 10000000000 44086175508433 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2109999829/10000000000 : ℝ)^8323 ≤ (12698295564951/100000000000000 : ℝ)^6275 := by
    have hnat : (2109999829 : ℕ)^8323*100000000000000^6275 ≤ 12698295564951^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109999829 10000000000 12698295564951 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328116493/2500000000 : ℝ), (5392959911/10000000000 : ℝ), (-2109999829/10000000000 : ℝ)] ![(43215528916659/100000000000000 : ℝ), (44086175508433/100000000000000 : ℝ), (12698295564951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328116493/2500000000 : ℝ)|^8323 ≤ (43215528916659/100000000000000 : ℝ)^6275
        have hw : |(1328116493/2500000000 : ℝ)|=(1328116493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392959911/10000000000 : ℝ)|^8323 ≤ (44086175508433/100000000000000 : ℝ)^6275
        have hw : |(5392959911/10000000000 : ℝ)|=(5392959911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2109999829/10000000000 : ℝ)|^8323 ≤ (12698295564951/100000000000000 : ℝ)^6275
        have hw : |(-2109999829/10000000000 : ℝ)|=(2109999829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s7_7 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4366375247/10000000000 : ℝ)*x 0 + (4494356701/10000000000 : ℝ)*x 1 + (212102451/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4366375247/10000000000 : ℝ)^8323 ≤ (16658494494263/50000000000000 : ℝ)^6275 := by
    have hnat : (4366375247 : ℕ)^8323*50000000000000^6275 ≤ 16658494494263^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4366375247 10000000000 16658494494263 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4494356701/10000000000 : ℝ)^8323 ≤ (34618406918449/100000000000000 : ℝ)^6275 := by
    have hnat : (4494356701 : ℕ)^8323*100000000000000^6275 ≤ 34618406918449^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4494356701 10000000000 34618406918449 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (212102451/500000000 : ℝ)^8323 ≤ (125252359671/390625000000 : ℝ)^6275 := by
    have hnat : (212102451 : ℕ)^8323*390625000000^6275 ≤ 125252359671^6275*500000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212102451 500000000 125252359671 390625000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4366375247/10000000000 : ℝ), (4494356701/10000000000 : ℝ), (212102451/500000000 : ℝ)] ![(16658494494263/50000000000000 : ℝ), (34618406918449/100000000000000 : ℝ), (125252359671/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4366375247/10000000000 : ℝ)|^8323 ≤ (16658494494263/50000000000000 : ℝ)^6275
        have hw : |(4366375247/10000000000 : ℝ)|=(4366375247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4494356701/10000000000 : ℝ)|^8323 ≤ (34618406918449/100000000000000 : ℝ)^6275
        have hw : |(4494356701/10000000000 : ℝ)|=(4494356701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(212102451/500000000 : ℝ)|^8323 ≤ (125252359671/390625000000 : ℝ)^6275
        have hw : |(212102451/500000000 : ℝ)|=(212102451/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1130_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149239627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (281/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1133/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (11337/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14043/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (281/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1133/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (281/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1133/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (281/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1133/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (281/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1133/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (281/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1133/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (281/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1133/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (1133/10000 : ℝ) ^ (4161/1024 : ℝ) ≤ (7175553544963799/50000000000000000000 : ℝ) := by
    have hpowers : (1133/10000 : ℝ)^4161 ≤ (7175553544963799/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1133 : ℕ)^4161*50000000000000000000^1024 ≤ 7175553544963799^1024*10000^4161 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1133 10000 7175553544963799 50000000000000000000 4161 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1133/10000 : ℝ)) (X := (7175553544963799/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (281/2000 : ℝ) ^ (4161/1024 : ℝ) ≤ (34403507337671297/100000000000000000000 : ℝ) := by
    have hpowers : (281/2000 : ℝ)^4161 ≤ (34403507337671297/100000000000000000000 : ℝ)^1024 := by
      have hnat : (281 : ℕ)^4161*100000000000000000000^1024 ≤ 34403507337671297^1024*2000^4161 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        281 2000 34403507337671297 100000000000000000000 4161 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (281/2000 : ℝ)) (X := (34403507337671297/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007175553544963799/25000000000000000000 : ℝ) ≤ (5000353134918573/5000000000000000 : ℝ) ^ (4161/1024 : ℝ) := by
    have hpowers : (25007175553544963799/25000000000000000000 : ℝ)^1024 ≤ (5000353134918573/5000000000000000 : ℝ)^4161 := by
      have hnat : (25007175553544963799 : ℕ)^1024*5000000000000000^4161 ≤ 5000353134918573^4161*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007175553544963799 25000000000000000000 5000353134918573 5000000000000000 1024 4161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000353134918573/5000000000000000 : ℝ)) (X := (25007175553544963799/25000000000000000000 : ℝ)) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009750922885519779/20000000000000000000 : ℝ) ≤ (2000239920944637/2000000000000000 : ℝ) ^ (4161/1024 : ℝ) := by
    have hpowers : (20009750922885519779/20000000000000000000 : ℝ)^1024 ≤ (2000239920944637/2000000000000000 : ℝ)^4161 := by
      have hnat : (20009750922885519779 : ℕ)^1024*2000000000000000^4161 ≤ 2000239920944637^4161*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009750922885519779 20000000000000000000 2000239920944637 2000000000000000 1024 4161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000239920944637/2000000000000000 : ℝ)) (X := (20009750922885519779/20000000000000000000 : ℝ)) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034403507337671297/50000000000000000000 : ℝ) ≤ (1250211617451153/1250000000000000 : ℝ) ^ (4161/1024 : ℝ) := by
    have hpowers : (50034403507337671297/50000000000000000000 : ℝ)^1024 ≤ (1250211617451153/1250000000000000 : ℝ)^4161 := by
      have hnat : (50034403507337671297 : ℕ)^1024*1250000000000000^4161 ≤ 1250211617451153^4161*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034403507337671297 50000000000000000000 1250211617451153 1250000000000000 1024 4161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250211617451153/1250000000000000 : ℝ)) (X := (50034403507337671297/50000000000000000000 : ℝ)) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7175553544963799/50000000000000000000 : ℝ) ≤ ((1359537104271969669/1360000000000000000 : ℝ)+2*(493334886039/272000000000000 : ℝ)*(1133/10000 : ℝ))^(4161/1024 : ℝ) := by
    rw [show (1359537104271969669/1360000000000000000 : ℝ)+2*(493334886039/272000000000000 : ℝ)*(1133/10000 : ℝ)=(5000353134918573/5000000000000000 : ℝ) by norm_num, show 1+2*(7175553544963799/50000000000000000000 : ℝ)=(25007175553544963799/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34403507337671297/100000000000000000000 : ℝ)+(7175553544963799/50000000000000000000 : ℝ) ≤ ((1359537104271969669/1360000000000000000 : ℝ)+(493334886039/272000000000000 : ℝ)*((281/2000 : ℝ)+(1133/10000 : ℝ)))^(4161/1024 : ℝ) := by
    rw [show (1359537104271969669/1360000000000000000 : ℝ)+(493334886039/272000000000000 : ℝ)*((281/2000 : ℝ)+(1133/10000 : ℝ))=(2000239920944637/2000000000000000 : ℝ) by norm_num, show 1+(34403507337671297/100000000000000000000 : ℝ)+(7175553544963799/50000000000000000000 : ℝ)=(20009750922885519779/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34403507337671297/100000000000000000000 : ℝ) ≤ ((1359537104271969669/1360000000000000000 : ℝ)+2*(493334886039/272000000000000 : ℝ)*(281/2000 : ℝ))^(4161/1024 : ℝ) := by
    rw [show (1359537104271969669/1360000000000000000 : ℝ)+2*(493334886039/272000000000000 : ℝ)*(281/2000 : ℝ)=(1250211617451153/1250000000000000 : ℝ) by norm_num, show 1+2*(34403507337671297/100000000000000000000 : ℝ)=(50034403507337671297/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1359537104271969669/1360000000000000000 : ℝ)*(X 1 0+X 2 0)+(493334886039/272000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4161/1024 : ℝ)) (lo := (1133/10000 : ℝ)) (hi := (281/2000 : ℝ)) (c := (1359537104271969669/1360000000000000000 : ℝ)) (alpha := (493334886039/272000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1359537104271969669/1360000000000000000 : ℝ)*(X 0 1+X 2 1)+(493334886039/272000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4161/1024 : ℝ)) (lo := (1133/10000 : ℝ)) (hi := (281/2000 : ℝ)) (c := (1359537104271969669/1360000000000000000 : ℝ)) (alpha := (493334886039/272000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1359537104271969669/1360000000000000000 : ℝ)*(X 0 2+X 1 2)+(493334886039/272000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4161/1024 : ℝ)) (lo := (1133/10000 : ℝ)) (hi := (281/2000 : ℝ)) (c := (1359537104271969669/1360000000000000000 : ℝ)) (alpha := (493334886039/272000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-217263453/1000000000 : ℝ)*X 0 0+(5393280097/10000000000 : ℝ)*X 0 1+(1316378921/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267240429/500000000 : ℝ)*X 1 0+(-279680289/1250000000 : ℝ)*X 1 1+(526551569/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267240429/500000000 : ℝ)*X 2 0+(5265515689/10000000000 : ℝ)*X 2 1+(-1118721157/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2183182461/5000000000 : ℝ)*X 0 0+(4241409043/10000000000 : ℝ)*X 0 1+(2247497461/5000000000 : ℝ)*X 0 2+(2183182461/5000000000 : ℝ)*X 1 0+(4241409043/10000000000 : ℝ)*X 1 1+(2247497461/5000000000 : ℝ)*X 1 2+(2183182461/5000000000 : ℝ)*X 2 0+(4241409043/10000000000 : ℝ)*X 2 1+(2247497461/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1086319151/5000000000 : ℝ)*X 0 0+(5265838807/10000000000 : ℝ)*X 0 1+(5392956683/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312466919/10000000000 : ℝ)*X 1 0+(-2109999551/10000000000 : ℝ)*X 1 1+(5392959173/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328116493/2500000000 : ℝ)*X 2 0+(5392959911/10000000000 : ℝ)*X 2 1+(-2109999829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4366375247/10000000000 : ℝ)*X 0 0+(4494356701/10000000000 : ℝ)*X 0 1+(212102451/500000000 : ℝ)*X 0 2+(4366375247/10000000000 : ℝ)*X 1 0+(4494356701/10000000000 : ℝ)*X 1 1+(212102451/500000000 : ℝ)*X 1 2+(4366375247/10000000000 : ℝ)*X 2 0+(4494356701/10000000000 : ℝ)*X 2 1+(212102451/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (45980747697928958987784177/13600000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (667593693/100000000000000 : ℝ)*(base19) + (124178697/20000000000000 : ℝ)*(base23) + (24960369/100000000000000 : ℝ)*(lower2) + (4604203/5000000000000 : ℝ)*(upper3) + (54761061/100000000000000 : ℝ)*(upper5) + (1177039894150689/20000000000000 : ℝ)*(major0) + (1177039894150689/20000000000000 : ℝ)*(major1) + (1177039894150689/20000000000000 : ℝ)*(major2) + (1956731146521149/25000000000000 : ℝ)*(sp0) + (7826941862739373/100000000000000 : ℝ)*(sp1) + (7826941909439581/100000000000000 : ℝ)*(sp2) + (1971723123641081/50000000000000 : ℝ)*(sp3) + (1794424847/10000000000000 : ℝ)*(sp4) + (10051193741/100000000000000 : ℝ)*(sp7) + (30808252331843/781250000000 : ℝ)*(f.failure) + (3913471265166533/50000000000000 : ℝ)*(f.sum) + (17918541337751/2720000000000000000000000000 : ℝ)*base65 + (128934629733006941/27200000000000000000000000000000 : ℝ)*base67 + (18019717359793059/27200000000000000000000000000000 : ℝ)*base70 + (232841968305393059/27200000000000000000000000000000 : ℝ)*base72 + (8631926966551/2720000000000000000000000000 : ℝ)*base73 + (829955686109006941/27200000000000000000000000000000 : ℝ)*base75 + (245709809486606941/27200000000000000000000000000000 : ℝ)*base77 + (117738424102606941/27200000000000000000000000000000 : ℝ)*base79 + (10913773810871/2720000000000000000000000000 : ℝ)*base81 + (636311/78125000000000000000 : ℝ)*base89 + (636311/78125000000000000000 : ℝ)*base91 + (636311/78125000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18618243425253332585803071/4000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (626713489/20000000000000 : ℝ)*(base15) + (428192131/100000000000000 : ℝ)*(upper2) + (1587310941/100000000000000 : ℝ)*(lower4) + (465092301/100000000000000 : ℝ)*(lower5) + (5914988851477601/100000000000000 : ℝ)*(major0) + (5914988851477601/100000000000000 : ℝ)*(major1) + (5914988851477601/100000000000000 : ℝ)*(major2) + (2636986851/12500000000000 : ℝ)*(sp1) + (16483391421/20000000000000 : ℝ)*(sp2) + (1548304397/6250000000000 : ℝ)*(sp3) + (983320059745893/12500000000000 : ℝ)*(sp4) + (1966634062126223/25000000000000 : ℝ)*(sp5) + (7866478061010039/100000000000000 : ℝ)*(sp6) + (792678459393133/20000000000000 : ℝ)*(sp7) + (3963417069836017/100000000000000 : ℝ)*(f.failure) + (983320059745893/12500000000000 : ℝ)*(f.sum) + (2176964040167/800000000000000000000000000 : ℝ)*base65 + (177062181609230643/8000000000000000000000000000000 : ℝ)*base68 + (86472203105230643/8000000000000000000000000000000 : ℝ)*base70 + (479756467033230643/8000000000000000000000000000000 : ℝ)*base72 + (5901361881433/800000000000000000000000000 : ℝ)*base74 + (13759089022769357/8000000000000000000000000000000 : ℝ)*base75 + (1056865606769357/8000000000000000000000000000000 : ℝ)*base77 + (42397458937230643/8000000000000000000000000000000 : ℝ)*base80 + (1261372654567/800000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (28245659/10000000000000000000000 : ℝ)*base89 + (28245659/10000000000000000000000 : ℝ)*base91 + (28245659/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1130_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149239627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (281/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1133/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11337/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14043/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1130_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1130_s8_0 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2172639637/10000000000 : ℝ)*x 0 + (5393209289/10000000000 : ℝ)*x 1 + (2632791611/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2172639637/10000000000 : ℝ)^8323 ≤ (1320071298829/10000000000000 : ℝ)^6275 := by
    have hnat : (2172639637 : ℕ)^8323*10000000000000^6275 ≤ 1320071298829^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172639637 10000000000 1320071298829 10000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393209289/10000000000 : ℝ)^8323 ≤ (44088879484309/100000000000000 : ℝ)^6275 := by
    have hnat : (5393209289 : ℕ)^8323*100000000000000^6275 ≤ 44088879484309^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393209289 10000000000 44088879484309 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632791611/5000000000 : ℝ)^8323 ≤ (42710407508893/100000000000000 : ℝ)^6275 := by
    have hnat : (2632791611 : ℕ)^8323*100000000000000^6275 ≤ 42710407508893^6275*5000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632791611 5000000000 42710407508893 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2172639637/10000000000 : ℝ), (5393209289/10000000000 : ℝ), (2632791611/5000000000 : ℝ)] ![(1320071298829/10000000000000 : ℝ), (44088879484309/100000000000000 : ℝ), (42710407508893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2172639637/10000000000 : ℝ)|^8323 ≤ (1320071298829/10000000000000 : ℝ)^6275
        have hw : |(-2172639637/10000000000 : ℝ)|=(2172639637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393209289/10000000000 : ℝ)|^8323 ≤ (44088879484309/100000000000000 : ℝ)^6275
        have hw : |(5393209289/10000000000 : ℝ)|=(5393209289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632791611/5000000000 : ℝ)|^8323 ≤ (42710407508893/100000000000000 : ℝ)^6275
        have hw : |(2632791611/5000000000 : ℝ)|=(2632791611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s8_1 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344791103/10000000000 : ℝ)*x 0 + (-1118688133/5000000000 : ℝ)*x 1 + (2632791601/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344791103/10000000000 : ℝ)^8323 ≤ (2178232680373/5000000000000 : ℝ)^6275 := by
    have hnat : (5344791103 : ℕ)^8323*5000000000000^6275 ≤ 2178232680373^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344791103 10000000000 2178232680373 5000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1118688133/5000000000 : ℝ)^8323 ≤ (6862469540677/50000000000000 : ℝ)^6275 := by
    have hnat : (1118688133 : ℕ)^8323*50000000000000^6275 ≤ 6862469540677^6275*5000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118688133 5000000000 6862469540677 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632791601/5000000000 : ℝ)^8323 ≤ (21355203646861/50000000000000 : ℝ)^6275 := by
    have hnat : (2632791601 : ℕ)^8323*50000000000000^6275 ≤ 21355203646861^6275*5000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632791601 5000000000 21355203646861 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344791103/10000000000 : ℝ), (-1118688133/5000000000 : ℝ), (2632791601/5000000000 : ℝ)] ![(2178232680373/5000000000000 : ℝ), (6862469540677/50000000000000 : ℝ), (21355203646861/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344791103/10000000000 : ℝ)|^8323 ≤ (2178232680373/5000000000000 : ℝ)^6275
        have hw : |(5344791103/10000000000 : ℝ)|=(5344791103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1118688133/5000000000 : ℝ)|^8323 ≤ (6862469540677/50000000000000 : ℝ)^6275
        have hw : |(-1118688133/5000000000 : ℝ)|=(1118688133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632791601/5000000000 : ℝ)|^8323 ≤ (21355203646861/50000000000000 : ℝ)^6275
        have hw : |(2632791601/5000000000 : ℝ)|=(2632791601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s8_2 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672395553/5000000000 : ℝ)*x 0 + (6581979/12500000 : ℝ)*x 1 + (-279672033/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672395553/5000000000 : ℝ)^8323 ≤ (43564653639893/100000000000000 : ℝ)^6275 := by
    have hnat : (2672395553 : ℕ)^8323*100000000000000^6275 ≤ 43564653639893^6275*5000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672395553 5000000000 43564653639893 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6581979/12500000 : ℝ)^8323 ≤ (8542081454441/20000000000000 : ℝ)^6275 := by
    have hnat : (6581979 : ℕ)^8323*20000000000000^6275 ≤ 8542081454441^6275*12500000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6581979 12500000 8542081454441 20000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (279672033/1250000000 : ℝ)^8323 ≤ (13724939065081/100000000000000 : ℝ)^6275 := by
    have hnat : (279672033 : ℕ)^8323*100000000000000^6275 ≤ 13724939065081^6275*1250000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279672033 1250000000 13724939065081 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672395553/5000000000 : ℝ), (6581979/12500000 : ℝ), (-279672033/1250000000 : ℝ)] ![(43564653639893/100000000000000 : ℝ), (8542081454441/20000000000000 : ℝ), (13724939065081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672395553/5000000000 : ℝ)|^8323 ≤ (43564653639893/100000000000000 : ℝ)^6275
        have hw : |(2672395553/5000000000 : ℝ)|=(2672395553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6581979/12500000 : ℝ)|^8323 ≤ (8542081454441/20000000000000 : ℝ)^6275
        have hw : |(6581979/12500000 : ℝ)|=(6581979/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-279672033/1250000000 : ℝ)|^8323 ≤ (13724939065081/100000000000000 : ℝ)^6275
        have hw : |(-279672033/1250000000 : ℝ)|=(279672033/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s8_3 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4366368387/10000000000 : ℝ)*x 0 + (13254831/31250000 : ℝ)*x 1 + (224742859/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4366368387/10000000000 : ℝ)^8323 ≤ (33316919560493/100000000000000 : ℝ)^6275 := by
    have hnat : (4366368387 : ℕ)^8323*100000000000000^6275 ≤ 33316919560493^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4366368387 10000000000 33316919560493 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13254831/31250000 : ℝ)^8323 ≤ (32059560224467/100000000000000 : ℝ)^6275 := by
    have hnat : (13254831 : ℕ)^8323*100000000000000^6275 ≤ 32059560224467^6275*31250000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13254831 31250000 32059560224467 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (224742859/500000000 : ℝ)^8323 ≤ (34623520197049/100000000000000 : ℝ)^6275 := by
    have hnat : (224742859 : ℕ)^8323*100000000000000^6275 ≤ 34623520197049^6275*500000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224742859 500000000 34623520197049 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4366368387/10000000000 : ℝ), (13254831/31250000 : ℝ), (224742859/500000000 : ℝ)] ![(33316919560493/100000000000000 : ℝ), (32059560224467/100000000000000 : ℝ), (34623520197049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4366368387/10000000000 : ℝ)|^8323 ≤ (33316919560493/100000000000000 : ℝ)^6275
        have hw : |(4366368387/10000000000 : ℝ)|=(4366368387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(13254831/31250000 : ℝ)|^8323 ≤ (32059560224467/100000000000000 : ℝ)^6275
        have hw : |(13254831/31250000 : ℝ)|=(13254831/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(224742859/500000000 : ℝ)|^8323 ≤ (34623520197049/100000000000000 : ℝ)^6275
        have hw : |(224742859/500000000 : ℝ)|=(224742859/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s8_4 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-43452891/200000000 : ℝ)*x 0 + (5265903537/10000000000 : ℝ)*x 1 + (539288781/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43452891/200000000 : ℝ)^8323 ≤ (13200752581689/100000000000000 : ℝ)^6275 := by
    have hnat : (43452891 : ℕ)^8323*100000000000000^6275 ≤ 13200752581689^6275*200000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43452891 200000000 13200752581689 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265903537/10000000000 : ℝ)^8323 ≤ (8542770733063/20000000000000 : ℝ)^6275 := by
    have hnat : (5265903537 : ℕ)^8323*20000000000000^6275 ≤ 8542770733063^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265903537 10000000000 8542770733063 20000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539288781/1000000000 : ℝ)^8323 ≤ (8817078746701/20000000000000 : ℝ)^6275 := by
    have hnat : (539288781 : ℕ)^8323*20000000000000^6275 ≤ 8817078746701^6275*1000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539288781 1000000000 8817078746701 20000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-43452891/200000000 : ℝ), (5265903537/10000000000 : ℝ), (539288781/1000000000 : ℝ)] ![(13200752581689/100000000000000 : ℝ), (8542770733063/20000000000000 : ℝ), (8817078746701/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-43452891/200000000 : ℝ)|^8323 ≤ (13200752581689/100000000000000 : ℝ)^6275
        have hw : |(-43452891/200000000 : ℝ)|=(43452891/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265903537/10000000000 : ℝ)|^8323 ≤ (8542770733063/20000000000000 : ℝ)^6275
        have hw : |(5265903537/10000000000 : ℝ)|=(5265903537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539288781/1000000000 : ℝ)|^8323 ≤ (8817078746701/20000000000000 : ℝ)^6275
        have hw : |(539288781/1000000000 : ℝ)|=(539288781/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s8_5 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656242641/5000000000 : ℝ)*x 0 + (-1055035833/5000000000 : ℝ)*x 1 + (5392887809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656242641/5000000000 : ℝ)^8323 ≤ (43215737266113/100000000000000 : ℝ)^6275 := by
    have hnat : (2656242641 : ℕ)^8323*100000000000000^6275 ≤ 43215737266113^6275*5000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656242641 5000000000 43215737266113 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1055035833/5000000000 : ℝ)^8323 ≤ (6349434497057/50000000000000 : ℝ)^6275 := by
    have hnat : (1055035833 : ℕ)^8323*50000000000000^6275 ≤ 6349434497057^6275*5000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055035833 5000000000 6349434497057 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392887809/10000000000 : ℝ)^8323 ≤ (22042696861331/50000000000000 : ℝ)^6275 := by
    have hnat : (5392887809 : ℕ)^8323*50000000000000^6275 ≤ 22042696861331^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392887809 10000000000 22042696861331 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656242641/5000000000 : ℝ), (-1055035833/5000000000 : ℝ), (5392887809/10000000000 : ℝ)] ![(43215737266113/100000000000000 : ℝ), (6349434497057/50000000000000 : ℝ), (22042696861331/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656242641/5000000000 : ℝ)|^8323 ≤ (43215737266113/100000000000000 : ℝ)^6275
        have hw : |(2656242641/5000000000 : ℝ)|=(2656242641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1055035833/5000000000 : ℝ)|^8323 ≤ (6349434497057/50000000000000 : ℝ)^6275
        have hw : |(-1055035833/5000000000 : ℝ)|=(1055035833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392887809/10000000000 : ℝ)|^8323 ≤ (22042696861331/50000000000000 : ℝ)^6275
        have hw : |(5392887809/10000000000 : ℝ)|=(5392887809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s8_6 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656242641/5000000000 : ℝ)*x 0 + (5392887809/10000000000 : ℝ)*x 1 + (-1055035833/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656242641/5000000000 : ℝ)^8323 ≤ (43215737266113/100000000000000 : ℝ)^6275 := by
    have hnat : (2656242641 : ℕ)^8323*100000000000000^6275 ≤ 43215737266113^6275*5000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656242641 5000000000 43215737266113 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392887809/10000000000 : ℝ)^8323 ≤ (22042696861331/50000000000000 : ℝ)^6275 := by
    have hnat : (5392887809 : ℕ)^8323*50000000000000^6275 ≤ 22042696861331^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392887809 10000000000 22042696861331 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1055035833/5000000000 : ℝ)^8323 ≤ (6349434497057/50000000000000 : ℝ)^6275 := by
    have hnat : (1055035833 : ℕ)^8323*50000000000000^6275 ≤ 6349434497057^6275*5000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055035833 5000000000 6349434497057 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656242641/5000000000 : ℝ), (5392887809/10000000000 : ℝ), (-1055035833/5000000000 : ℝ)] ![(43215737266113/100000000000000 : ℝ), (22042696861331/50000000000000 : ℝ), (6349434497057/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656242641/5000000000 : ℝ)|^8323 ≤ (43215737266113/100000000000000 : ℝ)^6275
        have hw : |(2656242641/5000000000 : ℝ)|=(2656242641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392887809/10000000000 : ℝ)|^8323 ≤ (22042696861331/50000000000000 : ℝ)^6275
        have hw : |(5392887809/10000000000 : ℝ)|=(5392887809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1055035833/5000000000 : ℝ)|^8323 ≤ (6349434497057/50000000000000 : ℝ)^6275
        have hw : |(-1055035833/5000000000 : ℝ)|=(1055035833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s8_7 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4366378157/10000000000 : ℝ)*x 0 + (1123555349/2500000000 : ℝ)*x 1 + (2121091981/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4366378157/10000000000 : ℝ)^8323 ≤ (33317018439787/100000000000000 : ℝ)^6275 := by
    have hnat : (4366378157 : ℕ)^8323*100000000000000^6275 ≤ 33317018439787^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4366378157 10000000000 33317018439787 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1123555349/2500000000 : ℝ)^8323 ≤ (17308512285179/50000000000000 : ℝ)^6275 := by
    have hnat : (1123555349 : ℕ)^8323*50000000000000^6275 ≤ 17308512285179^6275*2500000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123555349 2500000000 17308512285179 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2121091981/5000000000 : ℝ)^8323 ≤ (1282638279039/4000000000000 : ℝ)^6275 := by
    have hnat : (2121091981 : ℕ)^8323*4000000000000^6275 ≤ 1282638279039^6275*5000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121091981 5000000000 1282638279039 4000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4366378157/10000000000 : ℝ), (1123555349/2500000000 : ℝ), (2121091981/5000000000 : ℝ)] ![(33317018439787/100000000000000 : ℝ), (17308512285179/50000000000000 : ℝ), (1282638279039/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4366378157/10000000000 : ℝ)|^8323 ≤ (33317018439787/100000000000000 : ℝ)^6275
        have hw : |(4366378157/10000000000 : ℝ)|=(4366378157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1123555349/2500000000 : ℝ)|^8323 ≤ (17308512285179/50000000000000 : ℝ)^6275
        have hw : |(1123555349/2500000000 : ℝ)|=(1123555349/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2121091981/5000000000 : ℝ)|^8323 ≤ (1282638279039/4000000000000 : ℝ)^6275
        have hw : |(2121091981/5000000000 : ℝ)|=(2121091981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1130_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149239627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14043/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11337/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5669/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7021/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14043/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11337/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14043/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11337/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14043/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11337/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14043/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11337/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14043/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11337/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14043/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11337/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11337/100000 : ℝ) ^ (4161/1024 : ℝ) ≤ (14387170124659263/100000000000000000000 : ℝ) := by
    have hpowers : (11337/100000 : ℝ)^4161 ≤ (14387170124659263/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11337 : ℕ)^4161*100000000000000000000^1024 ≤ 14387170124659263^1024*100000^4161 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11337 100000 14387170124659263 100000000000000000000 4161 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11337/100000 : ℝ)) (X := (14387170124659263/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14043/100000 : ℝ) ^ (4161/1024 : ℝ) ≤ (34333910300291833/100000000000000000000 : ℝ) := by
    have hpowers : (14043/100000 : ℝ)^4161 ≤ (34333910300291833/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14043 : ℕ)^4161*100000000000000000000^1024 ≤ 34333910300291833^1024*100000^4161 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14043 100000 34333910300291833 100000000000000000000 4161 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14043/100000 : ℝ)) (X := (34333910300291833/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014387170124659263/50000000000000000000 : ℝ) ≤ (5000354022218469/5000000000000000 : ℝ) ^ (4161/1024 : ℝ) := by
    have hpowers : (50014387170124659263/50000000000000000000 : ℝ)^1024 ≤ (5000354022218469/5000000000000000 : ℝ)^4161 := by
      have hnat : (50014387170124659263 : ℕ)^1024*5000000000000000^4161 ≤ 5000354022218469^4161*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014387170124659263 50000000000000000000 5000354022218469 5000000000000000 1024 4161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000354022218469/5000000000000000 : ℝ)) (X := (50014387170124659263/50000000000000000000 : ℝ)) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506090135053118887/12500000000000000000 : ℝ) ≤ (1000119877977229/1000000000000000 : ℝ) ^ (4161/1024 : ℝ) := by
    have hpowers : (12506090135053118887/12500000000000000000 : ℝ)^1024 ≤ (1000119877977229/1000000000000000 : ℝ)^4161 := by
      have hnat : (12506090135053118887 : ℕ)^1024*1000000000000000^4161 ≤ 1000119877977229^4161*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506090135053118887 12500000000000000000 1000119877977229 1000000000000000 1024 4161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000119877977229/1000000000000000 : ℝ)) (X := (12506090135053118887/12500000000000000000 : ℝ)) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034333910300291833/50000000000000000000 : ℝ) ≤ (5000844757553821/5000000000000000 : ℝ) ^ (4161/1024 : ℝ) := by
    have hpowers : (50034333910300291833/50000000000000000000 : ℝ)^1024 ≤ (5000844757553821/5000000000000000 : ℝ)^4161 := by
      have hnat : (50034333910300291833 : ℕ)^1024*5000000000000000^4161 ≤ 5000844757553821^4161*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034333910300291833 50000000000000000000 5000844757553821 5000000000000000 1024 4161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000844757553821/5000000000000000 : ℝ)) (X := (50034333910300291833/50000000000000000000 : ℝ)) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14387170124659263/100000000000000000000 : ℝ) ≤ ((450846483920876383/451000000000000000 : ℝ)+2*(61341916919/33825000000000 : ℝ)*(11337/100000 : ℝ))^(4161/1024 : ℝ) := by
    rw [show (450846483920876383/451000000000000000 : ℝ)+2*(61341916919/33825000000000 : ℝ)*(11337/100000 : ℝ)=(5000354022218469/5000000000000000 : ℝ) by norm_num, show 1+2*(14387170124659263/100000000000000000000 : ℝ)=(50014387170124659263/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34333910300291833/100000000000000000000 : ℝ)+(14387170124659263/100000000000000000000 : ℝ) ≤ ((450846483920876383/451000000000000000 : ℝ)+(61341916919/33825000000000 : ℝ)*((14043/100000 : ℝ)+(11337/100000 : ℝ)))^(4161/1024 : ℝ) := by
    rw [show (450846483920876383/451000000000000000 : ℝ)+(61341916919/33825000000000 : ℝ)*((14043/100000 : ℝ)+(11337/100000 : ℝ))=(1000119877977229/1000000000000000 : ℝ) by norm_num, show 1+(34333910300291833/100000000000000000000 : ℝ)+(14387170124659263/100000000000000000000 : ℝ)=(12506090135053118887/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34333910300291833/100000000000000000000 : ℝ) ≤ ((450846483920876383/451000000000000000 : ℝ)+2*(61341916919/33825000000000 : ℝ)*(14043/100000 : ℝ))^(4161/1024 : ℝ) := by
    rw [show (450846483920876383/451000000000000000 : ℝ)+2*(61341916919/33825000000000 : ℝ)*(14043/100000 : ℝ)=(5000844757553821/5000000000000000 : ℝ) by norm_num, show 1+2*(34333910300291833/100000000000000000000 : ℝ)=(50034333910300291833/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (450846483920876383/451000000000000000 : ℝ)*(X 1 0+X 2 0)+(61341916919/33825000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4161/1024 : ℝ)) (lo := (11337/100000 : ℝ)) (hi := (14043/100000 : ℝ)) (c := (450846483920876383/451000000000000000 : ℝ)) (alpha := (61341916919/33825000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (450846483920876383/451000000000000000 : ℝ)*(X 0 1+X 2 1)+(61341916919/33825000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4161/1024 : ℝ)) (lo := (11337/100000 : ℝ)) (hi := (14043/100000 : ℝ)) (c := (450846483920876383/451000000000000000 : ℝ)) (alpha := (61341916919/33825000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (450846483920876383/451000000000000000 : ℝ)*(X 0 2+X 1 2)+(61341916919/33825000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4161/1024 : ℝ)) (lo := (11337/100000 : ℝ)) (hi := (14043/100000 : ℝ)) (c := (450846483920876383/451000000000000000 : ℝ)) (alpha := (61341916919/33825000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2172639637/10000000000 : ℝ)*X 0 0+(5393209289/10000000000 : ℝ)*X 0 1+(2632791611/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344791103/10000000000 : ℝ)*X 1 0+(-1118688133/5000000000 : ℝ)*X 1 1+(2632791601/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672395553/5000000000 : ℝ)*X 2 0+(6581979/12500000 : ℝ)*X 2 1+(-279672033/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4366368387/10000000000 : ℝ)*X 0 0+(13254831/31250000 : ℝ)*X 0 1+(224742859/500000000 : ℝ)*X 0 2+(4366368387/10000000000 : ℝ)*X 1 0+(13254831/31250000 : ℝ)*X 1 1+(224742859/500000000 : ℝ)*X 1 2+(4366368387/10000000000 : ℝ)*X 2 0+(13254831/31250000 : ℝ)*X 2 1+(224742859/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-43452891/200000000 : ℝ)*X 0 0+(5265903537/10000000000 : ℝ)*X 0 1+(539288781/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656242641/5000000000 : ℝ)*X 1 0+(-1055035833/5000000000 : ℝ)*X 1 1+(5392887809/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656242641/5000000000 : ℝ)*X 2 0+(5392887809/10000000000 : ℝ)*X 2 1+(-1055035833/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4366378157/10000000000 : ℝ)*X 0 0+(1123555349/2500000000 : ℝ)*X 0 1+(2121091981/5000000000 : ℝ)*X 0 2+(4366378157/10000000000 : ℝ)*X 1 0+(1123555349/2500000000 : ℝ)*X 1 1+(2121091981/5000000000 : ℝ)*X 1 2+(4366378157/10000000000 : ℝ)*X 2 0+(1123555349/2500000000 : ℝ)*X 2 1+(2121091981/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10539405697808060093736519/1409375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (363037633/25000000000000 : ℝ)*(base19) + (683483097/50000000000000 : ℝ)*(base23) + (47879891/100000000000000 : ℝ)*(lower2) + (21417751/12500000000000 : ℝ)*(upper3) + (54282859/50000000000000 : ℝ)*(upper5) + (736451438427869/12500000000000 : ℝ)*(major0) + (736451438427869/12500000000000 : ℝ)*(major1) + (736451438427869/12500000000000 : ℝ)*(major2) + (1958857670426089/25000000000000 : ℝ)*(sp0) + (7835468544369267/100000000000000 : ℝ)*(sp1) + (3917734314776803/50000000000000 : ℝ)*(sp2) + (493466454158659/12500000000000 : ℝ)*(sp3) + (39314815443/100000000000000 : ℝ)*(sp4) + (5283946951/25000000000000 : ℝ)*(sp7) + (986938192264269/25000000000000 : ℝ)*(f.failure) + (7835469996519799/100000000000000 : ℝ)*(f.sum) + (17803218160501/3382500000000000000000000000 : ℝ)*base65 + (687086348712341/412500000000000000000000000000 : ℝ)*base67 + (6261311101924841/412500000000000000000000000000 : ℝ)*base69 + (3320765366187341/412500000000000000000000000000 : ℝ)*base71 + (5871070263989/3382500000000000000000000000 : ℝ)*base74 + (2248557272224841/412500000000000000000000000000 : ℝ)*base75 + (6170811712999841/412500000000000000000000000000 : ℝ)*base77 + (6872444101600159/412500000000000000000000000000 : ℝ)*base80 + (4902700321399/845625000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (9012337/2500000000000000000000 : ℝ)*base90 + (9012337/2500000000000000000000 : ℝ)*base92 + (9012337/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24985368781519773116021/2255000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2030010363/100000000000000 : ℝ)*(base19) + (2208504681/100000000000000 : ℝ)*(base23) + (22278171/3125000000000 : ℝ)*(lower1) + (221559577/100000000000000 : ℝ)*(upper3) + (81357803/100000000000000 : ℝ)*(lower4) + (28354847/12500000000000 : ℝ)*(upper5) + (2960642191745647/50000000000000 : ℝ)*(major0) + (2960642191745647/50000000000000 : ℝ)*(major1) + (2960642191745647/50000000000000 : ℝ)*(major2) + (1042151497/25000000000000 : ℝ)*(sp2) + (1574986584545801/20000000000000 : ℝ)*(sp4) + (3937465446359321/50000000000000 : ℝ)*(sp5) + (1574985309123667/20000000000000 : ℝ)*(sp6) + (158705418996827/4000000000000 : ℝ)*(sp7) + (158705418996827/4000000000000 : ℝ)*(f.failure) + (1574986584545801/20000000000000 : ℝ)*(f.sum) + (28809236595619/6765000000000000000000000000 : ℝ)*base65 + (155455242531108917/1650000000000000000000000000000 : ℝ)*base68 + (6738453284141083/1650000000000000000000000000000 : ℝ)*base69 + (241086068087208917/1650000000000000000000000000000 : ℝ)*base72 + (106772864239/422812500000000000000000000 : ℝ)*base73 + (105974542157058917/1650000000000000000000000000000 : ℝ)*base76 + (24950756008691083/1650000000000000000000000000000 : ℝ)*base77 + (19612085734391083/1650000000000000000000000000000 : ℝ)*base79 + (5926186191547/845625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (336471/400000000000000000000 : ℝ)*base90 + (336471/400000000000000000000 : ℝ)*base92 + (336471/400000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1130_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149239627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14043/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11337/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5669/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7021/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1130_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1130_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149239627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3521/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11297/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5669/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7021/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1130_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1130_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1130_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149239627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3521/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11297/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5669/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7021/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1130_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

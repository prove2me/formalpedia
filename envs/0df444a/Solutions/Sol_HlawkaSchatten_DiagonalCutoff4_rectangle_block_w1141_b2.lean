-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1141_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:31:43.595133+00:00
-- url     : https://prove2.me/submissions/88618512-e195-4891-9890-ff4a09257f1c

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
theorem support_rectangle_w1141_s6_0 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-54183363/250000000 : ℝ)*x 0 + (337087373/625000000 : ℝ)*x 1 + (1053079387/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (54183363/250000000 : ℝ)^4167 ≤ (13169472583983/100000000000000 : ℝ)^3143 := by
    have hnat : (54183363 : ℕ)^4167*100000000000000^3143 ≤ 13169472583983^3143*250000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54183363 250000000 13169472583983 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337087373/625000000 : ℝ)^4167 ≤ (5513309431329/12500000000000 : ℝ)^3143 := by
    have hnat : (337087373 : ℕ)^4167*12500000000000^3143 ≤ 5513309431329^3143*625000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337087373 625000000 5513309431329 12500000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053079387/2000000000 : ℝ)^4167 ≤ (2670253247001/6250000000000 : ℝ)^3143 := by
    have hnat : (1053079387 : ℕ)^4167*6250000000000^3143 ≤ 2670253247001^3143*2000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053079387 2000000000 2670253247001 6250000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-54183363/250000000 : ℝ), (337087373/625000000 : ℝ), (1053079387/2000000000 : ℝ)] ![(13169472583983/100000000000000 : ℝ), (5513309431329/12500000000000 : ℝ), (2670253247001/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-54183363/250000000 : ℝ)|^4167 ≤ (13169472583983/100000000000000 : ℝ)^3143
        have hw : |(-54183363/250000000 : ℝ)|=(54183363/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337087373/625000000 : ℝ)|^4167 ≤ (5513309431329/12500000000000 : ℝ)^3143
        have hw : |(337087373/625000000 : ℝ)|=(337087373/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053079387/2000000000 : ℝ)|^4167 ≤ (2670253247001/6250000000000 : ℝ)^3143
        have hw : |(1053079387/2000000000 : ℝ)|=(1053079387/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s6_1 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344848659/10000000000 : ℝ)*x 0 + (-558065989/2500000000 : ℝ)*x 1 + (2632698467/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344848659/10000000000 : ℝ)^4167 ≤ (21790432823373/50000000000000 : ℝ)^3143 := by
    have hnat : (5344848659 : ℕ)^4167*50000000000000^3143 ≤ 21790432823373^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344848659 10000000000 21790432823373 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (558065989/2500000000 : ℝ)^4167 ≤ (2739016479643/20000000000000 : ℝ)^3143 := by
    have hnat : (558065989 : ℕ)^4167*20000000000000^3143 ≤ 2739016479643^3143*2500000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      558065989 2500000000 2739016479643 20000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632698467/5000000000 : ℝ)^4167 ≤ (42724051941259/100000000000000 : ℝ)^3143 := by
    have hnat : (2632698467 : ℕ)^4167*100000000000000^3143 ≤ 42724051941259^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632698467 5000000000 42724051941259 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344848659/10000000000 : ℝ), (-558065989/2500000000 : ℝ), (2632698467/5000000000 : ℝ)] ![(21790432823373/50000000000000 : ℝ), (2739016479643/20000000000000 : ℝ), (42724051941259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344848659/10000000000 : ℝ)|^4167 ≤ (21790432823373/50000000000000 : ℝ)^3143
        have hw : |(5344848659/10000000000 : ℝ)|=(5344848659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-558065989/2500000000 : ℝ)|^4167 ≤ (2739016479643/20000000000000 : ℝ)^3143
        have hw : |(-558065989/2500000000 : ℝ)|=(558065989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632698467/5000000000 : ℝ)|^4167 ≤ (42724051941259/100000000000000 : ℝ)^3143
        have hw : |(2632698467/5000000000 : ℝ)|=(2632698467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s6_2 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336212161/2500000000 : ℝ)*x 0 + (2632698473/5000000000 : ℝ)*x 1 + (-55806599/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336212161/2500000000 : ℝ)^4167 ≤ (43580865484591/100000000000000 : ℝ)^3143 := by
    have hnat : (1336212161 : ℕ)^4167*100000000000000^3143 ≤ 43580865484591^3143*2500000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336212161 2500000000 43580865484591 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632698473/5000000000 : ℝ)^4167 ≤ (42724052070351/100000000000000 : ℝ)^3143 := by
    have hnat : (2632698473 : ℕ)^4167*100000000000000^3143 ≤ 42724052070351^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632698473 5000000000 42724052070351 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (55806599/250000000 : ℝ)^4167 ≤ (54780329723/400000000000 : ℝ)^3143 := by
    have hnat : (55806599 : ℕ)^4167*400000000000^3143 ≤ 54780329723^3143*250000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55806599 250000000 54780329723 400000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336212161/2500000000 : ℝ), (2632698473/5000000000 : ℝ), (-55806599/250000000 : ℝ)] ![(43580865484591/100000000000000 : ℝ), (42724052070351/100000000000000 : ℝ), (54780329723/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336212161/2500000000 : ℝ)|^4167 ≤ (43580865484591/100000000000000 : ℝ)^3143
        have hw : |(1336212161/2500000000 : ℝ)|=(1336212161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632698473/5000000000 : ℝ)|^4167 ≤ (42724052070351/100000000000000 : ℝ)^3143
        have hw : |(2632698473/5000000000 : ℝ)|=(2632698473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-55806599/250000000 : ℝ)|^4167 ≤ (54780329723/400000000000 : ℝ)^3143
        have hw : |(-55806599/250000000 : ℝ)|=(55806599/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s6_3 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (872959379/2000000000 : ℝ)*x 0 + (4239342229/10000000000 : ℝ)*x 1 + (2246973509/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (872959379/2000000000 : ℝ)^4167 ≤ (16658393394927/50000000000000 : ℝ)^3143 := by
    have hnat : (872959379 : ℕ)^4167*50000000000000^3143 ≤ 16658393394927^3143*2000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872959379 2000000000 16658393394927 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4239342229/10000000000 : ℝ)^4167 ≤ (16026587850523/50000000000000 : ℝ)^3143 := by
    have hnat : (4239342229 : ℕ)^4167*50000000000000^3143 ≤ 16026587850523^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4239342229 10000000000 16026587850523 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2246973509/5000000000 : ℝ)^4167 ≤ (34630037500301/100000000000000 : ℝ)^3143 := by
    have hnat : (2246973509 : ℕ)^4167*100000000000000^3143 ≤ 34630037500301^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246973509 5000000000 34630037500301 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(872959379/2000000000 : ℝ), (4239342229/10000000000 : ℝ), (2246973509/5000000000 : ℝ)] ![(16658393394927/50000000000000 : ℝ), (16026587850523/50000000000000 : ℝ), (34630037500301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(872959379/2000000000 : ℝ)|^4167 ≤ (16658393394927/50000000000000 : ℝ)^3143
        have hw : |(872959379/2000000000 : ℝ)|=(872959379/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4239342229/10000000000 : ℝ)|^4167 ≤ (16026587850523/50000000000000 : ℝ)^3143
        have hw : |(4239342229/10000000000 : ℝ)|=(4239342229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2246973509/5000000000 : ℝ)|^4167 ≤ (34630037500301/100000000000000 : ℝ)^3143
        have hw : |(2246973509/5000000000 : ℝ)|=(2246973509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s6_4 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-216733949/1000000000 : ℝ)*x 0 + (5265720219/10000000000 : ℝ)*x 1 + (168533547/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216733949/1000000000 : ℝ)^4167 ≤ (823094538907/6250000000000 : ℝ)^3143 := by
    have hnat : (216733949 : ℕ)^4167*6250000000000^3143 ≤ 823094538907^3143*1000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216733949 1000000000 823094538907 6250000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265720219/10000000000 : ℝ)^4167 ≤ (10681882446791/25000000000000 : ℝ)^3143 := by
    have hnat : (5265720219 : ℕ)^4167*25000000000000^3143 ≤ 10681882446791^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265720219 10000000000 10681882446791 25000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168533547/312500000 : ℝ)^4167 ≤ (22051478784313/50000000000000 : ℝ)^3143 := by
    have hnat : (168533547 : ℕ)^4167*50000000000000^3143 ≤ 22051478784313^3143*312500000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168533547 312500000 22051478784313 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-216733949/1000000000 : ℝ), (5265720219/10000000000 : ℝ), (168533547/312500000 : ℝ)] ![(823094538907/6250000000000 : ℝ), (10681882446791/25000000000000 : ℝ), (22051478784313/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-216733949/1000000000 : ℝ)|^4167 ≤ (823094538907/6250000000000 : ℝ)^3143
        have hw : |(-216733949/1000000000 : ℝ)|=(216733949/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265720219/10000000000 : ℝ)|^4167 ≤ (10681882446791/25000000000000 : ℝ)^3143
        have hw : |(5265720219/10000000000 : ℝ)|=(5265720219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(168533547/312500000 : ℝ)|^4167 ≤ (22051478784313/50000000000000 : ℝ)^3143
        have hw : |(168533547/312500000 : ℝ)|=(168533547/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s6_5 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656210723/5000000000 : ℝ)*x 0 + (-1052293707/5000000000 : ℝ)*x 1 + (5393073507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656210723/5000000000 : ℝ)^4167 ≤ (21615331606503/50000000000000 : ℝ)^3143 := by
    have hnat : (2656210723 : ℕ)^4167*50000000000000^3143 ≤ 21615331606503^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656210723 5000000000 21615331606503 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052293707/5000000000 : ℝ)^4167 ≤ (12666379173017/100000000000000 : ℝ)^3143 := by
    have hnat : (1052293707 : ℕ)^4167*100000000000000^3143 ≤ 12666379173017^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052293707 5000000000 12666379173017 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393073507/10000000000 : ℝ)^4167 ≤ (344554356259/781250000000 : ℝ)^3143 := by
    have hnat : (5393073507 : ℕ)^4167*781250000000^3143 ≤ 344554356259^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393073507 10000000000 344554356259 781250000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656210723/5000000000 : ℝ), (-1052293707/5000000000 : ℝ), (5393073507/10000000000 : ℝ)] ![(21615331606503/50000000000000 : ℝ), (12666379173017/100000000000000 : ℝ), (344554356259/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656210723/5000000000 : ℝ)|^4167 ≤ (21615331606503/50000000000000 : ℝ)^3143
        have hw : |(2656210723/5000000000 : ℝ)|=(2656210723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1052293707/5000000000 : ℝ)|^4167 ≤ (12666379173017/100000000000000 : ℝ)^3143
        have hw : |(-1052293707/5000000000 : ℝ)|=(1052293707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393073507/10000000000 : ℝ)|^4167 ≤ (344554356259/781250000000 : ℝ)^3143
        have hw : |(5393073507/10000000000 : ℝ)|=(5393073507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s6_6 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1328105361/2500000000 : ℝ)*x 0 + (2696536759/5000000000 : ℝ)*x 1 + (-1052293701/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328105361/2500000000 : ℝ)^4167 ≤ (10807665797857/25000000000000 : ℝ)^3143 := by
    have hnat : (1328105361 : ℕ)^4167*25000000000000^3143 ≤ 10807665797857^3143*2500000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328105361 2500000000 10807665797857 25000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696536759/5000000000 : ℝ)^4167 ≤ (8820591544083/20000000000000 : ℝ)^3143 := by
    have hnat : (2696536759 : ℕ)^4167*20000000000000^3143 ≤ 8820591544083^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696536759 5000000000 8820591544083 20000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052293701/5000000000 : ℝ)^4167 ≤ (2533275815453/20000000000000 : ℝ)^3143 := by
    have hnat : (1052293701 : ℕ)^4167*20000000000000^3143 ≤ 2533275815453^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052293701 5000000000 2533275815453 20000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328105361/2500000000 : ℝ), (2696536759/5000000000 : ℝ), (-1052293701/5000000000 : ℝ)] ![(10807665797857/25000000000000 : ℝ), (8820591544083/20000000000000 : ℝ), (2533275815453/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328105361/2500000000 : ℝ)|^4167 ≤ (10807665797857/25000000000000 : ℝ)^3143
        have hw : |(1328105361/2500000000 : ℝ)|=(1328105361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696536759/5000000000 : ℝ)|^4167 ≤ (8820591544083/20000000000000 : ℝ)^3143
        have hw : |(2696536759/5000000000 : ℝ)|=(2696536759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1052293701/5000000000 : ℝ)|^4167 ≤ (2533275815453/20000000000000 : ℝ)^3143
        have hw : |(-1052293701/5000000000 : ℝ)|=(1052293701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s6_7 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4364806767/10000000000 : ℝ)*x 0 + (2246651989/5000000000 : ℝ)*x 1 + (4239987607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364806767/10000000000 : ℝ)^4167 ≤ (8329221673499/25000000000000 : ℝ)^3143 := by
    have hnat : (4364806767 : ℕ)^4167*25000000000000^3143 ≤ 8329221673499^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364806767 10000000000 8329221673499 25000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2246651989/5000000000 : ℝ)^4167 ≤ (34623468005119/100000000000000 : ℝ)^3143 := by
    have hnat : (2246651989 : ℕ)^4167*100000000000000^3143 ≤ 34623468005119^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246651989 5000000000 34623468005119 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4239987607/10000000000 : ℝ)^4167 ≤ (32059645289171/100000000000000 : ℝ)^3143 := by
    have hnat : (4239987607 : ℕ)^4167*100000000000000^3143 ≤ 32059645289171^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4239987607 10000000000 32059645289171 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364806767/10000000000 : ℝ), (2246651989/5000000000 : ℝ), (4239987607/10000000000 : ℝ)] ![(8329221673499/25000000000000 : ℝ), (34623468005119/100000000000000 : ℝ), (32059645289171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364806767/10000000000 : ℝ)|^4167 ≤ (8329221673499/25000000000000 : ℝ)^3143
        have hw : |(4364806767/10000000000 : ℝ)|=(4364806767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2246651989/5000000000 : ℝ)|^4167 ≤ (34623468005119/100000000000000 : ℝ)^3143
        have hw : |(2246651989/5000000000 : ℝ)|=(2246651989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4239987607/10000000000 : ℝ)|^4167 ≤ (32059645289171/100000000000000 : ℝ)^3143
        have hw : |(4239987607/10000000000 : ℝ)|=(4239987607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1141_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149454197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1761/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5657/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2269/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1757/12500 : ℝ)*pair X 0 0 := by
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
  have lower0 : (5657/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1761/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5657/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1761/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5657/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1761/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5657/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1761/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5657/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1761/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5657/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5657/50000 : ℝ) ^ (8333/2048 : ℝ) ≤ (7051449397021217/50000000000000000000 : ℝ) := by
    have hpowers : (5657/50000 : ℝ)^8333 ≤ (7051449397021217/50000000000000000000 : ℝ)^2048 := by
      have hnat : (5657 : ℕ)^8333*50000000000000000000^2048 ≤ 7051449397021217^2048*50000^8333 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5657 50000 7051449397021217 50000000000000000000 8333 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5657/50000 : ℝ)) (X := (7051449397021217/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1761/12500 : ℝ) ^ (8333/2048 : ℝ) ≤ (1376758084240839/4000000000000000000 : ℝ) := by
    have hpowers : (1761/12500 : ℝ)^8333 ≤ (1376758084240839/4000000000000000000 : ℝ)^2048 := by
      have hnat : (1761 : ℕ)^8333*4000000000000000000^2048 ≤ 1376758084240839^2048*12500^8333 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1761 12500 1376758084240839 4000000000000000000 8333 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1761/12500 : ℝ)) (X := (1376758084240839/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007051449397021217/25000000000000000000 : ℝ) ≤ (10000693139686277/10000000000000000 : ℝ) ^ (8333/2048 : ℝ) := by
    have hpowers : (25007051449397021217/25000000000000000000 : ℝ)^2048 ≤ (10000693139686277/10000000000000000 : ℝ)^8333 := by
      have hnat : (25007051449397021217 : ℕ)^2048*10000000000000000^8333 ≤ 10000693139686277^8333*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007051449397021217 25000000000000000000 10000693139686277 10000000000000000 2048 8333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000693139686277/10000000000000000 : ℝ)) (X := (25007051449397021217/25000000000000000000 : ℝ)) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048521850900063409/100000000000000000000 : ℝ) ≤ (10001192302559163/10000000000000000 : ℝ) ^ (8333/2048 : ℝ) := by
    have hpowers : (100048521850900063409/100000000000000000000 : ℝ)^2048 ≤ (10001192302559163/10000000000000000 : ℝ)^8333 := by
      have hnat : (100048521850900063409 : ℕ)^2048*10000000000000000^8333 ≤ 10001192302559163^8333*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048521850900063409 100000000000000000000 10001192302559163 10000000000000000 2048 8333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001192302559163/10000000000000000 : ℝ)) (X := (100048521850900063409/100000000000000000000 : ℝ)) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001376758084240839/2000000000000000000 : ℝ) ≤ (10001691465432049/10000000000000000 : ℝ) ^ (8333/2048 : ℝ) := by
    have hpowers : (2001376758084240839/2000000000000000000 : ℝ)^2048 ≤ (10001691465432049/10000000000000000 : ℝ)^8333 := by
      have hnat : (2001376758084240839 : ℕ)^2048*10000000000000000^8333 ≤ 10001691465432049^8333*2000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001376758084240839 2000000000000000000 10001691465432049 10000000000000000 2048 8333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001691465432049/10000000000000000 : ℝ)) (X := (2001376758084240839/2000000000000000000 : ℝ)) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7051449397021217/50000000000000000000 : ℝ) ≤ ((2773062771200206799/2774000000000000000 : ℝ)+2*(249581436443/138700000000000 : ℝ)*(5657/50000 : ℝ))^(8333/2048 : ℝ) := by
    rw [show (2773062771200206799/2774000000000000000 : ℝ)+2*(249581436443/138700000000000 : ℝ)*(5657/50000 : ℝ)=(10000693139686277/10000000000000000 : ℝ) by norm_num, show 1+2*(7051449397021217/50000000000000000000 : ℝ)=(25007051449397021217/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1376758084240839/4000000000000000000 : ℝ)+(7051449397021217/50000000000000000000 : ℝ) ≤ ((2773062771200206799/2774000000000000000 : ℝ)+(249581436443/138700000000000 : ℝ)*((1761/12500 : ℝ)+(5657/50000 : ℝ)))^(8333/2048 : ℝ) := by
    rw [show (2773062771200206799/2774000000000000000 : ℝ)+(249581436443/138700000000000 : ℝ)*((1761/12500 : ℝ)+(5657/50000 : ℝ))=(10001192302559163/10000000000000000 : ℝ) by norm_num, show 1+(1376758084240839/4000000000000000000 : ℝ)+(7051449397021217/50000000000000000000 : ℝ)=(100048521850900063409/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1376758084240839/4000000000000000000 : ℝ) ≤ ((2773062771200206799/2774000000000000000 : ℝ)+2*(249581436443/138700000000000 : ℝ)*(1761/12500 : ℝ))^(8333/2048 : ℝ) := by
    rw [show (2773062771200206799/2774000000000000000 : ℝ)+2*(249581436443/138700000000000 : ℝ)*(1761/12500 : ℝ)=(10001691465432049/10000000000000000 : ℝ) by norm_num, show 1+2*(1376758084240839/4000000000000000000 : ℝ)=(2001376758084240839/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2773062771200206799/2774000000000000000 : ℝ)*(X 1 0+X 2 0)+(249581436443/138700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8333/2048 : ℝ)) (lo := (5657/50000 : ℝ)) (hi := (1761/12500 : ℝ)) (c := (2773062771200206799/2774000000000000000 : ℝ)) (alpha := (249581436443/138700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2773062771200206799/2774000000000000000 : ℝ)*(X 0 1+X 2 1)+(249581436443/138700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8333/2048 : ℝ)) (lo := (5657/50000 : ℝ)) (hi := (1761/12500 : ℝ)) (c := (2773062771200206799/2774000000000000000 : ℝ)) (alpha := (249581436443/138700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2773062771200206799/2774000000000000000 : ℝ)*(X 0 2+X 1 2)+(249581436443/138700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8333/2048 : ℝ)) (lo := (5657/50000 : ℝ)) (hi := (1761/12500 : ℝ)) (c := (2773062771200206799/2774000000000000000 : ℝ)) (alpha := (249581436443/138700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-54183363/250000000 : ℝ)*X 0 0+(337087373/625000000 : ℝ)*X 0 1+(1053079387/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344848659/10000000000 : ℝ)*X 1 0+(-558065989/2500000000 : ℝ)*X 1 1+(2632698467/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336212161/2500000000 : ℝ)*X 2 0+(2632698473/5000000000 : ℝ)*X 2 1+(-55806599/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((872959379/2000000000 : ℝ)*X 0 0+(4239342229/10000000000 : ℝ)*X 0 1+(2246973509/5000000000 : ℝ)*X 0 2+(872959379/2000000000 : ℝ)*X 1 0+(4239342229/10000000000 : ℝ)*X 1 1+(2246973509/5000000000 : ℝ)*X 1 2+(872959379/2000000000 : ℝ)*X 2 0+(4239342229/10000000000 : ℝ)*X 2 1+(2246973509/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-216733949/1000000000 : ℝ)*X 0 0+(5265720219/10000000000 : ℝ)*X 0 1+(168533547/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656210723/5000000000 : ℝ)*X 1 0+(-1052293707/5000000000 : ℝ)*X 1 1+(5393073507/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328105361/2500000000 : ℝ)*X 2 0+(2696536759/5000000000 : ℝ)*X 2 1+(-1052293701/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4364806767/10000000000 : ℝ)*X 0 0+(2246651989/5000000000 : ℝ)*X 0 1+(4239987607/10000000000 : ℝ)*X 0 2+(4364806767/10000000000 : ℝ)*X 1 0+(2246651989/5000000000 : ℝ)*X 1 1+(4239987607/10000000000 : ℝ)*X 1 2+(4364806767/10000000000 : ℝ)*X 2 0+(2246651989/5000000000 : ℝ)*X 2 1+(4239987607/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (516860976839774956463960397/138700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (814411909/100000000000000 : ℝ)*(base19) + (720989819/100000000000000 : ℝ)*(base23) + (38213969/100000000000000 : ℝ)*(lower2) + (105579277/100000000000000 : ℝ)*(upper3) + (21063913/50000000000000 : ℝ)*(upper5) + (5870080898829861/100000000000000 : ℝ)*(major0) + (5870080898829861/100000000000000 : ℝ)*(major1) + (2935040449414931/50000000000000 : ℝ)*(major2) + (1953115236166427/25000000000000 : ℝ)*(sp0) + (976560250056499/12500000000000 : ℝ)*(sp1) + (7812482093874083/100000000000000 : ℝ)*(sp2) + (981916642430861/25000000000000 : ℝ)*(sp3) + (10935099097/50000000000000 : ℝ)*(sp4) + (3072214199/25000000000000 : ℝ)*(sp7) + (1963839429290119/50000000000000 : ℝ)*(f.failure) + (7812482814863901/100000000000000 : ℝ)*(f.sum) + (113381460122751/13870000000000000000000000000 : ℝ)*base66 + (83093140810428681/14600000000000000000000000000000 : ℝ)*base67 + (2089115886701454131/138700000000000000000000000000000 : ℝ)*base70 + (231845143778828681/14600000000000000000000000000000 : ℝ)*base71 + (52721391277151/13870000000000000000000000000 : ℝ)*base74 + (1326007318277854131/138700000000000000000000000000000 : ℝ)*base76 + (147689061368715061/277400000000000000000000000000000 : ℝ)*base78 + (2048913014218084939/277400000000000000000000000000000 : ℝ)*base79 + (20504864912117/6935000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (34820557/5000000000000000000000 : ℝ)*base90 + (34820557/5000000000000000000000 : ℝ)*base92 + (84820557/5000000000000000000000 : ℝ)*base94 + (1/50000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (41281890797820880744653/6935000000000000000000000000 : ℝ) := by norm_num
    linear_combination (33722973/3125000000000 : ℝ)*(base19) + (1187986997/100000000000000 : ℝ)*(base23) + (59726467/50000000000000 : ℝ)*(upper3) + (48926501/100000000000000 : ℝ)*(lower4) + (30773337/25000000000000 : ℝ)*(upper5) + (5899902074042371/100000000000000 : ℝ)*(major0) + (5899902074042371/100000000000000 : ℝ)*(major1) + (5899902074042371/100000000000000 : ℝ)*(major2) + (5953360633/20000000000000 : ℝ)*(sp1) + (8248944957/25000000000000 : ℝ)*(sp2) + (1570434340696229/20000000000000 : ℝ)*(sp4) + (1963035214385711/25000000000000 : ℝ)*(sp5) + (98151718996429/1250000000000 : ℝ)*(sp6) + (1973816123090331/50000000000000 : ℝ)*(sp7) + (1973816123090331/50000000000000 : ℝ)*(f.failure) + (1570434340696229/20000000000000 : ℝ)*(f.sum) + (20614519139113/6935000000000000000000000000 : ℝ)*base65 + (1300846342968059571/277400000000000000000000000000000 : ℝ)*base68 + (410352778271740429/277400000000000000000000000000000 : ℝ)*base69 + (1171836957450859571/277400000000000000000000000000000 : ℝ)*base72 + (24264662239553/6935000000000000000000000000 : ℝ)*base73 + (1088508199729459571/277400000000000000000000000000000 : ℝ)*base76 + (705164301906940429/277400000000000000000000000000000 : ℝ)*base77 + (1072251766953740429/277400000000000000000000000000000 : ℝ)*base79 + (48774526248763/6935000000000000000000000000 : ℝ)*base81 + (28069207/5000000000000000000000 : ℝ)*base89 + (28069207/5000000000000000000000 : ℝ)*base91 + (28069207/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1141_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149454197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1761/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5657/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2269/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1757/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1141_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1141_s7_0 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-541840229/2500000000 : ℝ)*x 0 + (2696538507/5000000000 : ℝ)*x 1 + (5265700637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541840229/2500000000 : ℝ)^4167 ≤ (1646210653951/12500000000000 : ℝ)^3143 := by
    have hnat : (541840229 : ℕ)^4167*12500000000000^3143 ≤ 1646210653951^3143*2500000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541840229 2500000000 1646210653951 12500000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696538507/5000000000 : ℝ)^4167 ≤ (22051497812073/50000000000000 : ℝ)^3143 := by
    have hnat : (2696538507 : ℕ)^4167*50000000000000^3143 ≤ 22051497812073^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696538507 5000000000 22051497812073 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265700637/10000000000 : ℝ)^4167 ≤ (10681829781327/25000000000000 : ℝ)^3143 := by
    have hnat : (5265700637 : ℕ)^4167*25000000000000^3143 ≤ 10681829781327^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265700637 10000000000 10681829781327 25000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-541840229/2500000000 : ℝ), (2696538507/5000000000 : ℝ), (5265700637/10000000000 : ℝ)] ![(1646210653951/12500000000000 : ℝ), (22051497812073/50000000000000 : ℝ), (10681829781327/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-541840229/2500000000 : ℝ)|^4167 ≤ (1646210653951/12500000000000 : ℝ)^3143
        have hw : |(-541840229/2500000000 : ℝ)|=(541840229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696538507/5000000000 : ℝ)|^4167 ≤ (22051497812073/50000000000000 : ℝ)^3143
        have hw : |(2696538507/5000000000 : ℝ)|=(2696538507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265700637/10000000000 : ℝ)|^4167 ≤ (10681829781327/25000000000000 : ℝ)^3143
        have hw : |(5265700637/10000000000 : ℝ)|=(5265700637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s7_1 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344768349/10000000000 : ℝ)*x 0 + (-223196901/1000000000 : ℝ)*x 1 + (5265700637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344768349/10000000000 : ℝ)^4167 ≤ (21789998735027/50000000000000 : ℝ)^3143 := by
    have hnat : (5344768349 : ℕ)^4167*50000000000000^3143 ≤ 21789998735027^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344768349 10000000000 21789998735027 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (223196901/1000000000 : ℝ)^4167 ≤ (2738536678387/20000000000000 : ℝ)^3143 := by
    have hnat : (223196901 : ℕ)^4167*20000000000000^3143 ≤ 2738536678387^3143*1000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223196901 1000000000 2738536678387 20000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265700637/10000000000 : ℝ)^4167 ≤ (10681829781327/25000000000000 : ℝ)^3143 := by
    have hnat : (5265700637 : ℕ)^4167*25000000000000^3143 ≤ 10681829781327^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265700637 10000000000 10681829781327 25000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344768349/10000000000 : ℝ), (-223196901/1000000000 : ℝ), (5265700637/10000000000 : ℝ)] ![(21789998735027/50000000000000 : ℝ), (2738536678387/20000000000000 : ℝ), (10681829781327/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344768349/10000000000 : ℝ)|^4167 ≤ (21789998735027/50000000000000 : ℝ)^3143
        have hw : |(5344768349/10000000000 : ℝ)|=(5344768349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-223196901/1000000000 : ℝ)|^4167 ≤ (2738536678387/20000000000000 : ℝ)^3143
        have hw : |(-223196901/1000000000 : ℝ)|=(223196901/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265700637/10000000000 : ℝ)|^4167 ≤ (10681829781327/25000000000000 : ℝ)^3143
        have hw : |(5265700637/10000000000 : ℝ)|=(5265700637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s7_2 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344768349/10000000000 : ℝ)*x 0 + (5265700637/10000000000 : ℝ)*x 1 + (-223196901/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344768349/10000000000 : ℝ)^4167 ≤ (21789998735027/50000000000000 : ℝ)^3143 := by
    have hnat : (5344768349 : ℕ)^4167*50000000000000^3143 ≤ 21789998735027^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344768349 10000000000 21789998735027 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265700637/10000000000 : ℝ)^4167 ≤ (10681829781327/25000000000000 : ℝ)^3143 := by
    have hnat : (5265700637 : ℕ)^4167*25000000000000^3143 ≤ 10681829781327^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265700637 10000000000 10681829781327 25000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (223196901/1000000000 : ℝ)^4167 ≤ (2738536678387/20000000000000 : ℝ)^3143 := by
    have hnat : (223196901 : ℕ)^4167*20000000000000^3143 ≤ 2738536678387^3143*1000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223196901 1000000000 2738536678387 20000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344768349/10000000000 : ℝ), (5265700637/10000000000 : ℝ), (-223196901/1000000000 : ℝ)] ![(21789998735027/50000000000000 : ℝ), (10681829781327/25000000000000 : ℝ), (2738536678387/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344768349/10000000000 : ℝ)|^4167 ≤ (21789998735027/50000000000000 : ℝ)^3143
        have hw : |(5344768349/10000000000 : ℝ)|=(5344768349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265700637/10000000000 : ℝ)|^4167 ≤ (10681829781327/25000000000000 : ℝ)^3143
        have hw : |(5265700637/10000000000 : ℝ)|=(5265700637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-223196901/1000000000 : ℝ)|^4167 ≤ (2738536678387/20000000000000 : ℝ)^3143
        have hw : |(-223196901/1000000000 : ℝ)|=(223196901/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s7_3 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2182406397/5000000000 : ℝ)*x 0 + (4239961409/10000000000 : ℝ)*x 1 + (898664743/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182406397/5000000000 : ℝ)^4167 ≤ (33316947686969/100000000000000 : ℝ)^3143 := by
    have hnat : (2182406397 : ℕ)^4167*100000000000000^3143 ≤ 33316947686969^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182406397 5000000000 33316947686969 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4239961409/10000000000 : ℝ)^4167 ≤ (32059382661219/100000000000000 : ℝ)^3143 := by
    have hnat : (4239961409 : ℕ)^4167*100000000000000^3143 ≤ 32059382661219^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4239961409 10000000000 32059382661219 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (898664743/2000000000 : ℝ)^4167 ≤ (4327958704981/12500000000000 : ℝ)^3143 := by
    have hnat : (898664743 : ℕ)^4167*12500000000000^3143 ≤ 4327958704981^3143*2000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898664743 2000000000 4327958704981 12500000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2182406397/5000000000 : ℝ), (4239961409/10000000000 : ℝ), (898664743/2000000000 : ℝ)] ![(33316947686969/100000000000000 : ℝ), (32059382661219/100000000000000 : ℝ), (4327958704981/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2182406397/5000000000 : ℝ)|^4167 ≤ (33316947686969/100000000000000 : ℝ)^3143
        have hw : |(2182406397/5000000000 : ℝ)|=(2182406397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4239961409/10000000000 : ℝ)|^4167 ≤ (32059382661219/100000000000000 : ℝ)^3143
        have hw : |(4239961409/10000000000 : ℝ)|=(4239961409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(898664743/2000000000 : ℝ)|^4167 ≤ (4327958704981/12500000000000 : ℝ)^3143
        have hw : |(898664743/2000000000 : ℝ)|=(898664743/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s7_4 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1083682903/5000000000 : ℝ)*x 0 + (5266020771/10000000000 : ℝ)*x 1 + (1348188931/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083682903/5000000000 : ℝ)^4167 ≤ (13169724625809/100000000000000 : ℝ)^3143 := by
    have hnat : (1083682903 : ℕ)^4167*100000000000000^3143 ≤ 13169724625809^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083682903 5000000000 13169724625809 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266020771/10000000000 : ℝ)^4167 ≤ (42730763137663/100000000000000 : ℝ)^3143 := by
    have hnat : (5266020771 : ℕ)^4167*100000000000000^3143 ≤ 42730763137663^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266020771 10000000000 42730763137663 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348188931/2500000000 : ℝ)^4167 ≤ (44099512222279/100000000000000 : ℝ)^3143 := by
    have hnat : (1348188931 : ℕ)^4167*100000000000000^3143 ≤ 44099512222279^3143*2500000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348188931 2500000000 44099512222279 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1083682903/5000000000 : ℝ), (5266020771/10000000000 : ℝ), (1348188931/2500000000 : ℝ)] ![(13169724625809/100000000000000 : ℝ), (42730763137663/100000000000000 : ℝ), (44099512222279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1083682903/5000000000 : ℝ)|^4167 ≤ (13169724625809/100000000000000 : ℝ)^3143
        have hw : |(-1083682903/5000000000 : ℝ)|=(1083682903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266020771/10000000000 : ℝ)|^4167 ≤ (42730763137663/100000000000000 : ℝ)^3143
        have hw : |(5266020771/10000000000 : ℝ)|=(5266020771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348188931/2500000000 : ℝ)|^4167 ≤ (44099512222279/100000000000000 : ℝ)^3143
        have hw : |(1348188931/2500000000 : ℝ)|=(1348188931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s7_5 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656249651/5000000000 : ℝ)*x 0 + (-84196557/400000000 : ℝ)*x 1 + (5392755723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656249651/5000000000 : ℝ)^4167 ≤ (43231503198179/100000000000000 : ℝ)^3143 := by
    have hnat : (2656249651 : ℕ)^4167*100000000000000^3143 ≤ 43231503198179^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656249651 5000000000 43231503198179 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84196557/400000000 : ℝ)^4167 ≤ (12668984567131/100000000000000 : ℝ)^3143 := by
    have hnat : (84196557 : ℕ)^4167*100000000000000^3143 ≤ 12668984567131^3143*400000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84196557 400000000 12668984567131 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392755723/10000000000 : ℝ)^4167 ≤ (44099512211437/100000000000000 : ℝ)^3143 := by
    have hnat : (5392755723 : ℕ)^4167*100000000000000^3143 ≤ 44099512211437^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392755723 10000000000 44099512211437 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656249651/5000000000 : ℝ), (-84196557/400000000 : ℝ), (5392755723/10000000000 : ℝ)] ![(43231503198179/100000000000000 : ℝ), (12668984567131/100000000000000 : ℝ), (44099512211437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656249651/5000000000 : ℝ)|^4167 ≤ (43231503198179/100000000000000 : ℝ)^3143
        have hw : |(2656249651/5000000000 : ℝ)|=(2656249651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-84196557/400000000 : ℝ)|^4167 ≤ (12668984567131/100000000000000 : ℝ)^3143
        have hw : |(-84196557/400000000 : ℝ)|=(84196557/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392755723/10000000000 : ℝ)|^4167 ≤ (44099512211437/100000000000000 : ℝ)^3143
        have hw : |(5392755723/10000000000 : ℝ)|=(5392755723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s7_6 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312499303/10000000000 : ℝ)*x 0 + (1348188931/2500000000 : ℝ)*x 1 + (-526228481/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312499303/10000000000 : ℝ)^4167 ≤ (5403937901121/12500000000000 : ℝ)^3143 := by
    have hnat : (5312499303 : ℕ)^4167*12500000000000^3143 ≤ 5403937901121^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312499303 10000000000 5403937901121 12500000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348188931/2500000000 : ℝ)^4167 ≤ (44099512222279/100000000000000 : ℝ)^3143 := by
    have hnat : (1348188931 : ℕ)^4167*100000000000000^3143 ≤ 44099512222279^3143*2500000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348188931 2500000000 44099512222279 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526228481/2500000000 : ℝ)^4167 ≤ (12668984559151/100000000000000 : ℝ)^3143 := by
    have hnat : (526228481 : ℕ)^4167*100000000000000^3143 ≤ 12668984559151^3143*2500000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526228481 2500000000 12668984559151 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312499303/10000000000 : ℝ), (1348188931/2500000000 : ℝ), (-526228481/2500000000 : ℝ)] ![(5403937901121/12500000000000 : ℝ), (44099512222279/100000000000000 : ℝ), (12668984559151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312499303/10000000000 : ℝ)|^4167 ≤ (5403937901121/12500000000000 : ℝ)^3143
        have hw : |(5312499303/10000000000 : ℝ)|=(5312499303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348188931/2500000000 : ℝ)|^4167 ≤ (44099512222279/100000000000000 : ℝ)^3143
        have hw : |(1348188931/2500000000 : ℝ)|=(1348188931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-526228481/2500000000 : ℝ)|^4167 ≤ (12668984559151/100000000000000 : ℝ)^3143
        have hw : |(-526228481/2500000000 : ℝ)|=(526228481/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s7_7 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4364822523/10000000000 : ℝ)*x 0 + (2246343471/5000000000 : ℝ)*x 1 + (848120097/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364822523/10000000000 : ℝ)^4167 ≤ (16658523072037/50000000000000 : ℝ)^3143 := by
    have hnat : (4364822523 : ℕ)^4167*50000000000000^3143 ≤ 16658523072037^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364822523 10000000000 16658523072037 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2246343471/5000000000 : ℝ)^4167 ≤ (34617164462801/100000000000000 : ℝ)^3143 := by
    have hnat : (2246343471 : ℕ)^4167*100000000000000^3143 ≤ 34617164462801^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246343471 5000000000 34617164462801 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (848120097/2000000000 : ℝ)^4167 ≤ (8016447344561/25000000000000 : ℝ)^3143 := by
    have hnat : (848120097 : ℕ)^4167*25000000000000^3143 ≤ 8016447344561^3143*2000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848120097 2000000000 8016447344561 25000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364822523/10000000000 : ℝ), (2246343471/5000000000 : ℝ), (848120097/2000000000 : ℝ)] ![(16658523072037/50000000000000 : ℝ), (34617164462801/100000000000000 : ℝ), (8016447344561/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364822523/10000000000 : ℝ)|^4167 ≤ (16658523072037/50000000000000 : ℝ)^3143
        have hw : |(4364822523/10000000000 : ℝ)|=(4364822523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2246343471/5000000000 : ℝ)|^4167 ≤ (34617164462801/100000000000000 : ℝ)^3143
        have hw : |(2246343471/5000000000 : ℝ)|=(2246343471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(848120097/2000000000 : ℝ)|^4167 ≤ (8016447344561/25000000000000 : ℝ)^3143
        have hw : |(848120097/2000000000 : ℝ)|=(848120097/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1141_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149454197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1757/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2269/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11351/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14049/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1757/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2269/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1757/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2269/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1757/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2269/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1757/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2269/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1757/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2269/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1757/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2269/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2269/20000 : ℝ) ^ (8333/2048 : ℝ) ≤ (1426078741851457/10000000000000000000 : ℝ) := by
    have hpowers : (2269/20000 : ℝ)^8333 ≤ (1426078741851457/10000000000000000000 : ℝ)^2048 := by
      have hnat : (2269 : ℕ)^8333*10000000000000000000^2048 ≤ 1426078741851457^2048*20000^8333 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2269 20000 1426078741851457 10000000000000000000 8333 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2269/20000 : ℝ)) (X := (1426078741851457/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1757/12500 : ℝ) ^ (8333/2048 : ℝ) ≤ (3410195465067673/10000000000000000000 : ℝ) := by
    have hpowers : (1757/12500 : ℝ)^8333 ≤ (3410195465067673/10000000000000000000 : ℝ)^2048 := by
      have hnat : (1757 : ℕ)^8333*10000000000000000000^2048 ≤ 3410195465067673^2048*12500^8333 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1757 12500 3410195465067673 10000000000000000000 8333 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1757/12500 : ℝ)) (X := (3410195465067673/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001426078741851457/5000000000000000000 : ℝ) ≤ (5000350449439267/5000000000000000 : ℝ) ^ (8333/2048 : ℝ) := by
    have hpowers : (5001426078741851457/5000000000000000000 : ℝ)^2048 ≤ (5000350449439267/5000000000000000 : ℝ)^8333 := by
      have hnat : (5001426078741851457 : ℕ)^2048*5000000000000000^8333 ≤ 5000350449439267^8333*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001426078741851457 5000000000000000000 5000350449439267 5000000000000000 2048 8333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000350449439267/5000000000000000 : ℝ)) (X := (5001426078741851457/5000000000000000000 : ℝ)) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (1000483627420691913/1000000000000000000 : ℝ) ≤ (5000594196786123/5000000000000000 : ℝ) ^ (8333/2048 : ℝ) := by
    have hpowers : (1000483627420691913/1000000000000000000 : ℝ)^2048 ≤ (5000594196786123/5000000000000000 : ℝ)^8333 := by
      have hnat : (1000483627420691913 : ℕ)^2048*5000000000000000^8333 ≤ 5000594196786123^8333*1000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000483627420691913 1000000000000000000 5000594196786123 5000000000000000 2048 8333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000594196786123/5000000000000000 : ℝ)) (X := (1000483627420691913/1000000000000000000 : ℝ)) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003410195465067673/5000000000000000000 : ℝ) ≤ (5000837944132979/5000000000000000 : ℝ) ^ (8333/2048 : ℝ) := by
    have hpowers : (5003410195465067673/5000000000000000000 : ℝ)^2048 ≤ (5000837944132979/5000000000000000 : ℝ)^8333 := by
      have hnat : (5003410195465067673 : ℕ)^2048*5000000000000000^8333 ≤ 5000837944132979^8333*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003410195465067673 5000000000000000000 5000837944132979 5000000000000000 2048 8333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000837944132979/5000000000000000 : ℝ)) (X := (5003410195465067673/5000000000000000000 : ℝ)) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1426078741851457/10000000000000000000 : ℝ) ≤ ((13550419441129690197/13555000000000000000 : ℝ)+2*(30468418357/16943750000000 : ℝ)*(2269/20000 : ℝ))^(8333/2048 : ℝ) := by
    rw [show (13550419441129690197/13555000000000000000 : ℝ)+2*(30468418357/16943750000000 : ℝ)*(2269/20000 : ℝ)=(5000350449439267/5000000000000000 : ℝ) by norm_num, show 1+2*(1426078741851457/10000000000000000000 : ℝ)=(5001426078741851457/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3410195465067673/10000000000000000000 : ℝ)+(1426078741851457/10000000000000000000 : ℝ) ≤ ((13550419441129690197/13555000000000000000 : ℝ)+(30468418357/16943750000000 : ℝ)*((1757/12500 : ℝ)+(2269/20000 : ℝ)))^(8333/2048 : ℝ) := by
    rw [show (13550419441129690197/13555000000000000000 : ℝ)+(30468418357/16943750000000 : ℝ)*((1757/12500 : ℝ)+(2269/20000 : ℝ))=(5000594196786123/5000000000000000 : ℝ) by norm_num, show 1+(3410195465067673/10000000000000000000 : ℝ)+(1426078741851457/10000000000000000000 : ℝ)=(1000483627420691913/1000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3410195465067673/10000000000000000000 : ℝ) ≤ ((13550419441129690197/13555000000000000000 : ℝ)+2*(30468418357/16943750000000 : ℝ)*(1757/12500 : ℝ))^(8333/2048 : ℝ) := by
    rw [show (13550419441129690197/13555000000000000000 : ℝ)+2*(30468418357/16943750000000 : ℝ)*(1757/12500 : ℝ)=(5000837944132979/5000000000000000 : ℝ) by norm_num, show 1+2*(3410195465067673/10000000000000000000 : ℝ)=(5003410195465067673/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13550419441129690197/13555000000000000000 : ℝ)*(X 1 0+X 2 0)+(30468418357/16943750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8333/2048 : ℝ)) (lo := (2269/20000 : ℝ)) (hi := (1757/12500 : ℝ)) (c := (13550419441129690197/13555000000000000000 : ℝ)) (alpha := (30468418357/16943750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13550419441129690197/13555000000000000000 : ℝ)*(X 0 1+X 2 1)+(30468418357/16943750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8333/2048 : ℝ)) (lo := (2269/20000 : ℝ)) (hi := (1757/12500 : ℝ)) (c := (13550419441129690197/13555000000000000000 : ℝ)) (alpha := (30468418357/16943750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13550419441129690197/13555000000000000000 : ℝ)*(X 0 2+X 1 2)+(30468418357/16943750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8333/2048 : ℝ)) (lo := (2269/20000 : ℝ)) (hi := (1757/12500 : ℝ)) (c := (13550419441129690197/13555000000000000000 : ℝ)) (alpha := (30468418357/16943750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-541840229/2500000000 : ℝ)*X 0 0+(2696538507/5000000000 : ℝ)*X 0 1+(5265700637/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344768349/10000000000 : ℝ)*X 1 0+(-223196901/1000000000 : ℝ)*X 1 1+(5265700637/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344768349/10000000000 : ℝ)*X 2 0+(5265700637/10000000000 : ℝ)*X 2 1+(-223196901/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2182406397/5000000000 : ℝ)*X 0 0+(4239961409/10000000000 : ℝ)*X 0 1+(898664743/2000000000 : ℝ)*X 0 2+(2182406397/5000000000 : ℝ)*X 1 0+(4239961409/10000000000 : ℝ)*X 1 1+(898664743/2000000000 : ℝ)*X 1 2+(2182406397/5000000000 : ℝ)*X 2 0+(4239961409/10000000000 : ℝ)*X 2 1+(898664743/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1083682903/5000000000 : ℝ)*X 0 0+(5266020771/10000000000 : ℝ)*X 0 1+(1348188931/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656249651/5000000000 : ℝ)*X 1 0+(-84196557/400000000 : ℝ)*X 1 1+(5392755723/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312499303/10000000000 : ℝ)*X 2 0+(1348188931/2500000000 : ℝ)*X 2 1+(-526228481/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4364822523/10000000000 : ℝ)*X 0 0+(2246343471/5000000000 : ℝ)*X 0 1+(848120097/2000000000 : ℝ)*X 0 2+(4364822523/10000000000 : ℝ)*X 1 0+(2246343471/5000000000 : ℝ)*X 1 1+(848120097/2000000000 : ℝ)*X 1 2+(4364822523/10000000000 : ℝ)*X 2 0+(2246343471/5000000000 : ℝ)*X 2 1+(848120097/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (696126783281353239447906627/84718750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (812346241/50000000000000 : ℝ)*(base19) + (1512443421/100000000000000 : ℝ)*(base23) + (59994523/100000000000000 : ℝ)*(lower2) + (208025087/100000000000000 : ℝ)*(upper3) + (2499203/2000000000000 : ℝ)*(upper5) + (1474725332452397/25000000000000 : ℝ)*(major0) + (1474725332452397/25000000000000 : ℝ)*(major1) + (5898901329809589/100000000000000 : ℝ)*(major2) + (1570159114541859/20000000000000 : ℝ)*(sp0) + (3925419057066347/50000000000000 : ℝ)*(sp1) + (3925419113190877/50000000000000 : ℝ)*(sp2) + (1973469316270361/50000000000000 : ℝ)*(sp3) + (44166115881/100000000000000 : ℝ)*(sp4) + (24014356099/100000000000000 : ℝ)*(sp7) + (3946962646896821/100000000000000 : ℝ)*(f.failure) + (314033589553007/4000000000000 : ℝ)*(f.sum) + (25675327684633/13555000000000000000000000000 : ℝ)*base66 + (2448740455486222791/338875000000000000000000000000000 : ℝ)*base68 + (21033988784680699033/1355500000000000000000000000000000 : ℝ)*base69 + (4165566369517972791/338875000000000000000000000000000 : ℝ)*base72 + (4352227442829/1694375000000000000000000000 : ℝ)*base73 + (1861697083723800967/1355500000000000000000000000000000 : ℝ)*base76 + (1831051085606872791/338875000000000000000000000000000 : ℝ)*base78 + (399681942030997791/338875000000000000000000000000000 : ℝ)*base80 + (26558206375619/13555000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (124407737/10000000000000000000000 : ℝ)*base89 + (124407737/10000000000000000000000 : ℝ)*base91 + (24407737/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1159027177606935450474945771/338875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (618555327/100000000000000 : ℝ)*(base19) + (678304951/100000000000000 : ℝ)*(base23) + (67603299/100000000000000 : ℝ)*(upper3) + (2628603/10000000000000 : ℝ)*(lower4) + (69872439/100000000000000 : ℝ)*(upper5) + (5928687637581981/100000000000000 : ℝ)*(major0) + (5928687637581981/100000000000000 : ℝ)*(major1) + (5928687637581981/100000000000000 : ℝ)*(major2) + (17047030987/100000000000000 : ℝ)*(sp1) + (18493279587/100000000000000 : ℝ)*(sp2) + (3945241228254727/50000000000000 : ℝ)*(sp4) + (394523239546157/5000000000000 : ℝ)*(sp5) + (7890463284924917/100000000000000 : ℝ)*(sp6) + (3966892704647151/100000000000000 : ℝ)*(sp7) + (3966892704647151/100000000000000 : ℝ)*(f.failure) + (3945241228254727/50000000000000 : ℝ)*(f.sum) + (41695566320723/13555000000000000000000000000 : ℝ)*base66 + (11338094561724859743/1355500000000000000000000000000000 : ℝ)*base68 + (11767803860077359743/1355500000000000000000000000000000 : ℝ)*base70 + (1192704947644859743/1355500000000000000000000000000000 : ℝ)*base72 + (9945204079561/1694375000000000000000000000 : ℝ)*base74 + (52126669936463859743/1355500000000000000000000000000000 : ℝ)*base76 + (3077464388664640257/1355500000000000000000000000000000 : ℝ)*base77 + (40650921397636359743/1355500000000000000000000000000000 : ℝ)*base80 + (53056960555837/13555000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (21042747/10000000000000000000000 : ℝ)*base89 + (21042747/10000000000000000000000 : ℝ)*base91 + (21042747/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1141_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149454197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1757/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2269/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11351/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14049/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1141_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1141_s8_0 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2167368871/10000000000 : ℝ)*x 0 + (5393010317/10000000000 : ℝ)*x 1 + (2632880949/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2167368871/10000000000 : ℝ)^4167 ≤ (1316974931769/10000000000000 : ℝ)^3143 := by
    have hnat : (2167368871 : ℕ)^4167*10000000000000^3143 ≤ 1316974931769^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2167368871 10000000000 1316974931769 10000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393010317/10000000000 : ℝ)^4167 ≤ (22051136247379/50000000000000 : ℝ)^3143 := by
    have hnat : (5393010317 : ℕ)^4167*50000000000000^3143 ≤ 22051136247379^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393010317 10000000000 22051136247379 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632880949/5000000000 : ℝ)^4167 ≤ (42727978167931/100000000000000 : ℝ)^3143 := by
    have hnat : (2632880949 : ℕ)^4167*100000000000000^3143 ≤ 42727978167931^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632880949 5000000000 42727978167931 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2167368871/10000000000 : ℝ), (5393010317/10000000000 : ℝ), (2632880949/5000000000 : ℝ)] ![(1316974931769/10000000000000 : ℝ), (22051136247379/50000000000000 : ℝ), (42727978167931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2167368871/10000000000 : ℝ)|^4167 ≤ (1316974931769/10000000000000 : ℝ)^3143
        have hw : |(-2167368871/10000000000 : ℝ)|=(2167368871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393010317/10000000000 : ℝ)|^4167 ≤ (22051136247379/50000000000000 : ℝ)^3143
        have hw : |(5393010317/10000000000 : ℝ)|=(5393010317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632880949/5000000000 : ℝ)|^4167 ≤ (42727978167931/100000000000000 : ℝ)^3143
        have hw : |(2632880949/5000000000 : ℝ)|=(2632880949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s8_1 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336187733/2500000000 : ℝ)*x 0 + (-34873611/156250000 : ℝ)*x 1 + (2632880959/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336187733/2500000000 : ℝ)^4167 ≤ (8715961837459/20000000000000 : ℝ)^3143 := by
    have hnat : (1336187733 : ℕ)^4167*20000000000000^3143 ≤ 8715961837459^3143*2500000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336187733 2500000000 8715961837459 20000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34873611/156250000 : ℝ)^4167 ≤ (13692212413247/100000000000000 : ℝ)^3143 := by
    have hnat : (34873611 : ℕ)^4167*100000000000000^3143 ≤ 13692212413247^3143*156250000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34873611 156250000 13692212413247 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632880959/5000000000 : ℝ)^4167 ≤ (4272797838309/10000000000000 : ℝ)^3143 := by
    have hnat : (2632880959 : ℕ)^4167*10000000000000^3143 ≤ 4272797838309^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632880959 5000000000 4272797838309 10000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336187733/2500000000 : ℝ), (-34873611/156250000 : ℝ), (2632880959/5000000000 : ℝ)] ![(8715961837459/20000000000000 : ℝ), (13692212413247/100000000000000 : ℝ), (4272797838309/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336187733/2500000000 : ℝ)|^4167 ≤ (8715961837459/20000000000000 : ℝ)^3143
        have hw : |(1336187733/2500000000 : ℝ)|=(1336187733/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-34873611/156250000 : ℝ)|^4167 ≤ (13692212413247/100000000000000 : ℝ)^3143
        have hw : |(-34873611/156250000 : ℝ)|=(34873611/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632880959/5000000000 : ℝ)|^4167 ≤ (4272797838309/10000000000000 : ℝ)^3143
        have hw : |(2632880959/5000000000 : ℝ)|=(2632880959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s8_2 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344750901/10000000000 : ℝ)*x 0 + (5265761931/10000000000 : ℝ)*x 1 + (-278988891/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344750901/10000000000 : ℝ)^4167 ≤ (2723738053261/6250000000000 : ℝ)^3143 := by
    have hnat : (5344750901 : ℕ)^4167*6250000000000^3143 ≤ 2723738053261^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344750901 10000000000 2723738053261 6250000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265761931/10000000000 : ℝ)^4167 ≤ (667624664421/1562500000000 : ℝ)^3143 := by
    have hnat : (5265761931 : ℕ)^4167*1562500000000^3143 ≤ 667624664421^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265761931 10000000000 667624664421 1562500000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (278988891/1250000000 : ℝ)^4167 ≤ (273844252169/2000000000000 : ℝ)^3143 := by
    have hnat : (278988891 : ℕ)^4167*2000000000000^3143 ≤ 273844252169^3143*1250000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278988891 1250000000 273844252169 2000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344750901/10000000000 : ℝ), (5265761931/10000000000 : ℝ), (-278988891/1250000000 : ℝ)] ![(2723738053261/6250000000000 : ℝ), (667624664421/1562500000000 : ℝ), (273844252169/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344750901/10000000000 : ℝ)|^4167 ≤ (2723738053261/6250000000000 : ℝ)^3143
        have hw : |(5344750901/10000000000 : ℝ)|=(5344750901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265761931/10000000000 : ℝ)|^4167 ≤ (667624664421/1562500000000 : ℝ)^3143
        have hw : |(5265761931/10000000000 : ℝ)|=(5265761931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-278988891/1250000000 : ℝ)|^4167 ≤ (273844252169/2000000000000 : ℝ)^3143
        have hw : |(-278988891/1250000000 : ℝ)|=(278988891/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s8_3 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4364816049/10000000000 : ℝ)*x 0 + (848017649/2000000000 : ℝ)*x 1 + (4493196029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364816049/10000000000 : ℝ)^4167 ≤ (6663396125487/20000000000000 : ℝ)^3143 := by
    have hnat : (4364816049 : ℕ)^4167*20000000000000^3143 ≤ 6663396125487^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364816049 10000000000 6663396125487 20000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (848017649/2000000000 : ℝ)^4167 ≤ (2003790885197/6250000000000 : ℝ)^3143 := by
    have hnat : (848017649 : ℕ)^4167*6250000000000^3143 ≤ 2003790885197^3143*2000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848017649 2000000000 2003790885197 6250000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4493196029/10000000000 : ℝ)^4167 ≤ (3462236519483/10000000000000 : ℝ)^3143 := by
    have hnat : (4493196029 : ℕ)^4167*10000000000000^3143 ≤ 3462236519483^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493196029 10000000000 3462236519483 10000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364816049/10000000000 : ℝ), (848017649/2000000000 : ℝ), (4493196029/10000000000 : ℝ)] ![(6663396125487/20000000000000 : ℝ), (2003790885197/6250000000000 : ℝ), (3462236519483/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364816049/10000000000 : ℝ)|^4167 ≤ (6663396125487/20000000000000 : ℝ)^3143
        have hw : |(4364816049/10000000000 : ℝ)|=(4364816049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(848017649/2000000000 : ℝ)|^4167 ≤ (2003790885197/6250000000000 : ℝ)^3143
        have hw : |(848017649/2000000000 : ℝ)|=(848017649/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4493196029/10000000000 : ℝ)|^4167 ≤ (3462236519483/10000000000000 : ℝ)^3143
        have hw : |(4493196029/10000000000 : ℝ)|=(4493196029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s8_4 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2167374037/10000000000 : ℝ)*x 0 + (5266081167/10000000000 : ℝ)*x 1 + (5392689677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2167374037/10000000000 : ℝ)^4167 ≤ (13169790935417/100000000000000 : ℝ)^3143 := by
    have hnat : (2167374037 : ℕ)^4167*100000000000000^3143 ≤ 13169790935417^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2167374037 10000000000 13169790935417 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266081167/10000000000 : ℝ)^4167 ≤ (21365706443757/50000000000000 : ℝ)^3143 := by
    have hnat : (5266081167 : ℕ)^4167*50000000000000^3143 ≤ 21365706443757^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266081167 10000000000 21365706443757 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392689677/10000000000 : ℝ)^4167 ≤ (44098796154081/100000000000000 : ℝ)^3143 := by
    have hnat : (5392689677 : ℕ)^4167*100000000000000^3143 ≤ 44098796154081^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392689677 10000000000 44098796154081 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2167374037/10000000000 : ℝ), (5266081167/10000000000 : ℝ), (5392689677/10000000000 : ℝ)] ![(13169790935417/100000000000000 : ℝ), (21365706443757/50000000000000 : ℝ), (44098796154081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2167374037/10000000000 : ℝ)|^4167 ≤ (13169790935417/100000000000000 : ℝ)^3143
        have hw : |(-2167374037/10000000000 : ℝ)|=(2167374037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266081167/10000000000 : ℝ)|^4167 ≤ (21365706443757/50000000000000 : ℝ)^3143
        have hw : |(5266081167/10000000000 : ℝ)|=(5266081167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392689677/10000000000 : ℝ)|^4167 ≤ (44098796154081/100000000000000 : ℝ)^3143
        have hw : |(5392689677/10000000000 : ℝ)|=(5392689677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s8_5 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656257437/5000000000 : ℝ)*x 0 + (-420996661/2000000000 : ℝ)*x 1 + (2696344581/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656257437/5000000000 : ℝ)^4167 ≤ (43231671204327/100000000000000 : ℝ)^3143 := by
    have hnat : (2656257437 : ℕ)^4167*100000000000000^3143 ≤ 43231671204327^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656257437 5000000000 43231671204327 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (420996661/2000000000 : ℝ)^4167 ≤ (12669538201717/100000000000000 : ℝ)^3143 := by
    have hnat : (420996661 : ℕ)^4167*100000000000000^3143 ≤ 12669538201717^3143*2000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420996661 2000000000 12669538201717 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696344581/5000000000 : ℝ)^4167 ≤ (44098790570567/100000000000000 : ℝ)^3143 := by
    have hnat : (2696344581 : ℕ)^4167*100000000000000^3143 ≤ 44098790570567^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696344581 5000000000 44098790570567 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656257437/5000000000 : ℝ), (-420996661/2000000000 : ℝ), (2696344581/5000000000 : ℝ)] ![(43231671204327/100000000000000 : ℝ), (12669538201717/100000000000000 : ℝ), (44098790570567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656257437/5000000000 : ℝ)|^4167 ≤ (43231671204327/100000000000000 : ℝ)^3143
        have hw : |(2656257437/5000000000 : ℝ)|=(2656257437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-420996661/2000000000 : ℝ)|^4167 ≤ (12669538201717/100000000000000 : ℝ)^3143
        have hw : |(-420996661/2000000000 : ℝ)|=(420996661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696344581/5000000000 : ℝ)|^4167 ≤ (44098790570567/100000000000000 : ℝ)^3143
        have hw : |(2696344581/5000000000 : ℝ)|=(2696344581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s8_6 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312514171/10000000000 : ℝ)*x 0 + (5392689847/10000000000 : ℝ)*x 1 + (-1052491663/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312514171/10000000000 : ℝ)^4167 ≤ (43231663619663/100000000000000 : ℝ)^3143 := by
    have hnat : (5312514171 : ℕ)^4167*100000000000000^3143 ≤ 43231663619663^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312514171 10000000000 43231663619663 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392689847/10000000000 : ℝ)^4167 ≤ (44098797997183/100000000000000 : ℝ)^3143 := by
    have hnat : (5392689847 : ℕ)^4167*100000000000000^3143 ≤ 44098797997183^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392689847 10000000000 44098797997183 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052491663/5000000000 : ℝ)^4167 ≤ (3167384592323/25000000000000 : ℝ)^3143 := by
    have hnat : (1052491663 : ℕ)^4167*25000000000000^3143 ≤ 3167384592323^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052491663 5000000000 3167384592323 25000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312514171/10000000000 : ℝ), (5392689847/10000000000 : ℝ), (-1052491663/5000000000 : ℝ)] ![(43231663619663/100000000000000 : ℝ), (44098797997183/100000000000000 : ℝ), (3167384592323/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312514171/10000000000 : ℝ)|^4167 ≤ (43231663619663/100000000000000 : ℝ)^3143
        have hw : |(5312514171/10000000000 : ℝ)|=(5312514171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392689847/10000000000 : ℝ)|^4167 ≤ (44098797997183/100000000000000 : ℝ)^3143
        have hw : |(5392689847/10000000000 : ℝ)|=(5392689847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1052491663/5000000000 : ℝ)|^4167 ≤ (3167384592323/25000000000000 : ℝ)^3143
        have hw : |(-1052491663/5000000000 : ℝ)|=(1052491663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s8_7 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2182412973/5000000000 : ℝ)*x 0 + (4492560379/10000000000 : ℝ)*x 1 + (848145199/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182412973/5000000000 : ℝ)^4167 ≤ (416463509809/1250000000000 : ℝ)^3143 := by
    have hnat : (2182412973 : ℕ)^4167*1250000000000^3143 ≤ 416463509809^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182412973 5000000000 416463509809 1250000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4492560379/10000000000 : ℝ)^4167 ≤ (34615871550043/100000000000000 : ℝ)^3143 := by
    have hnat : (4492560379 : ℕ)^4167*100000000000000^3143 ≤ 34615871550043^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492560379 10000000000 34615871550043 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (848145199/2000000000 : ℝ)^4167 ≤ (4008380956131/12500000000000 : ℝ)^3143 := by
    have hnat : (848145199 : ℕ)^4167*12500000000000^3143 ≤ 4008380956131^3143*2000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848145199 2000000000 4008380956131 12500000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2182412973/5000000000 : ℝ), (4492560379/10000000000 : ℝ), (848145199/2000000000 : ℝ)] ![(416463509809/1250000000000 : ℝ), (34615871550043/100000000000000 : ℝ), (4008380956131/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2182412973/5000000000 : ℝ)|^4167 ≤ (416463509809/1250000000000 : ℝ)^3143
        have hw : |(2182412973/5000000000 : ℝ)|=(2182412973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4492560379/10000000000 : ℝ)|^4167 ≤ (34615871550043/100000000000000 : ℝ)^3143
        have hw : |(4492560379/10000000000 : ℝ)|=(4492560379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(848145199/2000000000 : ℝ)|^4167 ≤ (4008380956131/12500000000000 : ℝ)^3143
        have hw : |(848145199/2000000000 : ℝ)|=(848145199/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1141_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149454197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14049/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11351/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1419/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (439/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14049/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11351/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14049/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11351/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14049/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11351/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14049/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11351/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14049/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11351/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14049/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11351/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11351/100000 : ℝ) ^ (8333/2048 : ℝ) ≤ (14291499843172367/100000000000000000000 : ℝ) := by
    have hpowers : (11351/100000 : ℝ)^8333 ≤ (14291499843172367/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11351 : ℕ)^8333*100000000000000000000^2048 ≤ 14291499843172367^2048*100000^8333 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11351 100000 14291499843172367 100000000000000000000 8333 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11351/100000 : ℝ)) (X := (14291499843172367/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14049/100000 : ℝ) ^ (8333/2048 : ℝ) ≤ (34032906013329589/100000000000000000000 : ℝ) := by
    have hpowers : (14049/100000 : ℝ)^8333 ≤ (34032906013329589/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14049 : ℕ)^8333*100000000000000000000^2048 ≤ 34032906013329589^2048*100000^8333 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14049 100000 34032906013329589 100000000000000000000 8333 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14049/100000 : ℝ)) (X := (34032906013329589/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014291499843172367/50000000000000000000 : ℝ) ≤ (10000702408190997/10000000000000000 : ℝ) ^ (8333/2048 : ℝ) := by
    have hpowers : (50014291499843172367/50000000000000000000 : ℝ)^2048 ≤ (10000702408190997/10000000000000000 : ℝ)^8333 := by
      have hnat : (50014291499843172367 : ℕ)^2048*10000000000000000^8333 ≤ 10000702408190997^8333*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014291499843172367 50000000000000000000 10000702408190997 10000000000000000 2048 8333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000702408190997/10000000000000000 : ℝ)) (X := (50014291499843172367/50000000000000000000 : ℝ)) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012081101464125489/25000000000000000000 : ℝ) ≤ (1250148431465899/1250000000000000 : ℝ) ^ (8333/2048 : ℝ) := by
    have hpowers : (25012081101464125489/25000000000000000000 : ℝ)^2048 ≤ (1250148431465899/1250000000000000 : ℝ)^8333 := by
      have hnat : (25012081101464125489 : ℕ)^2048*1250000000000000^8333 ≤ 1250148431465899^8333*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012081101464125489 25000000000000000000 1250148431465899 1250000000000000 2048 8333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250148431465899/1250000000000000 : ℝ)) (X := (25012081101464125489/25000000000000000000 : ℝ)) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034032906013329589/50000000000000000000 : ℝ) ≤ (10001672495263387/10000000000000000 : ℝ) ^ (8333/2048 : ℝ) := by
    have hpowers : (50034032906013329589/50000000000000000000 : ℝ)^2048 ≤ (10001672495263387/10000000000000000 : ℝ)^8333 := by
      have hnat : (50034032906013329589 : ℕ)^2048*10000000000000000^8333 ≤ 10001672495263387^8333*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034032906013329589 50000000000000000000 10001672495263387 10000000000000000 2048 8333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001672495263387/10000000000000000 : ℝ)) (X := (50034032906013329589/50000000000000000000 : ℝ)) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14291499843172367/100000000000000000000 : ℝ) ≤ ((3371360454867576377/3372500000000000000 : ℝ)+2*(97008707239/53960000000000 : ℝ)*(11351/100000 : ℝ))^(8333/2048 : ℝ) := by
    rw [show (3371360454867576377/3372500000000000000 : ℝ)+2*(97008707239/53960000000000 : ℝ)*(11351/100000 : ℝ)=(10000702408190997/10000000000000000 : ℝ) by norm_num, show 1+2*(14291499843172367/100000000000000000000 : ℝ)=(50014291499843172367/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34032906013329589/100000000000000000000 : ℝ)+(14291499843172367/100000000000000000000 : ℝ) ≤ ((3371360454867576377/3372500000000000000 : ℝ)+(97008707239/53960000000000 : ℝ)*((14049/100000 : ℝ)+(11351/100000 : ℝ)))^(8333/2048 : ℝ) := by
    rw [show (3371360454867576377/3372500000000000000 : ℝ)+(97008707239/53960000000000 : ℝ)*((14049/100000 : ℝ)+(11351/100000 : ℝ))=(1250148431465899/1250000000000000 : ℝ) by norm_num, show 1+(34032906013329589/100000000000000000000 : ℝ)+(14291499843172367/100000000000000000000 : ℝ)=(25012081101464125489/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34032906013329589/100000000000000000000 : ℝ) ≤ ((3371360454867576377/3372500000000000000 : ℝ)+2*(97008707239/53960000000000 : ℝ)*(14049/100000 : ℝ))^(8333/2048 : ℝ) := by
    rw [show (3371360454867576377/3372500000000000000 : ℝ)+2*(97008707239/53960000000000 : ℝ)*(14049/100000 : ℝ)=(10001672495263387/10000000000000000 : ℝ) by norm_num, show 1+2*(34032906013329589/100000000000000000000 : ℝ)=(50034032906013329589/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3371360454867576377/3372500000000000000 : ℝ)*(X 1 0+X 2 0)+(97008707239/53960000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8333/2048 : ℝ)) (lo := (11351/100000 : ℝ)) (hi := (14049/100000 : ℝ)) (c := (3371360454867576377/3372500000000000000 : ℝ)) (alpha := (97008707239/53960000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3371360454867576377/3372500000000000000 : ℝ)*(X 0 1+X 2 1)+(97008707239/53960000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8333/2048 : ℝ)) (lo := (11351/100000 : ℝ)) (hi := (14049/100000 : ℝ)) (c := (3371360454867576377/3372500000000000000 : ℝ)) (alpha := (97008707239/53960000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3371360454867576377/3372500000000000000 : ℝ)*(X 0 2+X 1 2)+(97008707239/53960000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8333/2048 : ℝ)) (lo := (11351/100000 : ℝ)) (hi := (14049/100000 : ℝ)) (c := (3371360454867576377/3372500000000000000 : ℝ)) (alpha := (97008707239/53960000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2167368871/10000000000 : ℝ)*X 0 0+(5393010317/10000000000 : ℝ)*X 0 1+(2632880949/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336187733/2500000000 : ℝ)*X 1 0+(-34873611/156250000 : ℝ)*X 1 1+(2632880959/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344750901/10000000000 : ℝ)*X 2 0+(5265761931/10000000000 : ℝ)*X 2 1+(-278988891/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4364816049/10000000000 : ℝ)*X 0 0+(848017649/2000000000 : ℝ)*X 0 1+(4493196029/10000000000 : ℝ)*X 0 2+(4364816049/10000000000 : ℝ)*X 1 0+(848017649/2000000000 : ℝ)*X 1 1+(4493196029/10000000000 : ℝ)*X 1 2+(4364816049/10000000000 : ℝ)*X 2 0+(848017649/2000000000 : ℝ)*X 2 1+(4493196029/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2167374037/10000000000 : ℝ)*X 0 0+(5266081167/10000000000 : ℝ)*X 0 1+(5392689677/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656257437/5000000000 : ℝ)*X 1 0+(-420996661/2000000000 : ℝ)*X 1 1+(2696344581/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312514171/10000000000 : ℝ)*X 2 0+(5392689847/10000000000 : ℝ)*X 2 1+(-1052491663/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2182412973/5000000000 : ℝ)*X 0 0+(4492560379/10000000000 : ℝ)*X 0 1+(848145199/2000000000 : ℝ)*X 0 2+(2182412973/5000000000 : ℝ)*X 1 0+(4492560379/10000000000 : ℝ)*X 1 1+(848145199/2000000000 : ℝ)*X 1 2+(2182412973/5000000000 : ℝ)*X 2 0+(4492560379/10000000000 : ℝ)*X 2 1+(848145199/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1872835127690692378500780231/168625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2214330259/100000000000000 : ℝ)*(base19) + (2013978509/100000000000000 : ℝ)*(base23) + (16544169/20000000000000 : ℝ)*(lower2) + (306737153/100000000000000 : ℝ)*(upper3) + (36305753/25000000000000 : ℝ)*(upper5) + (5904859134148101/100000000000000 : ℝ)*(major0) + (5904859134148101/100000000000000 : ℝ)*(major1) + (2952429567074051/50000000000000 : ℝ)*(major2) + (7858709212837003/100000000000000 : ℝ)*(sp0) + (98234583276557/1250000000000 : ℝ)*(sp1) + (785876686247631/10000000000000 : ℝ)*(sp2) + (3950915491202291/100000000000000 : ℝ)*(sp3) + (7457952227/12500000000000 : ℝ)*(sp4) + (8382605527/25000000000000 : ℝ)*(sp7) + (3950949021624399/100000000000000 : ℝ)*(f.failure) + (7858768876454819/100000000000000 : ℝ)*(f.sum) + (5296342075441/1079200000000000000000000000 : ℝ)*base65 + (7027465034666864923/337250000000000000000000000000000 : ℝ)*base68 + (453541935585238023/168625000000000000000000000000000 : ℝ)*base70 + (4049147184180114923/337250000000000000000000000000000 : ℝ)*base72 + (1807387367933/1079200000000000000000000000 : ℝ)*base73 + (1347017442046511977/168625000000000000000000000000000 : ℝ)*base75 + (2756037343839947577/337250000000000000000000000000000 : ℝ)*base77 + (4890548291135052423/337250000000000000000000000000000 : ℝ)*base80 + (14419356456277/2698000000000000000000000000 : ℝ)*base81 + (88152603/10000000000000000000000 : ℝ)*base89 + (88152603/10000000000000000000000 : ℝ)*base91 + (11847397/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (135544264267099951630338357/33725000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (265892877/10000000000000 : ℝ)*(base19) + (443296283/25000000000000 : ℝ)*(base23) + (275121081/50000000000000 : ℝ)*(lower1) + (23762213/20000000000000 : ℝ)*(upper2) + (6686557/5000000000000 : ℝ)*(upper3) + (86325957/25000000000000 : ℝ)*(upper5) + (1186914617128247/20000000000000 : ℝ)*(major0) + (1186914617128247/20000000000000 : ℝ)*(major1) + (1186914617128247/20000000000000 : ℝ)*(major2) + (10582014371/100000000000000 : ℝ)*(sp1) + (7898315371619337/100000000000000 : ℝ)*(sp4) + (1974575532669049/25000000000000 : ℝ)*(sp5) + (3949156799217103/50000000000000 : ℝ)*(sp6) + (794166133138601/20000000000000 : ℝ)*(sp7) + (794166133138601/20000000000000 : ℝ)*(f.failure) + (7898315371619337/100000000000000 : ℝ)*(f.sum) + (18325167596013/2698000000000000000000000000 : ℝ)*base66 + (256019031692383619/67450000000000000000000000000000 : ℝ)*base67 + (1669325971235116381/67450000000000000000000000000000 : ℝ)*base70 + (846637157313983619/67450000000000000000000000000000 : ℝ)*base71 + (12776221402473/2698000000000000000000000000 : ℝ)*base74 + (524539424593566381/67450000000000000000000000000000 : ℝ)*base76 + (368727540303516381/67450000000000000000000000000000 : ℝ)*base78 + (1155370882999966381/67450000000000000000000000000000 : ℝ)*base80 + (85832801079497/2698000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (2158397/2000000000000000000000 : ℝ)*base89 + (2158397/2000000000000000000000 : ℝ)*base91 + (2158397/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1141_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149454197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14049/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11351/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1419/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (439/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1141_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1141_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149454197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1761/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5657/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1419/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (439/3125 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1141_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1141_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1141_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149454197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1761/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5657/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1419/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (439/3125 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1141_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

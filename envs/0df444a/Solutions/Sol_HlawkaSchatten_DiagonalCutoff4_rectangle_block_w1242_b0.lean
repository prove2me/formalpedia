-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1242_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:19:27.861414+00:00
-- url     : https://prove2.me/submissions/36f6f5b4-2e0e-4124-93e9-5eddebd8260c

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
theorem support_rectangle_w1242_s0_0 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1860560099/10000000000 : ℝ)*x 0 + (6031505241/10000000000 : ℝ)*x 1 + (2396493913/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1860560099/10000000000 : ℝ)^8435 ≤ (2170121180601/20000000000000 : ℝ)^6387 := by
    have hnat : (1860560099 : ℕ)^8435*20000000000000^6387 ≤ 2170121180601^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1860560099 10000000000 2170121180601 20000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6031505241/10000000000 : ℝ)^8435 ≤ (12822093263577/25000000000000 : ℝ)^6387 := by
    have hnat : (6031505241 : ℕ)^8435*25000000000000^6387 ≤ 12822093263577^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6031505241 10000000000 12822093263577 25000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2396493913/5000000000 : ℝ)^8435 ≤ (1183156907119/3125000000000 : ℝ)^6387 := by
    have hnat : (2396493913 : ℕ)^8435*3125000000000^6387 ≤ 1183156907119^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2396493913 5000000000 1183156907119 3125000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1860560099/10000000000 : ℝ), (6031505241/10000000000 : ℝ), (2396493913/5000000000 : ℝ)] ![(2170121180601/20000000000000 : ℝ), (12822093263577/25000000000000 : ℝ), (1183156907119/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1860560099/10000000000 : ℝ)|^8435 ≤ (2170121180601/20000000000000 : ℝ)^6387
        have hw : |(-1860560099/10000000000 : ℝ)|=(1860560099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6031505241/10000000000 : ℝ)|^8435 ≤ (12822093263577/25000000000000 : ℝ)^6387
        have hw : |(6031505241/10000000000 : ℝ)|=(6031505241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2396493913/5000000000 : ℝ)|^8435 ≤ (1183156907119/3125000000000 : ℝ)^6387
        have hw : |(2396493913/5000000000 : ℝ)|=(2396493913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s0_1 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (551115949/1000000000 : ℝ)*x 0 + (-102743613/400000000 : ℝ)*x 1 + (4792987773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (551115949/1000000000 : ℝ)^8435 ≤ (45527331792951/100000000000000 : ℝ)^6387 := by
    have hnat : (551115949 : ℕ)^8435*100000000000000^6387 ≤ 45527331792951^6387*1000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551115949 1000000000 45527331792951 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (102743613/400000000 : ℝ)^8435 ≤ (332232954463/2000000000000 : ℝ)^6387 := by
    have hnat : (102743613 : ℕ)^8435*2000000000000^6387 ≤ 332232954463^6387*400000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102743613 400000000 332232954463 2000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4792987773/10000000000 : ℝ)^8435 ≤ (37861020474903/100000000000000 : ℝ)^6387 := by
    have hnat : (4792987773 : ℕ)^8435*100000000000000^6387 ≤ 37861020474903^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4792987773 10000000000 37861020474903 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(551115949/1000000000 : ℝ), (-102743613/400000000 : ℝ), (4792987773/10000000000 : ℝ)] ![(45527331792951/100000000000000 : ℝ), (332232954463/2000000000000 : ℝ), (37861020474903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(551115949/1000000000 : ℝ)|^8435 ≤ (45527331792951/100000000000000 : ℝ)^6387
        have hw : |(551115949/1000000000 : ℝ)|=(551115949/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-102743613/400000000 : ℝ)|^8435 ≤ (332232954463/2000000000000 : ℝ)^6387
        have hw : |(-102743613/400000000 : ℝ)|=(102743613/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4792987773/10000000000 : ℝ)|^8435 ≤ (37861020474903/100000000000000 : ℝ)^6387
        have hw : |(4792987773/10000000000 : ℝ)|=(4792987773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s0_2 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5511159413/10000000000 : ℝ)*x 0 + (4792987851/10000000000 : ℝ)*x 1 + (-2568590327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5511159413/10000000000 : ℝ)^8435 ≤ (9105466190579/20000000000000 : ℝ)^6387 := by
    have hnat : (5511159413 : ℕ)^8435*20000000000000^6387 ≤ 9105466190579^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5511159413 10000000000 9105466190579 20000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4792987851/10000000000 : ℝ)^8435 ≤ (9465255322153/25000000000000 : ℝ)^6387 := by
    have hnat : (4792987851 : ℕ)^8435*25000000000000^6387 ≤ 9465255322153^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4792987851 10000000000 9465255322153 25000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2568590327/10000000000 : ℝ)^8435 ≤ (2076455967529/12500000000000 : ℝ)^6387 := by
    have hnat : (2568590327 : ℕ)^8435*12500000000000^6387 ≤ 2076455967529^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2568590327 10000000000 2076455967529 12500000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5511159413/10000000000 : ℝ), (4792987851/10000000000 : ℝ), (-2568590327/10000000000 : ℝ)] ![(9105466190579/20000000000000 : ℝ), (9465255322153/25000000000000 : ℝ), (2076455967529/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5511159413/10000000000 : ℝ)|^8435 ≤ (9105466190579/20000000000000 : ℝ)^6387
        have hw : |(5511159413/10000000000 : ℝ)|=(5511159413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4792987851/10000000000 : ℝ)|^8435 ≤ (9465255322153/25000000000000 : ℝ)^6387
        have hw : |(4792987851/10000000000 : ℝ)|=(4792987851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2568590327/10000000000 : ℝ)|^8435 ≤ (2076455967529/12500000000000 : ℝ)^6387
        have hw : |(-2568590327/10000000000 : ℝ)|=(2568590327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s0_3 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4193021553/10000000000 : ℝ)*x 0 + (3116890957/10000000000 : ℝ)*x 1 + (5629310771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4193021553/10000000000 : ℝ)^8435 ≤ (7932862321823/25000000000000 : ℝ)^6387 := by
    have hnat : (4193021553 : ℕ)^8435*25000000000000^6387 ≤ 7932862321823^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4193021553 10000000000 7932862321823 25000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3116890957/10000000000 : ℝ)^8435 ≤ (21447801078591/100000000000000 : ℝ)^6387 := by
    have hnat : (3116890957 : ℕ)^8435*100000000000000^6387 ≤ 21447801078591^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3116890957 10000000000 21447801078591 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5629310771/10000000000 : ℝ)^8435 ≤ (11705187404929/25000000000000 : ℝ)^6387 := by
    have hnat : (5629310771 : ℕ)^8435*25000000000000^6387 ≤ 11705187404929^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5629310771 10000000000 11705187404929 25000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4193021553/10000000000 : ℝ), (3116890957/10000000000 : ℝ), (5629310771/10000000000 : ℝ)] ![(7932862321823/25000000000000 : ℝ), (21447801078591/100000000000000 : ℝ), (11705187404929/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4193021553/10000000000 : ℝ)|^8435 ≤ (7932862321823/25000000000000 : ℝ)^6387
        have hw : |(4193021553/10000000000 : ℝ)|=(4193021553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3116890957/10000000000 : ℝ)|^8435 ≤ (21447801078591/100000000000000 : ℝ)^6387
        have hw : |(3116890957/10000000000 : ℝ)|=(3116890957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5629310771/10000000000 : ℝ)|^8435 ≤ (11705187404929/25000000000000 : ℝ)^6387
        have hw : |(5629310771/10000000000 : ℝ)|=(5629310771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s0_4 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1865417607/10000000000 : ℝ)*x 0 + (4824882357/10000000000 : ℝ)*x 1 + (299924169/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1865417607/10000000000 : ℝ)^8435 ≤ (5444016822269/50000000000000 : ℝ)^6387 := by
    have hnat : (1865417607 : ℕ)^8435*50000000000000^6387 ≤ 5444016822269^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1865417607 10000000000 5444016822269 50000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4824882357/10000000000 : ℝ)^8435 ≤ (2387131516797/6250000000000 : ℝ)^6387 := by
    have hnat : (4824882357 : ℕ)^8435*6250000000000^6387 ≤ 2387131516797^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4824882357 10000000000 2387131516797 6250000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (299924169/500000000 : ℝ)^8435 ≤ (50917862077949/100000000000000 : ℝ)^6387 := by
    have hnat : (299924169 : ℕ)^8435*100000000000000^6387 ≤ 50917862077949^6387*500000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299924169 500000000 50917862077949 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1865417607/10000000000 : ℝ), (4824882357/10000000000 : ℝ), (299924169/500000000 : ℝ)] ![(5444016822269/50000000000000 : ℝ), (2387131516797/6250000000000 : ℝ), (50917862077949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1865417607/10000000000 : ℝ)|^8435 ≤ (5444016822269/50000000000000 : ℝ)^6387
        have hw : |(-1865417607/10000000000 : ℝ)|=(1865417607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4824882357/10000000000 : ℝ)|^8435 ≤ (2387131516797/6250000000000 : ℝ)^6387
        have hw : |(4824882357/10000000000 : ℝ)|=(4824882357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(299924169/500000000 : ℝ)|^8435 ≤ (50917862077949/100000000000000 : ℝ)^6387
        have hw : |(299924169/500000000 : ℝ)|=(299924169/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s0_5 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5174176349/10000000000 : ℝ)*x 0 + (-21298321/156250000 : ℝ)*x 1 + (5998485661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5174176349/10000000000 : ℝ)^8435 ≤ (1308983158311/3125000000000 : ℝ)^6387 := by
    have hnat : (5174176349 : ℕ)^8435*3125000000000^6387 ≤ 1308983158311^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174176349 10000000000 1308983158311 3125000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21298321/156250000 : ℝ)^8435 ≤ (57557210161/800000000000 : ℝ)^6387 := by
    have hnat : (21298321 : ℕ)^8435*800000000000^6387 ≤ 57557210161^6387*156250000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21298321 156250000 57557210161 800000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5998485661/10000000000 : ℝ)^8435 ≤ (3182367978039/6250000000000 : ℝ)^6387 := by
    have hnat : (5998485661 : ℕ)^8435*6250000000000^6387 ≤ 3182367978039^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5998485661 10000000000 3182367978039 6250000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5174176349/10000000000 : ℝ), (-21298321/156250000 : ℝ), (5998485661/10000000000 : ℝ)] ![(1308983158311/3125000000000 : ℝ), (57557210161/800000000000 : ℝ), (3182367978039/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5174176349/10000000000 : ℝ)|^8435 ≤ (1308983158311/3125000000000 : ℝ)^6387
        have hw : |(5174176349/10000000000 : ℝ)|=(5174176349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-21298321/156250000 : ℝ)|^8435 ≤ (57557210161/800000000000 : ℝ)^6387
        have hw : |(-21298321/156250000 : ℝ)|=(21298321/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5998485661/10000000000 : ℝ)|^8435 ≤ (3182367978039/6250000000000 : ℝ)^6387
        have hw : |(5998485661/10000000000 : ℝ)|=(5998485661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s0_6 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2587088627/5000000000 : ℝ)*x 0 + (5998483837/10000000000 : ℝ)*x 1 + (-1363094089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2587088627/5000000000 : ℝ)^8435 ≤ (41887470741589/100000000000000 : ℝ)^6387 := by
    have hnat : (2587088627 : ℕ)^8435*100000000000000^6387 ≤ 41887470741589^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587088627 5000000000 41887470741589 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5998483837/10000000000 : ℝ)^8435 ≤ (12729466800263/25000000000000 : ℝ)^6387 := by
    have hnat : (5998483837 : ℕ)^8435*25000000000000^6387 ≤ 12729466800263^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5998483837 10000000000 12729466800263 25000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1363094089/10000000000 : ℝ)^8435 ≤ (1798665509941/25000000000000 : ℝ)^6387 := by
    have hnat : (1363094089 : ℕ)^8435*25000000000000^6387 ≤ 1798665509941^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363094089 10000000000 1798665509941 25000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2587088627/5000000000 : ℝ), (5998483837/10000000000 : ℝ), (-1363094089/10000000000 : ℝ)] ![(41887470741589/100000000000000 : ℝ), (12729466800263/25000000000000 : ℝ), (1798665509941/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2587088627/5000000000 : ℝ)|^8435 ≤ (41887470741589/100000000000000 : ℝ)^6387
        have hw : |(2587088627/5000000000 : ℝ)|=(2587088627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5998483837/10000000000 : ℝ)|^8435 ≤ (12729466800263/25000000000000 : ℝ)^6387
        have hw : |(5998483837/10000000000 : ℝ)|=(5998483837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1363094089/10000000000 : ℝ)|^8435 ≤ (1798665509941/25000000000000 : ℝ)^6387
        have hw : |(-1363094089/10000000000 : ℝ)|=(1363094089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s0_7 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4202876349/10000000000 : ℝ)*x 0 + (5564615703/10000000000 : ℝ)*x 1 + (3183872301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4202876349/10000000000 : ℝ)^8435 ≤ (6365995570203/20000000000000 : ℝ)^6387 := by
    have hnat : (4202876349 : ℕ)^8435*20000000000000^6387 ≤ 6365995570203^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4202876349 10000000000 6365995570203 20000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5564615703/10000000000 : ℝ)^8435 ≤ (23055717069157/50000000000000 : ℝ)^6387 := by
    have hnat : (5564615703 : ℕ)^8435*50000000000000^6387 ≤ 23055717069157^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5564615703 10000000000 23055717069157 50000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3183872301/10000000000 : ℝ)^8435 ≤ (22058588004073/100000000000000 : ℝ)^6387 := by
    have hnat : (3183872301 : ℕ)^8435*100000000000000^6387 ≤ 22058588004073^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3183872301 10000000000 22058588004073 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4202876349/10000000000 : ℝ), (5564615703/10000000000 : ℝ), (3183872301/10000000000 : ℝ)] ![(6365995570203/20000000000000 : ℝ), (23055717069157/50000000000000 : ℝ), (22058588004073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4202876349/10000000000 : ℝ)|^8435 ≤ (6365995570203/20000000000000 : ℝ)^6387
        have hw : |(4202876349/10000000000 : ℝ)|=(4202876349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5564615703/10000000000 : ℝ)|^8435 ≤ (23055717069157/50000000000000 : ℝ)^6387
        have hw : |(5564615703/10000000000 : ℝ)|=(5564615703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3183872301/10000000000 : ℝ)|^8435 ≤ (22058588004073/100000000000000 : ℝ)^6387
        have hw : |(3183872301/10000000000 : ℝ)|=(3183872301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1242_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151428527/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (409/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6859/25000 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (4217/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4217 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4217*1^1024 ≤ 0^1024*1^4217 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4217 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4217/1024 : ℝ) ≤ (459460047262876589/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4217 ≤ (459460047262876589/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4217*20000000000000000000^1024 ≤ 459460047262876589^1024*5^4217 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 459460047262876589 20000000000000000000 4217 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (459460047262876589/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4217/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4217 := by
      have hnat : (1 : ℕ)^1024*1^4217 ≤ 1^4217*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4217 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20459460047262876589/20000000000000000000 : ℝ) ≤ (10055305826129433/10000000000000000 : ℝ) ^ (4217/1024 : ℝ) := by
    have hpowers : (20459460047262876589/20000000000000000000 : ℝ)^1024 ≤ (10055305826129433/10000000000000000 : ℝ)^4217 := by
      have hnat : (20459460047262876589 : ℕ)^1024*10000000000000000^4217 ≤ 10055305826129433^4217*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20459460047262876589 20000000000000000000 10055305826129433 10000000000000000 1024 4217 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10055305826129433/10000000000000000 : ℝ)) (X := (20459460047262876589/20000000000000000000 : ℝ)) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10459460047262876589/10000000000000000000 : ℝ) ≤ (5055305826129433/5000000000000000 : ℝ) ^ (4217/1024 : ℝ) := by
    have hpowers : (10459460047262876589/10000000000000000000 : ℝ)^1024 ≤ (5055305826129433/5000000000000000 : ℝ)^4217 := by
      have hnat : (10459460047262876589 : ℕ)^1024*5000000000000000^4217 ≤ 5055305826129433^4217*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10459460047262876589 10000000000000000000 5055305826129433 5000000000000000 1024 4217 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5055305826129433/5000000000000000 : ℝ)) (X := (10459460047262876589/10000000000000000000 : ℝ)) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(55305826129433/4000000000000000 : ℝ)*(0 : ℝ))^(4217/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(55305826129433/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(459460047262876589/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(55305826129433/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4217/1024 : ℝ) := by
    rw [show (1 : ℝ)+(55305826129433/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10055305826129433/10000000000000000 : ℝ) by norm_num, show 1+(459460047262876589/20000000000000000000 : ℝ)+(0 : ℝ)=(20459460047262876589/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(459460047262876589/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(55305826129433/4000000000000000 : ℝ)*(2/5 : ℝ))^(4217/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(55305826129433/4000000000000000 : ℝ)*(2/5 : ℝ)=(5055305826129433/5000000000000000 : ℝ) by norm_num, show 1+2*(459460047262876589/20000000000000000000 : ℝ)=(10459460047262876589/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(55305826129433/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4217/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (55305826129433/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(55305826129433/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4217/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (55305826129433/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(55305826129433/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4217/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (55305826129433/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1860560099/10000000000 : ℝ)*X 0 0+(6031505241/10000000000 : ℝ)*X 0 1+(2396493913/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((551115949/1000000000 : ℝ)*X 1 0+(-102743613/400000000 : ℝ)*X 1 1+(4792987773/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5511159413/10000000000 : ℝ)*X 2 0+(4792987851/10000000000 : ℝ)*X 2 1+(-2568590327/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4193021553/10000000000 : ℝ)*X 0 0+(3116890957/10000000000 : ℝ)*X 0 1+(5629310771/10000000000 : ℝ)*X 0 2+(4193021553/10000000000 : ℝ)*X 1 0+(3116890957/10000000000 : ℝ)*X 1 1+(5629310771/10000000000 : ℝ)*X 1 2+(4193021553/10000000000 : ℝ)*X 2 0+(3116890957/10000000000 : ℝ)*X 2 1+(5629310771/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1865417607/10000000000 : ℝ)*X 0 0+(4824882357/10000000000 : ℝ)*X 0 1+(299924169/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5174176349/10000000000 : ℝ)*X 1 0+(-21298321/156250000 : ℝ)*X 1 1+(5998485661/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2587088627/5000000000 : ℝ)*X 2 0+(5998483837/10000000000 : ℝ)*X 2 1+(-1363094089/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4202876349/10000000000 : ℝ)*X 0 0+(5564615703/10000000000 : ℝ)*X 0 1+(3183872301/10000000000 : ℝ)*X 0 2+(4202876349/10000000000 : ℝ)*X 1 0+(5564615703/10000000000 : ℝ)*X 1 1+(3183872301/10000000000 : ℝ)*X 1 2+(4202876349/10000000000 : ℝ)*X 2 0+(5564615703/10000000000 : ℝ)*X 2 1+(3183872301/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13408112733401369177367/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (66741427/100000000000000 : ℝ)*(base1) + (654090913/50000000000000 : ℝ)*(base19) + (1210179893/100000000000000 : ℝ)*(base23) + (86720899/100000000000000 : ℝ)*(base24) + (146730889/50000000000000 : ℝ)*(upper3) + (37670336298467/6250000000000 : ℝ)*(major0) + (37670336298467/6250000000000 : ℝ)*(major1) + (37670336298467/6250000000000 : ℝ)*(major2) + (201855355639243/25000000000000 : ℝ)*(sp0) + (80742296296313/10000000000000 : ℝ)*(sp1) + (807422974244163/100000000000000 : ℝ)*(sp2) + (398023984394809/100000000000000 : ℝ)*(sp3) + (2915329411/100000000000000 : ℝ)*(sp4) + (565123727/25000000000000 : ℝ)*(sp7) + (49753288953893/12500000000000 : ℝ)*(f.failure) + (161484854228991/20000000000000 : ℝ)*(f.sum) + (15548741929211/12500000000000000000000000000 : ℝ)*base65 + (6747498579211/25000000000000000000000000000 : ℝ)*base67 + (133380784004211/25000000000000000000000000000 : ℝ)*base69 + (82455537254211/25000000000000000000000000000 : ℝ)*base71 + (11501045391711/12500000000000000000000000000 : ℝ)*base73 + (22711651945789/25000000000000000000000000000 : ℝ)*base76 + (6001721779211/25000000000000000000000000000 : ℝ)*base77 + (82985705229211/25000000000000000000000000000 : ℝ)*base79 + (20420364654211/12500000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (12094389/1250000000000000000000 : ℝ)*base90 + (12094389/1250000000000000000000 : ℝ)*base92 + (12094389/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1857538071209563953/500000000000000000000000 : ℝ) := by norm_num
    linear_combination (58879647/50000000000000 : ℝ)*(base1) + (456069713/50000000000000 : ℝ)*(base19) + (1037120991/100000000000000 : ℝ)*(base23) + (13643367/6250000000000 : ℝ)*(upper3) + (39753597948123/6250000000000 : ℝ)*(major0) + (39753597948123/6250000000000 : ℝ)*(major1) + (39753597948123/6250000000000 : ℝ)*(major2) + (2243231183/100000000000000 : ℝ)*(sp1) + (187392449/10000000000000 : ℝ)*(sp2) + (258792063/100000000000000 : ℝ)*(sp3) + (852076988970109/100000000000000 : ℝ)*(sp4) + (426036857920103/50000000000000 : ℝ)*(sp5) + (852073960165333/100000000000000 : ℝ)*(sp6) + (420037762741887/100000000000000 : ℝ)*(sp7) + (105009534823311/25000000000000 : ℝ)*(f.failure) + (170415374242163/20000000000000 : ℝ)*(f.sum) + (429123083241/12500000000000000000000000000 : ℝ)*base66 + (71142998279259/25000000000000000000000000000 : ℝ)*base67 + (66898957095741/25000000000000000000000000000 : ℝ)*base70 + (4170406745741/25000000000000000000000000000 : ℝ)*base72 + (15632850991759/12500000000000000000000000000 : ℝ)*base73 + (77192962779259/25000000000000000000000000000 : ℝ)*base75 + (60834708554259/25000000000000000000000000000 : ℝ)*base77 + (231264828329259/25000000000000000000000000000 : ℝ)*base79 + (51261653758241/12500000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (10007103/2500000000000000000000 : ℝ)*base90 + (10007103/2500000000000000000000 : ℝ)*base92 + (10007103/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1242_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151428527/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (409/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6859/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1242_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1242_s1_0 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2057972669/10000000000 : ℝ)*x 0 + (5675602007/10000000000 : ℝ)*x 1 + (5022524733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2057972669/10000000000 : ℝ)^8435 ≤ (12396329261711/100000000000000 : ℝ)^6387 := by
    have hnat : (2057972669 : ℕ)^8435*100000000000000^6387 ≤ 12396329261711^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2057972669 10000000000 12396329261711 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5675602007/10000000000 : ℝ)^8435 ≤ (9465978862259/20000000000000 : ℝ)^6387 := by
    have hnat : (5675602007 : ℕ)^8435*20000000000000^6387 ≤ 9465978862259^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5675602007 10000000000 9465978862259 20000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5022524733/10000000000 : ℝ)^8435 ≤ (1006844410269/2500000000000 : ℝ)^6387 := by
    have hnat : (5022524733 : ℕ)^8435*2500000000000^6387 ≤ 1006844410269^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5022524733 10000000000 1006844410269 2500000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2057972669/10000000000 : ℝ), (5675602007/10000000000 : ℝ), (5022524733/10000000000 : ℝ)] ![(12396329261711/100000000000000 : ℝ), (9465978862259/20000000000000 : ℝ), (1006844410269/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2057972669/10000000000 : ℝ)|^8435 ≤ (12396329261711/100000000000000 : ℝ)^6387
        have hw : |(-2057972669/10000000000 : ℝ)|=(2057972669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5675602007/10000000000 : ℝ)|^8435 ≤ (9465978862259/20000000000000 : ℝ)^6387
        have hw : |(5675602007/10000000000 : ℝ)|=(5675602007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5022524733/10000000000 : ℝ)|^8435 ≤ (1006844410269/2500000000000 : ℝ)^6387
        have hw : |(5022524733/10000000000 : ℝ)|=(5022524733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s1_1 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5413657269/10000000000 : ℝ)*x 0 + (-1204334009/5000000000 : ℝ)*x 1 + (627815617/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5413657269/10000000000 : ℝ)^8435 ≤ (44466629985983/100000000000000 : ℝ)^6387 := by
    have hnat : (5413657269 : ℕ)^8435*100000000000000^6387 ≤ 44466629985983^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413657269 10000000000 44466629985983 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1204334009/5000000000 : ℝ)^8435 ≤ (15259591442119/100000000000000 : ℝ)^6387 := by
    have hnat : (1204334009 : ℕ)^8435*100000000000000^6387 ≤ 15259591442119^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1204334009 5000000000 15259591442119 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (627815617/1250000000 : ℝ)^8435 ≤ (10068444640123/25000000000000 : ℝ)^6387 := by
    have hnat : (627815617 : ℕ)^8435*25000000000000^6387 ≤ 10068444640123^6387*1250000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      627815617 1250000000 10068444640123 25000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5413657269/10000000000 : ℝ), (-1204334009/5000000000 : ℝ), (627815617/1250000000 : ℝ)] ![(44466629985983/100000000000000 : ℝ), (15259591442119/100000000000000 : ℝ), (10068444640123/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5413657269/10000000000 : ℝ)|^8435 ≤ (44466629985983/100000000000000 : ℝ)^6387
        have hw : |(5413657269/10000000000 : ℝ)|=(5413657269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1204334009/5000000000 : ℝ)|^8435 ≤ (15259591442119/100000000000000 : ℝ)^6387
        have hw : |(-1204334009/5000000000 : ℝ)|=(1204334009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(627815617/1250000000 : ℝ)|^8435 ≤ (10068444640123/25000000000000 : ℝ)^6387
        have hw : |(627815617/1250000000 : ℝ)|=(627815617/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s1_2 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2706828729/5000000000 : ℝ)*x 0 + (5022524801/10000000000 : ℝ)*x 1 + (-2408667943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2706828729/5000000000 : ℝ)^8435 ≤ (4446663203617/10000000000000 : ℝ)^6387 := by
    have hnat : (2706828729 : ℕ)^8435*10000000000000^6387 ≤ 4446663203617^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706828729 5000000000 4446663203617 10000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5022524801/10000000000 : ℝ)^8435 ≤ (40273777130867/100000000000000 : ℝ)^6387 := by
    have hnat : (5022524801 : ℕ)^8435*100000000000000^6387 ≤ 40273777130867^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5022524801 10000000000 40273777130867 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2408667943/10000000000 : ℝ)^8435 ≤ (15259590814617/100000000000000 : ℝ)^6387 := by
    have hnat : (2408667943 : ℕ)^8435*100000000000000^6387 ≤ 15259590814617^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2408667943 10000000000 15259590814617 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2706828729/5000000000 : ℝ), (5022524801/10000000000 : ℝ), (-2408667943/10000000000 : ℝ)] ![(4446663203617/10000000000000 : ℝ), (40273777130867/100000000000000 : ℝ), (15259590814617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2706828729/5000000000 : ℝ)|^8435 ≤ (4446663203617/10000000000000 : ℝ)^6387
        have hw : |(2706828729/5000000000 : ℝ)|=(2706828729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5022524801/10000000000 : ℝ)|^8435 ≤ (40273777130867/100000000000000 : ℝ)^6387
        have hw : |(5022524801/10000000000 : ℝ)|=(5022524801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2408667943/10000000000 : ℝ)|^8435 ≤ (15259590814617/100000000000000 : ℝ)^6387
        have hw : |(-2408667943/10000000000 : ℝ)|=(2408667943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s1_3 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4308856419/10000000000 : ℝ)*x 0 + (1847726493/5000000000 : ℝ)*x 1 + (1004053373/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4308856419/10000000000 : ℝ)^8435 ≤ (131576919009/400000000000 : ℝ)^6387 := by
    have hnat : (4308856419 : ℕ)^8435*400000000000^6387 ≤ 131576919009^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4308856419 10000000000 131576919009 400000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1847726493/5000000000 : ℝ)^8435 ≤ (3356987812953/12500000000000 : ℝ)^6387 := by
    have hnat : (1847726493 : ℕ)^8435*12500000000000^6387 ≤ 3356987812953^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1847726493 5000000000 3356987812953 12500000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1004053373/2000000000 : ℝ)^8435 ≤ (10062466931523/25000000000000 : ℝ)^6387 := by
    have hnat : (1004053373 : ℕ)^8435*25000000000000^6387 ≤ 10062466931523^6387*2000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004053373 2000000000 10062466931523 25000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4308856419/10000000000 : ℝ), (1847726493/5000000000 : ℝ), (1004053373/2000000000 : ℝ)] ![(131576919009/400000000000 : ℝ), (3356987812953/12500000000000 : ℝ), (10062466931523/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4308856419/10000000000 : ℝ)|^8435 ≤ (131576919009/400000000000 : ℝ)^6387
        have hw : |(4308856419/10000000000 : ℝ)|=(4308856419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1847726493/5000000000 : ℝ)|^8435 ≤ (3356987812953/12500000000000 : ℝ)^6387
        have hw : |(1847726493/5000000000 : ℝ)|=(1847726493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1004053373/2000000000 : ℝ)|^8435 ≤ (10062466931523/25000000000000 : ℝ)^6387
        have hw : |(1004053373/2000000000 : ℝ)|=(1004053373/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s1_4 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2058649531/10000000000 : ℝ)*x 0 + (5031103687/10000000000 : ℝ)*x 1 + (1416714867/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2058649531/10000000000 : ℝ)^8435 ≤ (12401714001263/100000000000000 : ℝ)^6387 := by
    have hnat : (2058649531 : ℕ)^8435*100000000000000^6387 ≤ 12401714001263^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2058649531 10000000000 12401714001263 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5031103687/10000000000 : ℝ)^8435 ≤ (10091162707611/25000000000000 : ℝ)^6387 := by
    have hnat : (5031103687 : ℕ)^8435*25000000000000^6387 ≤ 10091162707611^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5031103687 10000000000 10091162707611 25000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1416714867/2500000000 : ℝ)^8435 ≤ (47233635156147/100000000000000 : ℝ)^6387 := by
    have hnat : (1416714867 : ℕ)^8435*100000000000000^6387 ≤ 47233635156147^6387*2500000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1416714867 2500000000 47233635156147 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2058649531/10000000000 : ℝ), (5031103687/10000000000 : ℝ), (1416714867/2500000000 : ℝ)] ![(12401714001263/100000000000000 : ℝ), (10091162707611/25000000000000 : ℝ), (47233635156147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2058649531/10000000000 : ℝ)|^8435 ≤ (12401714001263/100000000000000 : ℝ)^6387
        have hw : |(-2058649531/10000000000 : ℝ)|=(2058649531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5031103687/10000000000 : ℝ)|^8435 ≤ (10091162707611/25000000000000 : ℝ)^6387
        have hw : |(5031103687/10000000000 : ℝ)|=(5031103687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1416714867/2500000000 : ℝ)|^8435 ≤ (47233635156147/100000000000000 : ℝ)^6387
        have hw : |(1416714867/2500000000 : ℝ)|=(1416714867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s1_5 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2622702857/5000000000 : ℝ)*x 0 + (-1764332907/10000000000 : ℝ)*x 1 + (1416714893/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2622702857/5000000000 : ℝ)^8435 ≤ (21325335981331/50000000000000 : ℝ)^6387 := by
    have hnat : (2622702857 : ℕ)^8435*50000000000000^6387 ≤ 21325335981331^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622702857 5000000000 21325335981331 50000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1764332907/10000000000 : ℝ)^8435 ≤ (5057845863751/50000000000000 : ℝ)^6387 := by
    have hnat : (1764332907 : ℕ)^8435*50000000000000^6387 ≤ 5057845863751^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1764332907 10000000000 5057845863751 50000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1416714893/2500000000 : ℝ)^8435 ≤ (47233636300949/100000000000000 : ℝ)^6387 := by
    have hnat : (1416714893 : ℕ)^8435*100000000000000^6387 ≤ 47233636300949^6387*2500000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1416714893 2500000000 47233636300949 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2622702857/5000000000 : ℝ), (-1764332907/10000000000 : ℝ), (1416714893/2500000000 : ℝ)] ![(21325335981331/50000000000000 : ℝ), (5057845863751/50000000000000 : ℝ), (47233636300949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2622702857/5000000000 : ℝ)|^8435 ≤ (21325335981331/50000000000000 : ℝ)^6387
        have hw : |(2622702857/5000000000 : ℝ)|=(2622702857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1764332907/10000000000 : ℝ)|^8435 ≤ (5057845863751/50000000000000 : ℝ)^6387
        have hw : |(-1764332907/10000000000 : ℝ)|=(1764332907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1416714893/2500000000 : ℝ)|^8435 ≤ (47233636300949/100000000000000 : ℝ)^6387
        have hw : |(1416714893/2500000000 : ℝ)|=(1416714893/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s1_6 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5245406089/10000000000 : ℝ)*x 0 + (1416715087/2500000000 : ℝ)*x 1 + (-1764331247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5245406089/10000000000 : ℝ)^8435 ≤ (42650675989519/100000000000000 : ℝ)^6387 := by
    have hnat : (5245406089 : ℕ)^8435*100000000000000^6387 ≤ 42650675989519^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245406089 10000000000 42650675989519 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1416715087/2500000000 : ℝ)^8435 ≤ (9446728968587/20000000000000 : ℝ)^6387 := by
    have hnat : (1416715087 : ℕ)^8435*20000000000000^6387 ≤ 9446728968587^6387*2500000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1416715087 2500000000 9446728968587 20000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1764331247/10000000000 : ℝ)^8435 ≤ (5057839579099/50000000000000 : ℝ)^6387 := by
    have hnat : (1764331247 : ℕ)^8435*50000000000000^6387 ≤ 5057839579099^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1764331247 10000000000 5057839579099 50000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5245406089/10000000000 : ℝ), (1416715087/2500000000 : ℝ), (-1764331247/10000000000 : ℝ)] ![(42650675989519/100000000000000 : ℝ), (9446728968587/20000000000000 : ℝ), (5057839579099/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5245406089/10000000000 : ℝ)|^8435 ≤ (42650675989519/100000000000000 : ℝ)^6387
        have hw : |(5245406089/10000000000 : ℝ)|=(5245406089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1416715087/2500000000 : ℝ)|^8435 ≤ (9446728968587/20000000000000 : ℝ)^6387
        have hw : |(1416715087/2500000000 : ℝ)|=(1416715087/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1764331247/10000000000 : ℝ)|^8435 ≤ (5057839579099/50000000000000 : ℝ)^6387
        have hw : |(-1764331247/10000000000 : ℝ)|=(1764331247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s1_7 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (538778487/1250000000 : ℝ)*x 0 + (1250716151/2500000000 : ℝ)*x 1 + (1856593289/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538778487/1250000000 : ℝ)^8435 ≤ (32908057662703/100000000000000 : ℝ)^6387 := by
    have hnat : (538778487 : ℕ)^8435*100000000000000^6387 ≤ 32908057662703^6387*1250000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538778487 1250000000 32908057662703 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1250716151/2500000000 : ℝ)^8435 ≤ (40065710024963/100000000000000 : ℝ)^6387 := by
    have hnat : (1250716151 : ℕ)^8435*100000000000000^6387 ≤ 40065710024963^6387*2500000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1250716151 2500000000 40065710024963 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1856593289/5000000000 : ℝ)^8435 ≤ (27026232286717/100000000000000 : ℝ)^6387 := by
    have hnat : (1856593289 : ℕ)^8435*100000000000000^6387 ≤ 27026232286717^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1856593289 5000000000 27026232286717 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538778487/1250000000 : ℝ), (1250716151/2500000000 : ℝ), (1856593289/5000000000 : ℝ)] ![(32908057662703/100000000000000 : ℝ), (40065710024963/100000000000000 : ℝ), (27026232286717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538778487/1250000000 : ℝ)|^8435 ≤ (32908057662703/100000000000000 : ℝ)^6387
        have hw : |(538778487/1250000000 : ℝ)|=(538778487/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1250716151/2500000000 : ℝ)|^8435 ≤ (40065710024963/100000000000000 : ℝ)^6387
        have hw : |(1250716151/2500000000 : ℝ)|=(1250716151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1856593289/5000000000 : ℝ)|^8435 ≤ (27026232286717/100000000000000 : ℝ)^6387
        have hw : |(1856593289/5000000000 : ℝ)|=(1856593289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1242_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151428527/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6859/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (409/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (6191/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19999/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6859/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (409/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6859/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (409/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6859/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (409/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6859/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (409/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6859/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (409/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6859/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (409/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (409/50000 : ℝ) ^ (4217/1024 : ℝ) ≤ (253732247061/100000000000000000000 : ℝ) := by
    have hpowers : (409/50000 : ℝ)^4217 ≤ (253732247061/100000000000000000000 : ℝ)^1024 := by
      have hnat : (409 : ℕ)^4217*100000000000000000000^1024 ≤ 253732247061^1024*50000^4217 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        409 50000 253732247061 100000000000000000000 4217 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (409/50000 : ℝ)) (X := (253732247061/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (6859/25000 : ℝ) ^ (4217/1024 : ℝ) ≤ (243154820781409731/50000000000000000000 : ℝ) := by
    have hpowers : (6859/25000 : ℝ)^4217 ≤ (243154820781409731/50000000000000000000 : ℝ)^1024 := by
      have hnat : (6859 : ℕ)^4217*50000000000000000000^1024 ≤ 243154820781409731^1024*25000^4217 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6859 25000 243154820781409731 50000000000000000000 4217 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6859/25000 : ℝ)) (X := (243154820781409731/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000253732247061/50000000000000000000 : ℝ) ≤ (10000000012322591/10000000000000000 : ℝ) ^ (4217/1024 : ℝ) := by
    have hpowers : (50000000253732247061/50000000000000000000 : ℝ)^1024 ≤ (10000000012322591/10000000000000000 : ℝ)^4217 := by
      have hnat : (50000000253732247061 : ℕ)^1024*10000000000000000^4217 ≤ 10000000012322591^4217*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000253732247061 50000000000000000000 10000000012322591 10000000000000000 1024 4217 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000012322591/10000000000000000 : ℝ)) (X := (50000000253732247061/50000000000000000000 : ℝ)) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100486309895295066523/100000000000000000000 : ℝ) ≤ (1001178722077207/1000000000000000 : ℝ) ^ (4217/1024 : ℝ) := by
    have hpowers : (100486309895295066523/100000000000000000000 : ℝ)^1024 ≤ (1001178722077207/1000000000000000 : ℝ)^4217 := by
      have hnat : (100486309895295066523 : ℕ)^1024*1000000000000000^4217 ≤ 1001178722077207^4217*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100486309895295066523 100000000000000000000 1001178722077207 1000000000000000 1024 4217 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1001178722077207/1000000000000000 : ℝ)) (X := (100486309895295066523/100000000000000000000 : ℝ)) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25243154820781409731/25000000000000000000 : ℝ) ≤ (10023574429221549/10000000000000000 : ℝ) ^ (4217/1024 : ℝ) := by
    have hpowers : (25243154820781409731/25000000000000000000 : ℝ)^1024 ≤ (10023574429221549/10000000000000000 : ℝ)^4217 := by
      have hnat : (25243154820781409731 : ℕ)^1024*10000000000000000^4217 ≤ 10023574429221549^4217*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25243154820781409731 25000000000000000000 10023574429221549 10000000000000000 1024 4217 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10023574429221549/10000000000000000 : ℝ)) (X := (25243154820781409731/25000000000000000000 : ℝ)) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(253732247061/100000000000000000000 : ℝ) ≤ ((133080358227489689797/133090000000000000000 : ℝ)+2*(11787208449479/2661800000000000 : ℝ)*(409/50000 : ℝ))^(4217/1024 : ℝ) := by
    rw [show (133080358227489689797/133090000000000000000 : ℝ)+2*(11787208449479/2661800000000000 : ℝ)*(409/50000 : ℝ)=(10000000012322591/10000000000000000 : ℝ) by norm_num, show 1+2*(253732247061/100000000000000000000 : ℝ)=(50000000253732247061/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(243154820781409731/50000000000000000000 : ℝ)+(253732247061/100000000000000000000 : ℝ) ≤ ((133080358227489689797/133090000000000000000 : ℝ)+(11787208449479/2661800000000000 : ℝ)*((6859/25000 : ℝ)+(409/50000 : ℝ)))^(4217/1024 : ℝ) := by
    rw [show (133080358227489689797/133090000000000000000 : ℝ)+(11787208449479/2661800000000000 : ℝ)*((6859/25000 : ℝ)+(409/50000 : ℝ))=(1001178722077207/1000000000000000 : ℝ) by norm_num, show 1+(243154820781409731/50000000000000000000 : ℝ)+(253732247061/100000000000000000000 : ℝ)=(100486309895295066523/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(243154820781409731/50000000000000000000 : ℝ) ≤ ((133080358227489689797/133090000000000000000 : ℝ)+2*(11787208449479/2661800000000000 : ℝ)*(6859/25000 : ℝ))^(4217/1024 : ℝ) := by
    rw [show (133080358227489689797/133090000000000000000 : ℝ)+2*(11787208449479/2661800000000000 : ℝ)*(6859/25000 : ℝ)=(10023574429221549/10000000000000000 : ℝ) by norm_num, show 1+2*(243154820781409731/50000000000000000000 : ℝ)=(25243154820781409731/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (133080358227489689797/133090000000000000000 : ℝ)*(X 1 0+X 2 0)+(11787208449479/2661800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4217/1024 : ℝ)) (lo := (409/50000 : ℝ)) (hi := (6859/25000 : ℝ)) (c := (133080358227489689797/133090000000000000000 : ℝ)) (alpha := (11787208449479/2661800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (133080358227489689797/133090000000000000000 : ℝ)*(X 0 1+X 2 1)+(11787208449479/2661800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4217/1024 : ℝ)) (lo := (409/50000 : ℝ)) (hi := (6859/25000 : ℝ)) (c := (133080358227489689797/133090000000000000000 : ℝ)) (alpha := (11787208449479/2661800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (133080358227489689797/133090000000000000000 : ℝ)*(X 0 2+X 1 2)+(11787208449479/2661800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4217/1024 : ℝ)) (lo := (409/50000 : ℝ)) (hi := (6859/25000 : ℝ)) (c := (133080358227489689797/133090000000000000000 : ℝ)) (alpha := (11787208449479/2661800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2057972669/10000000000 : ℝ)*X 0 0+(5675602007/10000000000 : ℝ)*X 0 1+(5022524733/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5413657269/10000000000 : ℝ)*X 1 0+(-1204334009/5000000000 : ℝ)*X 1 1+(627815617/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2706828729/5000000000 : ℝ)*X 2 0+(5022524801/10000000000 : ℝ)*X 2 1+(-2408667943/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4308856419/10000000000 : ℝ)*X 0 0+(1847726493/5000000000 : ℝ)*X 0 1+(1004053373/2000000000 : ℝ)*X 0 2+(4308856419/10000000000 : ℝ)*X 1 0+(1847726493/5000000000 : ℝ)*X 1 1+(1004053373/2000000000 : ℝ)*X 1 2+(4308856419/10000000000 : ℝ)*X 2 0+(1847726493/5000000000 : ℝ)*X 2 1+(1004053373/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2058649531/10000000000 : ℝ)*X 0 0+(5031103687/10000000000 : ℝ)*X 0 1+(1416714867/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2622702857/5000000000 : ℝ)*X 1 0+(-1764332907/10000000000 : ℝ)*X 1 1+(1416714893/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5245406089/10000000000 : ℝ)*X 2 0+(1416715087/2500000000 : ℝ)*X 2 1+(-1764331247/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((538778487/1250000000 : ℝ)*X 0 0+(1250716151/2500000000 : ℝ)*X 0 1+(1856593289/5000000000 : ℝ)*X 0 2+(538778487/1250000000 : ℝ)*X 1 0+(1250716151/2500000000 : ℝ)*X 1 1+(1856593289/5000000000 : ℝ)*X 1 2+(538778487/1250000000 : ℝ)*X 2 0+(1250716151/2500000000 : ℝ)*X 2 1+(1856593289/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9785988846725305131884714691/1663625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14716647/25000000000000 : ℝ)*(base1) + (657574013/50000000000000 : ℝ)*(base19) + (1368605741/100000000000000 : ℝ)*(base23) + (7019771/5000000000000 : ℝ)*(upper3) + (18214791/10000000000000 : ℝ)*(upper5) + (285757333447233/25000000000000 : ℝ)*(major0) + (285757333447233/25000000000000 : ℝ)*(major1) + (285757333447233/25000000000000 : ℝ)*(major2) + (765609806320949/50000000000000 : ℝ)*(sp0) + (191403280345363/12500000000000 : ℝ)*(sp1) + (1531226189305189/100000000000000 : ℝ)*(sp2) + (754826946233643/100000000000000 : ℝ)*(sp3) + (400206781/5000000000000 : ℝ)*(sp4) + (156339563/4000000000000 : ℝ)*(sp7) + (188707728397327/25000000000000 : ℝ)*(f.failure) + (153122755791093/10000000000000 : ℝ)*(f.sum) + (32668554727139/66545000000000000000000000000 : ℝ)*base65 + (16865507411189331701/3327250000000000000000000000000000 : ℝ)*base67 + (29477254174880581701/3327250000000000000000000000000000 : ℝ)*base69 + (26253808206159081701/3327250000000000000000000000000000 : ℝ)*base71 + (82429626442989/16636250000000000000000000000 : ℝ)*base74 + (24999904444443081701/3327250000000000000000000000000000 : ℝ)*base75 + (18318981121840581701/3327250000000000000000000000000000 : ℝ)*base77 + (34102751381847581701/3327250000000000000000000000000000 : ℝ)*base79 + (287876347061/1039765625000000000000000000 : ℝ)*base81 + (1652671/2500000000000000000000 : ℝ)*base90 + (1652671/2500000000000000000000 : ℝ)*base92 + (1652671/2500000000000000000000 : ℝ)*base94 + (1/50000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21594108960837697947855994803/3327250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2043282733/100000000000000 : ℝ)*(base19) + (2496510133/100000000000000 : ℝ)*(base23) + (81332557/100000000000000 : ℝ)*(upper2) + (1211031/400000000000 : ℝ)*(upper3) + (76307233/50000000000000 : ℝ)*(upper5) + (587079499061311/50000000000000 : ℝ)*(major0) + (587079499061311/50000000000000 : ℝ)*(major1) + (587079499061311/50000000000000 : ℝ)*(major2) + (9296160483/100000000000000 : ℝ)*(sp1) + (15086247779/100000000000000 : ℝ)*(sp2) + (314585906957041/20000000000000 : ℝ)*(sp4) + (1572918195341989/100000000000000 : ℝ)*(sp5) + (1572911952027293/100000000000000 : ℝ)*(sp6) + (193847061281033/25000000000000 : ℝ)*(sp7) + (193847061281033/25000000000000 : ℝ)*(f.failure) + (314585906957041/20000000000000 : ℝ)*(f.sum) + (4082280621647/2079531250000000000000000000 : ℝ)*base65 + (30407009387060906133/6654500000000000000000000000000000 : ℝ)*base68 + (12818478297539406133/6654500000000000000000000000000000 : ℝ)*base70 + (34965593307379906133/6654500000000000000000000000000000 : ℝ)*base72 + (114014352690013/33272500000000000000000000000 : ℝ)*base74 + (58088388698291406133/6654500000000000000000000000000000 : ℝ)*base76 + (39939477944816906133/6654500000000000000000000000000000 : ℝ)*base78 + (26052265378746906133/6654500000000000000000000000000000 : ℝ)*base80 + (253932219965209/66545000000000000000000000000 : ℝ)*base81 + (10228391/2500000000000000000000 : ℝ)*base89 + (10228391/2500000000000000000000 : ℝ)*base91 + (10228391/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1242_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151428527/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6859/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (409/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6191/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19999/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1242_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1242_s2_0 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2106012987/10000000000 : ℝ)*x 0 + (21971179/40000000 : ℝ)*x 1 + (517469469/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2106012987/10000000000 : ℝ)^8435 ≤ (12779914078737/100000000000000 : ℝ)^6387 := by
    have hnat : (2106012987 : ℕ)^8435*100000000000000^6387 ≤ 12779914078737^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106012987 10000000000 12779914078737 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21971179/40000000 : ℝ)^8435 ≤ (22663541498247/50000000000000 : ℝ)^6387 := by
    have hnat : (21971179 : ℕ)^8435*50000000000000^6387 ≤ 22663541498247^6387*40000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21971179 40000000 22663541498247 50000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (517469469/1000000000 : ℝ)^8435 ≤ (41893002900029/100000000000000 : ℝ)^6387 := by
    have hnat : (517469469 : ℕ)^8435*100000000000000^6387 ≤ 41893002900029^6387*1000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517469469 1000000000 41893002900029 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2106012987/10000000000 : ℝ), (21971179/40000000 : ℝ), (517469469/1000000000 : ℝ)] ![(12779914078737/100000000000000 : ℝ), (22663541498247/50000000000000 : ℝ), (41893002900029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2106012987/10000000000 : ℝ)|^8435 ≤ (12779914078737/100000000000000 : ℝ)^6387
        have hw : |(-2106012987/10000000000 : ℝ)|=(2106012987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21971179/40000000 : ℝ)|^8435 ≤ (22663541498247/50000000000000 : ℝ)^6387
        have hw : |(21971179/40000000 : ℝ)|=(21971179/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(517469469/1000000000 : ℝ)|^8435 ≤ (41893002900029/100000000000000 : ℝ)^6387
        have hw : |(517469469/1000000000 : ℝ)|=(517469469/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s2_1 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5369687571/10000000000 : ℝ)*x 0 + (-2270786717/10000000000 : ℝ)*x 1 + (51746947/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369687571/10000000000 : ℝ)^8435 ≤ (43990288753451/100000000000000 : ℝ)^6387 := by
    have hnat : (5369687571 : ℕ)^8435*100000000000000^6387 ≤ 43990288753451^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369687571 10000000000 43990288753451 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2270786717/10000000000 : ℝ)^8435 ≤ (7058354111997/50000000000000 : ℝ)^6387 := by
    have hnat : (2270786717 : ℕ)^8435*50000000000000^6387 ≤ 7058354111997^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2270786717 10000000000 7058354111997 50000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51746947/100000000 : ℝ)^8435 ≤ (8378600601389/20000000000000 : ℝ)^6387 := by
    have hnat : (51746947 : ℕ)^8435*20000000000000^6387 ≤ 8378600601389^6387*100000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51746947 100000000 8378600601389 20000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369687571/10000000000 : ℝ), (-2270786717/10000000000 : ℝ), (51746947/100000000 : ℝ)] ![(43990288753451/100000000000000 : ℝ), (7058354111997/50000000000000 : ℝ), (8378600601389/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369687571/10000000000 : ℝ)|^8435 ≤ (43990288753451/100000000000000 : ℝ)^6387
        have hw : |(5369687571/10000000000 : ℝ)|=(5369687571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2270786717/10000000000 : ℝ)|^8435 ≤ (7058354111997/50000000000000 : ℝ)^6387
        have hw : |(-2270786717/10000000000 : ℝ)|=(2270786717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(51746947/100000000 : ℝ)|^8435 ≤ (8378600601389/20000000000000 : ℝ)^6387
        have hw : |(51746947/100000000 : ℝ)|=(51746947/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s2_2 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2684843711/5000000000 : ℝ)*x 0 + (2587347409/5000000000 : ℝ)*x 1 + (-56769669/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684843711/5000000000 : ℝ)^8435 ≤ (43990287141387/100000000000000 : ℝ)^6387 := by
    have hnat : (2684843711 : ℕ)^8435*100000000000000^6387 ≤ 43990287141387^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684843711 5000000000 43990287141387 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2587347409/5000000000 : ℝ)^8435 ≤ (523662553357/1250000000000 : ℝ)^6387 := by
    have hnat : (2587347409 : ℕ)^8435*1250000000000^6387 ≤ 523662553357^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587347409 5000000000 523662553357 1250000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (56769669/250000000 : ℝ)^8435 ≤ (7058354288513/50000000000000 : ℝ)^6387 := by
    have hnat : (56769669 : ℕ)^8435*50000000000000^6387 ≤ 7058354288513^6387*250000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56769669 250000000 7058354288513 50000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684843711/5000000000 : ℝ), (2587347409/5000000000 : ℝ), (-56769669/250000000 : ℝ)] ![(43990287141387/100000000000000 : ℝ), (523662553357/1250000000000 : ℝ), (7058354288513/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684843711/5000000000 : ℝ)|^8435 ≤ (43990287141387/100000000000000 : ℝ)^6387
        have hw : |(2684843711/5000000000 : ℝ)|=(2684843711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2587347409/5000000000 : ℝ)|^8435 ≤ (523662553357/1250000000000 : ℝ)^6387
        have hw : |(2587347409/5000000000 : ℝ)|=(2587347409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-56769669/250000000 : ℝ)|^8435 ≤ (7058354288513/50000000000000 : ℝ)^6387
        have hw : |(-56769669/250000000 : ℝ)|=(56769669/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s2_3 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2171020171/5000000000 : ℝ)*x 0 + (161240281/400000000 : ℝ)*x 1 + (2338147703/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2171020171/5000000000 : ℝ)^8435 ≤ (33229201799223/100000000000000 : ℝ)^6387 := by
    have hnat : (2171020171 : ℕ)^8435*100000000000000^6387 ≤ 33229201799223^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171020171 5000000000 33229201799223 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (161240281/400000000 : ℝ)^8435 ≤ (30122352704323/100000000000000 : ℝ)^6387 := by
    have hnat : (161240281 : ℕ)^8435*100000000000000^6387 ≤ 30122352704323^6387*400000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161240281 400000000 30122352704323 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2338147703/5000000000 : ℝ)^8435 ≤ (7329689096549/20000000000000 : ℝ)^6387 := by
    have hnat : (2338147703 : ℕ)^8435*20000000000000^6387 ≤ 7329689096549^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2338147703 5000000000 7329689096549 20000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2171020171/5000000000 : ℝ), (161240281/400000000 : ℝ), (2338147703/5000000000 : ℝ)] ![(33229201799223/100000000000000 : ℝ), (30122352704323/100000000000000 : ℝ), (7329689096549/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2171020171/5000000000 : ℝ)|^8435 ≤ (33229201799223/100000000000000 : ℝ)^6387
        have hw : |(2171020171/5000000000 : ℝ)|=(2171020171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(161240281/400000000 : ℝ)|^8435 ≤ (30122352704323/100000000000000 : ℝ)^6387
        have hw : |(161240281/400000000 : ℝ)|=(161240281/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2338147703/5000000000 : ℝ)|^8435 ≤ (7329689096549/20000000000000 : ℝ)^6387
        have hw : |(2338147703/5000000000 : ℝ)|=(2338147703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s2_4 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1053045707/5000000000 : ℝ)*x 0 + (2588369837/5000000000 : ℝ)*x 1 + (5490730589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053045707/5000000000 : ℝ)^8435 ≤ (3195135651187/25000000000000 : ℝ)^6387 := by
    have hnat : (1053045707 : ℕ)^8435*25000000000000^6387 ≤ 3195135651187^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053045707 5000000000 3195135651187 25000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2588369837/5000000000 : ℝ)^8435 ≤ (41914868548353/100000000000000 : ℝ)^6387 := by
    have hnat : (2588369837 : ℕ)^8435*100000000000000^6387 ≤ 41914868548353^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588369837 5000000000 41914868548353 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5490730589/10000000000 : ℝ)^8435 ≤ (45304588826641/100000000000000 : ℝ)^6387 := by
    have hnat : (5490730589 : ℕ)^8435*100000000000000^6387 ≤ 45304588826641^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490730589 10000000000 45304588826641 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1053045707/5000000000 : ℝ), (2588369837/5000000000 : ℝ), (5490730589/10000000000 : ℝ)] ![(3195135651187/25000000000000 : ℝ), (41914868548353/100000000000000 : ℝ), (45304588826641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1053045707/5000000000 : ℝ)|^8435 ≤ (3195135651187/25000000000000 : ℝ)^6387
        have hw : |(-1053045707/5000000000 : ℝ)|=(1053045707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2588369837/5000000000 : ℝ)|^8435 ≤ (41914868548353/100000000000000 : ℝ)^6387
        have hw : |(2588369837/5000000000 : ℝ)|=(2588369837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5490730589/10000000000 : ℝ)|^8435 ≤ (45304588826641/100000000000000 : ℝ)^6387
        have hw : |(5490730589/10000000000 : ℝ)|=(5490730589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s2_5 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2644226633/5000000000 : ℝ)*x 0 + (-122171913/625000000 : ℝ)*x 1 + (5490730633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644226633/5000000000 : ℝ)^8435 ≤ (43113535971213/100000000000000 : ℝ)^6387 := by
    have hnat : (2644226633 : ℕ)^8435*100000000000000^6387 ≤ 43113535971213^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644226633 5000000000 43113535971213 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (122171913/625000000 : ℝ)^8435 ≤ (5790937355737/50000000000000 : ℝ)^6387 := by
    have hnat : (122171913 : ℕ)^8435*50000000000000^6387 ≤ 5790937355737^6387*625000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122171913 625000000 5790937355737 50000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5490730633/10000000000 : ℝ)^8435 ≤ (45304589306101/100000000000000 : ℝ)^6387 := by
    have hnat : (5490730633 : ℕ)^8435*100000000000000^6387 ≤ 45304589306101^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490730633 10000000000 45304589306101 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644226633/5000000000 : ℝ), (-122171913/625000000 : ℝ), (5490730633/10000000000 : ℝ)] ![(43113535971213/100000000000000 : ℝ), (5790937355737/50000000000000 : ℝ), (45304589306101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644226633/5000000000 : ℝ)|^8435 ≤ (43113535971213/100000000000000 : ℝ)^6387
        have hw : |(2644226633/5000000000 : ℝ)|=(2644226633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-122171913/625000000 : ℝ)|^8435 ≤ (5790937355737/50000000000000 : ℝ)^6387
        have hw : |(-122171913/625000000 : ℝ)|=(122171913/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5490730633/10000000000 : ℝ)|^8435 ≤ (45304589306101/100000000000000 : ℝ)^6387
        have hw : |(5490730633/10000000000 : ℝ)|=(5490730633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s2_6 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5288453431/10000000000 : ℝ)*x 0 + (2745365357/5000000000 : ℝ)*x 1 + (-1954750267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288453431/10000000000 : ℝ)^8435 ≤ (269459610923/625000000000 : ℝ)^6387 := by
    have hnat : (5288453431 : ℕ)^8435*625000000000^6387 ≤ 269459610923^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288453431 10000000000 269459610923 625000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2745365357/5000000000 : ℝ)^8435 ≤ (5663073773593/12500000000000 : ℝ)^6387 := by
    have hnat : (2745365357 : ℕ)^8435*12500000000000^6387 ≤ 5663073773593^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2745365357 5000000000 5663073773593 12500000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1954750267/10000000000 : ℝ)^8435 ≤ (11581872043203/100000000000000 : ℝ)^6387 := by
    have hnat : (1954750267 : ℕ)^8435*100000000000000^6387 ≤ 11581872043203^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1954750267 10000000000 11581872043203 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288453431/10000000000 : ℝ), (2745365357/5000000000 : ℝ), (-1954750267/10000000000 : ℝ)] ![(269459610923/625000000000 : ℝ), (5663073773593/12500000000000 : ℝ), (11581872043203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288453431/10000000000 : ℝ)|^8435 ≤ (269459610923/625000000000 : ℝ)^6387
        have hw : |(5288453431/10000000000 : ℝ)|=(5288453431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2745365357/5000000000 : ℝ)|^8435 ≤ (5663073773593/12500000000000 : ℝ)^6387
        have hw : |(2745365357/5000000000 : ℝ)|=(2745365357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1954750267/10000000000 : ℝ)|^8435 ≤ (11581872043203/100000000000000 : ℝ)^6387
        have hw : |(-1954750267/10000000000 : ℝ)|=(1954750267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s2_7 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (542774863/1250000000 : ℝ)*x 0 + (2336073637/5000000000 : ℝ)*x 1 + (4035193739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542774863/1250000000 : ℝ)^8435 ≤ (2076925272817/6250000000000 : ℝ)^6387 := by
    have hnat : (542774863 : ℕ)^8435*6250000000000^6387 ≤ 2076925272817^6387*1250000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542774863 1250000000 2076925272817 6250000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2336073637/5000000000 : ℝ)^8435 ≤ (18302759140611/50000000000000 : ℝ)^6387 := by
    have hnat : (2336073637 : ℕ)^8435*50000000000000^6387 ≤ 18302759140611^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2336073637 5000000000 18302759140611 50000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4035193739/10000000000 : ℝ)^8435 ≤ (30163677345847/100000000000000 : ℝ)^6387 := by
    have hnat : (4035193739 : ℕ)^8435*100000000000000^6387 ≤ 30163677345847^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4035193739 10000000000 30163677345847 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(542774863/1250000000 : ℝ), (2336073637/5000000000 : ℝ), (4035193739/10000000000 : ℝ)] ![(2076925272817/6250000000000 : ℝ), (18302759140611/50000000000000 : ℝ), (30163677345847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(542774863/1250000000 : ℝ)|^8435 ≤ (2076925272817/6250000000000 : ℝ)^6387
        have hw : |(542774863/1250000000 : ℝ)|=(542774863/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2336073637/5000000000 : ℝ)|^8435 ≤ (18302759140611/50000000000000 : ℝ)^6387
        have hw : |(2336073637/5000000000 : ℝ)|=(2336073637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4035193739/10000000000 : ℝ)|^8435 ≤ (30163677345847/100000000000000 : ℝ)^6387
        have hw : |(4035193739/10000000000 : ℝ)|=(4035193739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1242_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151428527/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19999/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6191/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9499/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16223/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19999/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6191/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19999/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6191/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19999/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6191/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19999/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6191/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19999/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6191/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19999/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6191/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6191/100000 : ℝ) ^ (4217/1024 : ℝ) ≤ (1057481465394883/100000000000000000000 : ℝ) := by
    have hpowers : (6191/100000 : ℝ)^4217 ≤ (1057481465394883/100000000000000000000 : ℝ)^1024 := by
      have hnat : (6191 : ℕ)^4217*100000000000000000000^1024 ≤ 1057481465394883^1024*100000^4217 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6191 100000 1057481465394883 100000000000000000000 4217 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6191/100000 : ℝ)) (X := (1057481465394883/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (19999/100000 : ℝ) ^ (4217/1024 : ℝ) ≤ (66131355517639401/50000000000000000000 : ℝ) := by
    have hpowers : (19999/100000 : ℝ)^4217 ≤ (66131355517639401/50000000000000000000 : ℝ)^1024 := by
      have hnat : (19999 : ℕ)^4217*50000000000000000000^1024 ≤ 66131355517639401^1024*100000^4217 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19999 100000 66131355517639401 50000000000000000000 4217 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19999/100000 : ℝ)) (X := (66131355517639401/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001057481465394883/50000000000000000000 : ℝ) ≤ (5000025678262989/5000000000000000 : ℝ) ^ (4217/1024 : ℝ) := by
    have hpowers : (50001057481465394883/50000000000000000000 : ℝ)^1024 ≤ (5000025678262989/5000000000000000 : ℝ)^4217 := by
      have hnat : (50001057481465394883 : ℕ)^1024*5000000000000000^4217 ≤ 5000025678262989^4217*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001057481465394883 50000000000000000000 5000025678262989 5000000000000000 1024 4217 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000025678262989/5000000000000000 : ℝ)) (X := (50001057481465394883/50000000000000000000 : ℝ)) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20026664038500134737/20000000000000000000 : ℝ) ≤ (10003235736895019/10000000000000000 : ℝ) ^ (4217/1024 : ℝ) := by
    have hpowers : (20026664038500134737/20000000000000000000 : ℝ)^1024 ≤ (10003235736895019/10000000000000000 : ℝ)^4217 := by
      have hnat : (20026664038500134737 : ℕ)^1024*10000000000000000^4217 ≤ 10003235736895019^4217*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20026664038500134737 20000000000000000000 10003235736895019 10000000000000000 1024 4217 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003235736895019/10000000000000000 : ℝ)) (X := (20026664038500134737/20000000000000000000 : ℝ)) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25066131355517639401/25000000000000000000 : ℝ) ≤ (500321005863203/500000000000000 : ℝ) ^ (4217/1024 : ℝ) := by
    have hpowers : (25066131355517639401/25000000000000000000 : ℝ)^1024 ≤ (500321005863203/500000000000000 : ℝ)^4217 := by
      have hnat : (25066131355517639401 : ℕ)^1024*500000000000000^4217 ≤ 500321005863203^4217*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25066131355517639401 25000000000000000000 500321005863203 500000000000000 1024 4217 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500321005863203/500000000000000 : ℝ)) (X := (25066131355517639401/25000000000000000000 : ℝ)) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1057481465394883/100000000000000000000 : ℝ) ≤ ((69020640066590619281/69040000000000000000 : ℝ)+2*(3184380369041/1380800000000000 : ℝ)*(6191/100000 : ℝ))^(4217/1024 : ℝ) := by
    rw [show (69020640066590619281/69040000000000000000 : ℝ)+2*(3184380369041/1380800000000000 : ℝ)*(6191/100000 : ℝ)=(5000025678262989/5000000000000000 : ℝ) by norm_num, show 1+2*(1057481465394883/100000000000000000000 : ℝ)=(50001057481465394883/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(66131355517639401/50000000000000000000 : ℝ)+(1057481465394883/100000000000000000000 : ℝ) ≤ ((69020640066590619281/69040000000000000000 : ℝ)+(3184380369041/1380800000000000 : ℝ)*((19999/100000 : ℝ)+(6191/100000 : ℝ)))^(4217/1024 : ℝ) := by
    rw [show (69020640066590619281/69040000000000000000 : ℝ)+(3184380369041/1380800000000000 : ℝ)*((19999/100000 : ℝ)+(6191/100000 : ℝ))=(10003235736895019/10000000000000000 : ℝ) by norm_num, show 1+(66131355517639401/50000000000000000000 : ℝ)+(1057481465394883/100000000000000000000 : ℝ)=(20026664038500134737/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(66131355517639401/50000000000000000000 : ℝ) ≤ ((69020640066590619281/69040000000000000000 : ℝ)+2*(3184380369041/1380800000000000 : ℝ)*(19999/100000 : ℝ))^(4217/1024 : ℝ) := by
    rw [show (69020640066590619281/69040000000000000000 : ℝ)+2*(3184380369041/1380800000000000 : ℝ)*(19999/100000 : ℝ)=(500321005863203/500000000000000 : ℝ) by norm_num, show 1+2*(66131355517639401/50000000000000000000 : ℝ)=(25066131355517639401/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (69020640066590619281/69040000000000000000 : ℝ)*(X 1 0+X 2 0)+(3184380369041/1380800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4217/1024 : ℝ)) (lo := (6191/100000 : ℝ)) (hi := (19999/100000 : ℝ)) (c := (69020640066590619281/69040000000000000000 : ℝ)) (alpha := (3184380369041/1380800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (69020640066590619281/69040000000000000000 : ℝ)*(X 0 1+X 2 1)+(3184380369041/1380800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4217/1024 : ℝ)) (lo := (6191/100000 : ℝ)) (hi := (19999/100000 : ℝ)) (c := (69020640066590619281/69040000000000000000 : ℝ)) (alpha := (3184380369041/1380800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (69020640066590619281/69040000000000000000 : ℝ)*(X 0 2+X 1 2)+(3184380369041/1380800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4217/1024 : ℝ)) (lo := (6191/100000 : ℝ)) (hi := (19999/100000 : ℝ)) (c := (69020640066590619281/69040000000000000000 : ℝ)) (alpha := (3184380369041/1380800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2106012987/10000000000 : ℝ)*X 0 0+(21971179/40000000 : ℝ)*X 0 1+(517469469/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5369687571/10000000000 : ℝ)*X 1 0+(-2270786717/10000000000 : ℝ)*X 1 1+(51746947/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2684843711/5000000000 : ℝ)*X 2 0+(2587347409/5000000000 : ℝ)*X 2 1+(-56769669/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2171020171/5000000000 : ℝ)*X 0 0+(161240281/400000000 : ℝ)*X 0 1+(2338147703/5000000000 : ℝ)*X 0 2+(2171020171/5000000000 : ℝ)*X 1 0+(161240281/400000000 : ℝ)*X 1 1+(2338147703/5000000000 : ℝ)*X 1 2+(2171020171/5000000000 : ℝ)*X 2 0+(161240281/400000000 : ℝ)*X 2 1+(2338147703/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1053045707/5000000000 : ℝ)*X 0 0+(2588369837/5000000000 : ℝ)*X 0 1+(5490730589/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2644226633/5000000000 : ℝ)*X 1 0+(-122171913/625000000 : ℝ)*X 1 1+(5490730633/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5288453431/10000000000 : ℝ)*X 2 0+(2745365357/5000000000 : ℝ)*X 2 1+(-1954750267/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((542774863/1250000000 : ℝ)*X 0 0+(2336073637/5000000000 : ℝ)*X 0 1+(4035193739/10000000000 : ℝ)*X 0 2+(542774863/1250000000 : ℝ)*X 1 0+(2336073637/5000000000 : ℝ)*X 1 1+(4035193739/10000000000 : ℝ)*X 1 2+(542774863/1250000000 : ℝ)*X 2 0+(2336073637/5000000000 : ℝ)*X 2 1+(4035193739/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (28556816965368319766537423541/3452000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1597095149/100000000000000 : ℝ)*(base19) + (56095231/4000000000000 : ℝ)*(base23) + (2885721/5000000000000 : ℝ)*(lower2) + (62639049/25000000000000 : ℝ)*(upper3) + (27945649/25000000000000 : ℝ)*(upper5) + (2346706473621513/100000000000000 : ℝ)*(major0) + (2346706473621513/100000000000000 : ℝ)*(major1) + (2346706473621513/100000000000000 : ℝ)*(major2) + (3143683838430589/100000000000000 : ℝ)*(sp0) + (392962349689229/12500000000000 : ℝ)*(sp1) + (1571849496114103/50000000000000 : ℝ)*(sp2) + (774851405883673/50000000000000 : ℝ)*(sp3) + (16556178393/100000000000000 : ℝ)*(sp4) + (4732557637/50000000000000 : ℝ)*(sp7) + (77485613844131/5000000000000 : ℝ)*(f.failure) + (1571850197304491/50000000000000 : ℝ)*(f.sum) + (37904699247287/69040000000000000000000000000 : ℝ)*base66 + (28387050751206157847/6904000000000000000000000000000000 : ℝ)*base68 + (22945725450929842153/6904000000000000000000000000000000 : ℝ)*base69 + (28734064934025842153/6904000000000000000000000000000000 : ℝ)*base71 + (190624230746247/69040000000000000000000000000 : ℝ)*base74 + (591767706822157847/6904000000000000000000000000000000 : ℝ)*base76 + (283765828585842153/6904000000000000000000000000000000 : ℝ)*base77 + (71732238144889842153/6904000000000000000000000000000000 : ℝ)*base79 + (172648354864953/69040000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (74963/500000000000000000000 : ℝ)*base90 + (74963/500000000000000000000 : ℝ)*base92 + (74963/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (260344837618614834466077/69040000000000000000000000000 : ℝ) := by norm_num
    linear_combination (285205233/25000000000000 : ℝ)*(base19) + (1446364911/100000000000000 : ℝ)*(base23) + (899127/1562500000000 : ℝ)*(upper2) + (34420517/20000000000000 : ℝ)*(upper3) + (14355021/20000000000000 : ℝ)*(upper5) + (2377388963943653/100000000000000 : ℝ)*(major0) + (2377388963943653/100000000000000 : ℝ)*(major1) + (2377388963943653/100000000000000 : ℝ)*(major2) + (5637609561/50000000000000 : ℝ)*(sp1) + (17614006203/100000000000000 : ℝ)*(sp2) + (398100437181431/12500000000000 : ℝ)*(sp4) + (1592395540705697/50000000000000 : ℝ)*(sp5) + (1592392218540167/50000000000000 : ℝ)*(sp6) + (156997430473827/10000000000000 : ℝ)*(sp7) + (156997430473827/10000000000000 : ℝ)*(f.failure) + (398100437181431/12500000000000 : ℝ)*(f.sum) + (262863591849547/69040000000000000000000000000 : ℝ)*base66 + (9143538689070023493/6904000000000000000000000000000000 : ℝ)*base67 + (3354462404190023493/6904000000000000000000000000000000 : ℝ)*base69 + (27510333157985976507/6904000000000000000000000000000000 : ℝ)*base72 + (94140695017387/69040000000000000000000000000 : ℝ)*base74 + (66960027615470023493/6904000000000000000000000000000000 : ℝ)*base75 + (7144631957201976507/6904000000000000000000000000000000 : ℝ)*base78 + (22012739845441976507/6904000000000000000000000000000000 : ℝ)*base80 + (175478384124107/69040000000000000000000000000 : ℝ)*base82 + (4662829/1000000000000000000000 : ℝ)*base89 + (4662829/1000000000000000000000 : ℝ)*base91 + (4662829/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1242_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151428527/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19999/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6191/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9499/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16223/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1242_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1242_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151428527/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9499/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16223/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1242_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1242_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1242_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151428527/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9499/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16223/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1242_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1426_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:52:55.017729+00:00
-- url     : https://prove2.me/submissions/a1cc5730-3bc7-4f5f-bf92-ac83df05fab1

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
theorem support_rectangle_w1426_s3_0 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1972491281/10000000000 : ℝ)*x 0 + (541758833/1000000000 : ℝ)*x 1 + (523833301/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1972491281/10000000000 : ℝ)^2193 ≤ (12030685149243/100000000000000 : ℝ)^1681 := by
    have hnat : (1972491281 : ℕ)^2193*100000000000000^1681 ≤ 12030685149243^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1972491281 10000000000 12030685149243 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541758833/1000000000 : ℝ)^2193 ≤ (44949873220221/100000000000000 : ℝ)^1681 := by
    have hnat : (541758833 : ℕ)^2193*100000000000000^1681 ≤ 44949873220221^1681*1000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541758833 1000000000 44949873220221 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (523833301/1000000000 : ℝ)^2193 ≤ (43019441613289/100000000000000 : ℝ)^1681 := by
    have hnat : (523833301 : ℕ)^2193*100000000000000^1681 ≤ 43019441613289^1681*1000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523833301 1000000000 43019441613289 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1972491281/10000000000 : ℝ), (541758833/1000000000 : ℝ), (523833301/1000000000 : ℝ)] ![(12030685149243/100000000000000 : ℝ), (44949873220221/100000000000000 : ℝ), (43019441613289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1972491281/10000000000 : ℝ)|^2193 ≤ (12030685149243/100000000000000 : ℝ)^1681
        have hw : |(-1972491281/10000000000 : ℝ)|=(1972491281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541758833/1000000000 : ℝ)|^2193 ≤ (44949873220221/100000000000000 : ℝ)^1681
        have hw : |(541758833/1000000000 : ℝ)|=(541758833/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(523833301/1000000000 : ℝ)|^2193 ≤ (43019441613289/100000000000000 : ℝ)^1681
        have hw : |(523833301/1000000000 : ℝ)|=(523833301/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s3_1 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1337442071/2500000000 : ℝ)*x 0 + (-412786877/2000000000 : ℝ)*x 1 + (523833299/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337442071/2500000000 : ℝ)^2193 ≤ (22108591580293/50000000000000 : ℝ)^1681 := by
    have hnat : (1337442071 : ℕ)^2193*50000000000000^1681 ≤ 22108591580293^1681*2500000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337442071 2500000000 22108591580293 50000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (412786877/2000000000 : ℝ)^2193 ≤ (1276337541943/10000000000000 : ℝ)^1681 := by
    have hnat : (412786877 : ℕ)^2193*10000000000000^1681 ≤ 1276337541943^1681*2000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412786877 2000000000 1276337541943 10000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (523833299/1000000000 : ℝ)^2193 ≤ (43019441399013/100000000000000 : ℝ)^1681 := by
    have hnat : (523833299 : ℕ)^2193*100000000000000^1681 ≤ 43019441399013^1681*1000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523833299 1000000000 43019441399013 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337442071/2500000000 : ℝ), (-412786877/2000000000 : ℝ), (523833299/1000000000 : ℝ)] ![(22108591580293/50000000000000 : ℝ), (1276337541943/10000000000000 : ℝ), (43019441399013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337442071/2500000000 : ℝ)|^2193 ≤ (22108591580293/50000000000000 : ℝ)^1681
        have hw : |(1337442071/2500000000 : ℝ)|=(1337442071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-412786877/2000000000 : ℝ)|^2193 ≤ (1276337541943/10000000000000 : ℝ)^1681
        have hw : |(-412786877/2000000000 : ℝ)|=(412786877/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(523833299/1000000000 : ℝ)|^2193 ≤ (43019441399013/100000000000000 : ℝ)^1681
        have hw : |(523833299/1000000000 : ℝ)|=(523833299/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s3_2 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (534976831/1000000000 : ℝ)*x 0 + (5238332969/10000000000 : ℝ)*x 1 + (-2063934379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534976831/1000000000 : ℝ)^2193 ≤ (5527147930117/12500000000000 : ℝ)^1681 := by
    have hnat : (534976831 : ℕ)^2193*12500000000000^1681 ≤ 5527147930117^1681*1000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534976831 1000000000 5527147930117 12500000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5238332969/10000000000 : ℝ)^2193 ≤ (5377430146753/12500000000000 : ℝ)^1681 := by
    have hnat : (5238332969 : ℕ)^2193*12500000000000^1681 ≤ 5377430146753^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238332969 10000000000 5377430146753 12500000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2063934379/10000000000 : ℝ)^2193 ≤ (510535014841/4000000000000 : ℝ)^1681 := by
    have hnat : (2063934379 : ℕ)^2193*4000000000000^1681 ≤ 510535014841^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063934379 10000000000 510535014841 4000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534976831/1000000000 : ℝ), (5238332969/10000000000 : ℝ), (-2063934379/10000000000 : ℝ)] ![(5527147930117/12500000000000 : ℝ), (5377430146753/12500000000000 : ℝ), (510535014841/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534976831/1000000000 : ℝ)|^2193 ≤ (5527147930117/12500000000000 : ℝ)^1681
        have hw : |(534976831/1000000000 : ℝ)|=(534976831/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5238332969/10000000000 : ℝ)|^2193 ≤ (5377430146753/12500000000000 : ℝ)^1681
        have hw : |(5238332969/10000000000 : ℝ)|=(5238332969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2063934379/10000000000 : ℝ)|^2193 ≤ (510535014841/4000000000000 : ℝ)^1681
        have hw : |(-2063934379/10000000000 : ℝ)|=(2063934379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s3_3 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4304466729/10000000000 : ℝ)*x 0 + (1028677087/2500000000 : ℝ)*x 1 + (562758893/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4304466729/10000000000 : ℝ)^2193 ≤ (33298010846659/100000000000000 : ℝ)^1681 := by
    have hnat : (4304466729 : ℕ)^2193*100000000000000^1681 ≤ 33298010846659^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4304466729 10000000000 33298010846659 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1028677087/2500000000 : ℝ)^2193 ≤ (6279198459591/20000000000000 : ℝ)^1681 := by
    have hnat : (1028677087 : ℕ)^2193*20000000000000^1681 ≤ 6279198459591^1681*2500000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028677087 2500000000 6279198459591 20000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (562758893/1250000000 : ℝ)^2193 ≤ (441324960531/1250000000000 : ℝ)^1681 := by
    have hnat : (562758893 : ℕ)^2193*1250000000000^1681 ≤ 441324960531^1681*1250000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562758893 1250000000 441324960531 1250000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4304466729/10000000000 : ℝ), (1028677087/2500000000 : ℝ), (562758893/1250000000 : ℝ)] ![(33298010846659/100000000000000 : ℝ), (6279198459591/20000000000000 : ℝ), (441324960531/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4304466729/10000000000 : ℝ)|^2193 ≤ (33298010846659/100000000000000 : ℝ)^1681
        have hw : |(4304466729/10000000000 : ℝ)|=(4304466729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1028677087/2500000000 : ℝ)|^2193 ≤ (6279198459591/20000000000000 : ℝ)^1681
        have hw : |(1028677087/2500000000 : ℝ)|=(1028677087/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(562758893/1250000000 : ℝ)|^2193 ≤ (441324960531/1250000000000 : ℝ)^1681
        have hw : |(562758893/1250000000 : ℝ)|=(562758893/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s3_4 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-39450133/200000000 : ℝ)*x 0 + (5239049761/10000000000 : ℝ)*x 1 + (135421689/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (39450133/200000000 : ℝ)^2193 ≤ (3007701859907/25000000000000 : ℝ)^1681 := by
    have hnat : (39450133 : ℕ)^2193*25000000000000^1681 ≤ 3007701859907^1681*200000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39450133 200000000 3007701859907 25000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5239049761/10000000000 : ℝ)^2193 ≤ (43027120883337/100000000000000 : ℝ)^1681 := by
    have hnat : (5239049761 : ℕ)^2193*100000000000000^1681 ≤ 43027120883337^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239049761 10000000000 43027120883337 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135421689/250000000 : ℝ)^2193 ≤ (44942071663131/100000000000000 : ℝ)^1681 := by
    have hnat : (135421689 : ℕ)^2193*100000000000000^1681 ≤ 44942071663131^1681*250000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135421689 250000000 44942071663131 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-39450133/200000000 : ℝ), (5239049761/10000000000 : ℝ), (135421689/250000000 : ℝ)] ![(3007701859907/25000000000000 : ℝ), (43027120883337/100000000000000 : ℝ), (44942071663131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-39450133/200000000 : ℝ)|^2193 ≤ (3007701859907/25000000000000 : ℝ)^1681
        have hw : |(-39450133/200000000 : ℝ)|=(39450133/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5239049761/10000000000 : ℝ)|^2193 ≤ (43027120883337/100000000000000 : ℝ)^1681
        have hw : |(5239049761/10000000000 : ℝ)|=(5239049761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135421689/250000000 : ℝ)|^2193 ≤ (44942071663131/100000000000000 : ℝ)^1681
        have hw : |(135421689/250000000 : ℝ)|=(135421689/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s3_5 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1060636251/2000000000 : ℝ)*x 0 + (-188539971/1000000000 : ℝ)*x 1 + (5416867573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060636251/2000000000 : ℝ)^2193 ≤ (21857758659497/50000000000000 : ℝ)^1681 := by
    have hnat : (1060636251 : ℕ)^2193*50000000000000^1681 ≤ 21857758659497^1681*2000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060636251 2000000000 21857758659497 50000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (188539971/1000000000 : ℝ)^2193 ≤ (2835602714751/25000000000000 : ℝ)^1681 := by
    have hnat : (188539971 : ℕ)^2193*25000000000000^1681 ≤ 2835602714751^1681*1000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188539971 1000000000 2835602714751 25000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416867573/10000000000 : ℝ)^2193 ≤ (44942071803839/100000000000000 : ℝ)^1681 := by
    have hnat : (5416867573 : ℕ)^2193*100000000000000^1681 ≤ 44942071803839^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416867573 10000000000 44942071803839 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060636251/2000000000 : ℝ), (-188539971/1000000000 : ℝ), (5416867573/10000000000 : ℝ)] ![(21857758659497/50000000000000 : ℝ), (2835602714751/25000000000000 : ℝ), (44942071803839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060636251/2000000000 : ℝ)|^2193 ≤ (21857758659497/50000000000000 : ℝ)^1681
        have hw : |(1060636251/2000000000 : ℝ)|=(1060636251/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-188539971/1000000000 : ℝ)|^2193 ≤ (2835602714751/25000000000000 : ℝ)^1681
        have hw : |(-188539971/1000000000 : ℝ)|=(188539971/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416867573/10000000000 : ℝ)|^2193 ≤ (44942071803839/100000000000000 : ℝ)^1681
        have hw : |(5416867573/10000000000 : ℝ)|=(5416867573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s3_6 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (848509/1600000 : ℝ)*x 0 + (2708433781/5000000000 : ℝ)*x 1 + (-1885399733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (848509/1600000 : ℝ)^2193 ≤ (5464439658153/12500000000000 : ℝ)^1681 := by
    have hnat : (848509 : ℕ)^2193*12500000000000^1681 ≤ 5464439658153^1681*1600000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848509 1600000 5464439658153 12500000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2708433781/5000000000 : ℝ)^2193 ≤ (44942071684779/100000000000000 : ℝ)^1681 := by
    have hnat : (2708433781 : ℕ)^2193*100000000000000^1681 ≤ 44942071684779^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708433781 5000000000 44942071684779 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1885399733/10000000000 : ℝ)^2193 ≤ (5671205519757/50000000000000 : ℝ)^1681 := by
    have hnat : (1885399733 : ℕ)^2193*50000000000000^1681 ≤ 5671205519757^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1885399733 10000000000 5671205519757 50000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(848509/1600000 : ℝ), (2708433781/5000000000 : ℝ), (-1885399733/10000000000 : ℝ)] ![(5464439658153/12500000000000 : ℝ), (44942071684779/100000000000000 : ℝ), (5671205519757/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(848509/1600000 : ℝ)|^2193 ≤ (5464439658153/12500000000000 : ℝ)^1681
        have hw : |(848509/1600000 : ℝ)|=(848509/1600000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2708433781/5000000000 : ℝ)|^2193 ≤ (44942071684779/100000000000000 : ℝ)^1681
        have hw : |(2708433781/5000000000 : ℝ)|=(2708433781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1885399733/10000000000 : ℝ)|^2193 ≤ (5671205519757/50000000000000 : ℝ)^1681
        have hw : |(-1885399733/10000000000 : ℝ)|=(1885399733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s3_7 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4304500211/10000000000 : ℝ)*x 0 + (1800209/4000000 : ℝ)*x 1 + (2058132949/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4304500211/10000000000 : ℝ)^2193 ≤ (16649174370827/50000000000000 : ℝ)^1681 := by
    have hnat : (4304500211 : ℕ)^2193*50000000000000^1681 ≤ 16649174370827^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4304500211 10000000000 16649174370827 50000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1800209/4000000 : ℝ)^2193 ≤ (7058030779721/20000000000000 : ℝ)^1681 := by
    have hnat : (1800209 : ℕ)^2193*20000000000000^1681 ≤ 7058030779721^1681*4000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1800209 4000000 7058030779721 20000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2058132949/5000000000 : ℝ)^2193 ≤ (7852874336393/25000000000000 : ℝ)^1681 := by
    have hnat : (2058132949 : ℕ)^2193*25000000000000^1681 ≤ 7852874336393^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2058132949 5000000000 7852874336393 25000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4304500211/10000000000 : ℝ), (1800209/4000000 : ℝ), (2058132949/5000000000 : ℝ)] ![(16649174370827/50000000000000 : ℝ), (7058030779721/20000000000000 : ℝ), (7852874336393/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4304500211/10000000000 : ℝ)|^2193 ≤ (16649174370827/50000000000000 : ℝ)^1681
        have hw : |(4304500211/10000000000 : ℝ)|=(4304500211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1800209/4000000 : ℝ)|^2193 ≤ (7058030779721/20000000000000 : ℝ)^1681
        have hw : |(1800209/4000000 : ℝ)|=(1800209/4000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2058132949/5000000000 : ℝ)|^2193 ≤ (7852874336393/25000000000000 : ℝ)^1681
        have hw : |(2058132949/5000000000 : ℝ)|=(2058132949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1426_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79023921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15809/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10351/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (697/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3737/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15809/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10351/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15809/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10351/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15809/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10351/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15809/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10351/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15809/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10351/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15809/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10351/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10351/100000 : ℝ) ^ (4385/1024 : ℝ) ≤ (3026224072689983/50000000000000000000 : ℝ) := by
    have hpowers : (10351/100000 : ℝ)^4385 ≤ (3026224072689983/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10351 : ℕ)^4385*50000000000000000000^1024 ≤ 3026224072689983^1024*100000^4385 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10351 100000 3026224072689983 50000000000000000000 4385 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10351/100000 : ℝ)) (X := (3026224072689983/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15809/100000 : ℝ) ^ (4385/1024 : ℝ) ≤ (18556546087804619/50000000000000000000 : ℝ) := by
    have hpowers : (15809/100000 : ℝ)^4385 ≤ (18556546087804619/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15809 : ℕ)^4385*50000000000000000000^1024 ≤ 18556546087804619^1024*100000^4385 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15809 100000 18556546087804619 50000000000000000000 4385 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15809/100000 : ℝ)) (X := (18556546087804619/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003026224072689983/25000000000000000000 : ℝ) ≤ (10000282664511107/10000000000000000 : ℝ) ^ (4385/1024 : ℝ) := by
    have hpowers : (25003026224072689983/25000000000000000000 : ℝ)^1024 ≤ (10000282664511107/10000000000000000 : ℝ)^4385 := by
      have hnat : (25003026224072689983 : ℕ)^1024*10000000000000000^4385 ≤ 10000282664511107^4385*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003026224072689983 25000000000000000000 10000282664511107 10000000000000000 1024 4385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000282664511107/10000000000000000 : ℝ)) (X := (25003026224072689983/25000000000000000000 : ℝ)) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25010791385080247301/25000000000000000000 : ℝ) ≤ (5000503924777969/5000000000000000 : ℝ) ^ (4385/1024 : ℝ) := by
    have hpowers : (25010791385080247301/25000000000000000000 : ℝ)^1024 ≤ (5000503924777969/5000000000000000 : ℝ)^4385 := by
      have hnat : (25010791385080247301 : ℕ)^1024*5000000000000000^4385 ≤ 5000503924777969^4385*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010791385080247301 25000000000000000000 5000503924777969 5000000000000000 1024 4385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000503924777969/5000000000000000 : ℝ)) (X := (25010791385080247301/25000000000000000000 : ℝ)) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018556546087804619/25000000000000000000 : ℝ) ≤ (10001733034600769/10000000000000000 : ℝ) ^ (4385/1024 : ℝ) := by
    have hpowers : (25018556546087804619/25000000000000000000 : ℝ)^1024 ≤ (10001733034600769/10000000000000000 : ℝ)^4385 := by
      have hnat : (25018556546087804619 : ℕ)^1024*10000000000000000^4385 ≤ 10001733034600769^4385*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018556546087804619 25000000000000000000 10001733034600769 10000000000000000 1024 4385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001733034600769/10000000000000000 : ℝ)) (X := (25018556546087804619/25000000000000000000 : ℝ)) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3026224072689983/50000000000000000000 : ℝ) ≤ ((13641632500525882661/13645000000000000000 : ℝ)+2*(725185044831/545800000000000 : ℝ)*(10351/100000 : ℝ))^(4385/1024 : ℝ) := by
    rw [show (13641632500525882661/13645000000000000000 : ℝ)+2*(725185044831/545800000000000 : ℝ)*(10351/100000 : ℝ)=(10000282664511107/10000000000000000 : ℝ) by norm_num, show 1+2*(3026224072689983/50000000000000000000 : ℝ)=(25003026224072689983/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18556546087804619/50000000000000000000 : ℝ)+(3026224072689983/50000000000000000000 : ℝ) ≤ ((13641632500525882661/13645000000000000000 : ℝ)+(725185044831/545800000000000 : ℝ)*((15809/100000 : ℝ)+(10351/100000 : ℝ)))^(4385/1024 : ℝ) := by
    rw [show (13641632500525882661/13645000000000000000 : ℝ)+(725185044831/545800000000000 : ℝ)*((15809/100000 : ℝ)+(10351/100000 : ℝ))=(5000503924777969/5000000000000000 : ℝ) by norm_num, show 1+(18556546087804619/50000000000000000000 : ℝ)+(3026224072689983/50000000000000000000 : ℝ)=(25010791385080247301/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18556546087804619/50000000000000000000 : ℝ) ≤ ((13641632500525882661/13645000000000000000 : ℝ)+2*(725185044831/545800000000000 : ℝ)*(15809/100000 : ℝ))^(4385/1024 : ℝ) := by
    rw [show (13641632500525882661/13645000000000000000 : ℝ)+2*(725185044831/545800000000000 : ℝ)*(15809/100000 : ℝ)=(10001733034600769/10000000000000000 : ℝ) by norm_num, show 1+2*(18556546087804619/50000000000000000000 : ℝ)=(25018556546087804619/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13641632500525882661/13645000000000000000 : ℝ)*(X 1 0+X 2 0)+(725185044831/545800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4385/1024 : ℝ)) (lo := (10351/100000 : ℝ)) (hi := (15809/100000 : ℝ)) (c := (13641632500525882661/13645000000000000000 : ℝ)) (alpha := (725185044831/545800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13641632500525882661/13645000000000000000 : ℝ)*(X 0 1+X 2 1)+(725185044831/545800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4385/1024 : ℝ)) (lo := (10351/100000 : ℝ)) (hi := (15809/100000 : ℝ)) (c := (13641632500525882661/13645000000000000000 : ℝ)) (alpha := (725185044831/545800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13641632500525882661/13645000000000000000 : ℝ)*(X 0 2+X 1 2)+(725185044831/545800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4385/1024 : ℝ)) (lo := (10351/100000 : ℝ)) (hi := (15809/100000 : ℝ)) (c := (13641632500525882661/13645000000000000000 : ℝ)) (alpha := (725185044831/545800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1972491281/10000000000 : ℝ)*X 0 0+(541758833/1000000000 : ℝ)*X 0 1+(523833301/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337442071/2500000000 : ℝ)*X 1 0+(-412786877/2000000000 : ℝ)*X 1 1+(523833299/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534976831/1000000000 : ℝ)*X 2 0+(5238332969/10000000000 : ℝ)*X 2 1+(-2063934379/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4304466729/10000000000 : ℝ)*X 0 0+(1028677087/2500000000 : ℝ)*X 0 1+(562758893/1250000000 : ℝ)*X 0 2+(4304466729/10000000000 : ℝ)*X 1 0+(1028677087/2500000000 : ℝ)*X 1 1+(562758893/1250000000 : ℝ)*X 1 2+(4304466729/10000000000 : ℝ)*X 2 0+(1028677087/2500000000 : ℝ)*X 2 1+(562758893/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-39450133/200000000 : ℝ)*X 0 0+(5239049761/10000000000 : ℝ)*X 0 1+(135421689/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1060636251/2000000000 : ℝ)*X 1 0+(-188539971/1000000000 : ℝ)*X 1 1+(5416867573/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((848509/1600000 : ℝ)*X 2 0+(2708433781/5000000000 : ℝ)*X 2 1+(-1885399733/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4304500211/10000000000 : ℝ)*X 0 0+(1800209/4000000 : ℝ)*X 0 1+(2058132949/5000000000 : ℝ)*X 0 2+(4304500211/10000000000 : ℝ)*X 1 0+(1800209/4000000 : ℝ)*X 1 1+(2058132949/5000000000 : ℝ)*X 1 2+(4304500211/10000000000 : ℝ)*X 2 0+(1800209/4000000 : ℝ)*X 2 1+(2058132949/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (240780956656078467229566663/27290000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (405858149/25000000000000 : ℝ)*(base19) + (201436503/12500000000000 : ℝ)*(base23) + (118655559/50000000000000 : ℝ)*(upper3) + (20892527/100000000000000 : ℝ)*(upper4) + (44322863/20000000000000 : ℝ)*(upper5) + (510017418201001/12500000000000 : ℝ)*(major0) + (510017418201001/12500000000000 : ℝ)*(major1) + (4080139345608009/100000000000000 : ℝ)*(major2) + (5578664038868447/100000000000000 : ℝ)*(sp0) + (348668237290111/6250000000000 : ℝ)*(sp1) + (1394672952145587/25000000000000 : ℝ)*(sp2) + (2581571835051299/100000000000000 : ℝ)*(sp3) + (14690602963/50000000000000 : ℝ)*(sp4) + (13141988761/100000000000000 : ℝ)*(sp7) + (129079248852003/5000000000000 : ℝ)*(f.failure) + (1394673355018593/25000000000000 : ℝ)*(f.sum) + (44022668567827/54580000000000000000000000000 : ℝ)*base65 + (119419071679488577/5330078125000000000000000000000 : ℝ)*base68 + (18190307797525968051/1364500000000000000000000000000000 : ℝ)*base70 + (107398278966094933/21320312500000000000000000000000 : ℝ)*base72 + (351538117809233/54580000000000000000000000000 : ℝ)*base74 + (22606231247070968051/1364500000000000000000000000000000 : ℝ)*base76 + (2635568426530356339/170562500000000000000000000000000 : ℝ)*base78 + (2340690824487731339/170562500000000000000000000000000 : ℝ)*base80 + (50065010881133/6822500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (5763763/250000000000000000000 : ℝ)*base89 + (5763763/250000000000000000000 : ℝ)*base91 + (3263763/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3108789154805175571150180887/682250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (809243071/100000000000000 : ℝ)*(base19) + (105511033/12500000000000 : ℝ)*(base23) + (52041901/50000000000000 : ℝ)*(upper3) + (5188067/25000000000000 : ℝ)*(lower4) + (100690271/100000000000000 : ℝ)*(upper5) + (4113080509721111/100000000000000 : ℝ)*(major0) + (4113080509721111/100000000000000 : ℝ)*(major1) + (4113080509721111/100000000000000 : ℝ)*(major2) + (7676772289/50000000000000 : ℝ)*(sp1) + (3867288397/25000000000000 : ℝ)*(sp2) + (1124746672706249/20000000000000 : ℝ)*(sp4) + (1405929300185899/25000000000000 : ℝ)*(sp5) + (5623717050289393/100000000000000 : ℝ)*(sp6) + (1301213752010961/50000000000000 : ℝ)*(sp7) + (1301213752010961/50000000000000 : ℝ)*(f.failure) + (1124746672706249/20000000000000 : ℝ)*(f.sum) + (85576311818561/27290000000000000000000000000 : ℝ)*base65 + (8454597828699081371/1364500000000000000000000000000000 : ℝ)*base67 + (3628223908539581371/1364500000000000000000000000000000 : ℝ)*base69 + (2689646418728581371/1364500000000000000000000000000000 : ℝ)*base71 + (133207540497341/27290000000000000000000000000 : ℝ)*base73 + (10524504432083581371/1364500000000000000000000000000000 : ℝ)*base75 + (1272343614342418629/1364500000000000000000000000000000 : ℝ)*base78 + (9237686819649418629/1364500000000000000000000000000000 : ℝ)*base80 + (12158340607909/27290000000000000000000000000 : ℝ)*base82 + (1801919/2500000000000000000000 : ℝ)*base90 + (1801919/2500000000000000000000 : ℝ)*base92 + (1801919/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1426_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79023921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15809/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10351/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (697/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3737/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1426_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1426_s4_0 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1973408369/10000000000 : ℝ)*x 0 + (5409779163/10000000000 : ℝ)*x 1 + (209821529/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1973408369/10000000000 : ℝ)^2193 ≤ (1203798288181/10000000000000 : ℝ)^1681 := by
    have hnat : (1973408369 : ℕ)^2193*10000000000000^1681 ≤ 1203798288181^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1973408369 10000000000 1203798288181 10000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409779163/10000000000 : ℝ)^2193 ≤ (44865364267281/100000000000000 : ℝ)^1681 := by
    have hnat : (5409779163 : ℕ)^2193*100000000000000^1681 ≤ 44865364267281^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409779163 10000000000 44865364267281 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209821529/400000000 : ℝ)^2193 ≤ (43096652841683/100000000000000 : ℝ)^1681 := by
    have hnat : (209821529 : ℕ)^2193*100000000000000^1681 ≤ 43096652841683^1681*400000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209821529 400000000 43096652841683 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1973408369/10000000000 : ℝ), (5409779163/10000000000 : ℝ), (209821529/400000000 : ℝ)] ![(1203798288181/10000000000000 : ℝ), (44865364267281/100000000000000 : ℝ), (43096652841683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1973408369/10000000000 : ℝ)|^2193 ≤ (1203798288181/10000000000000 : ℝ)^1681
        have hw : |(-1973408369/10000000000 : ℝ)|=(1973408369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409779163/10000000000 : ℝ)|^2193 ≤ (44865364267281/100000000000000 : ℝ)^1681
        have hw : |(5409779163/10000000000 : ℝ)|=(5409779163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(209821529/400000000 : ℝ)|^2193 ≤ (43096652841683/100000000000000 : ℝ)^1681
        have hw : |(209821529/400000000 : ℝ)|=(209821529/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s4_1 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (33423457/62500000 : ℝ)*x 0 + (-411410629/2000000000 : ℝ)*x 1 + (1311384617/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33423457/62500000 : ℝ)^2193 ≤ (1381107985109/3125000000000 : ℝ)^1681 := by
    have hnat : (33423457 : ℕ)^2193*3125000000000^1681 ≤ 1381107985109^1681*62500000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33423457 62500000 1381107985109 3125000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (411410629/2000000000 : ℝ)^2193 ≤ (6353944509969/50000000000000 : ℝ)^1681 := by
    have hnat : (411410629 : ℕ)^2193*50000000000000^1681 ≤ 6353944509969^1681*2000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411410629 2000000000 6353944509969 50000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311384617/2500000000 : ℝ)^2193 ≤ (43096655446221/100000000000000 : ℝ)^1681 := by
    have hnat : (1311384617 : ℕ)^2193*100000000000000^1681 ≤ 43096655446221^1681*2500000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311384617 2500000000 43096655446221 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33423457/62500000 : ℝ), (-411410629/2000000000 : ℝ), (1311384617/2500000000 : ℝ)] ![(1381107985109/3125000000000 : ℝ), (6353944509969/50000000000000 : ℝ), (43096655446221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33423457/62500000 : ℝ)|^2193 ≤ (1381107985109/3125000000000 : ℝ)^1681
        have hw : |(33423457/62500000 : ℝ)|=(33423457/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-411410629/2000000000 : ℝ)|^2193 ≤ (6353944509969/50000000000000 : ℝ)^1681
        have hw : |(-411410629/2000000000 : ℝ)|=(411410629/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311384617/2500000000 : ℝ)|^2193 ≤ (43096655446221/100000000000000 : ℝ)^1681
        have hw : |(1311384617/2500000000 : ℝ)|=(1311384617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s4_2 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2673876573/5000000000 : ℝ)*x 0 + (327846159/625000000 : ℝ)*x 1 + (-205705301/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673876573/5000000000 : ℝ)^2193 ≤ (22097727901903/50000000000000 : ℝ)^1681 := by
    have hnat : (2673876573 : ℕ)^2193*50000000000000^1681 ≤ 22097727901903^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673876573 5000000000 22097727901903 50000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327846159/625000000 : ℝ)^2193 ≤ (43096656260809/100000000000000 : ℝ)^1681 := by
    have hnat : (327846159 : ℕ)^2193*100000000000000^1681 ≤ 43096656260809^1681*625000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327846159 625000000 43096656260809 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (205705301/1000000000 : ℝ)^2193 ≤ (12707887931929/100000000000000 : ℝ)^1681 := by
    have hnat : (205705301 : ℕ)^2193*100000000000000^1681 ≤ 12707887931929^1681*1000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205705301 1000000000 12707887931929 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673876573/5000000000 : ℝ), (327846159/625000000 : ℝ), (-205705301/1000000000 : ℝ)] ![(22097727901903/50000000000000 : ℝ), (43096656260809/100000000000000 : ℝ), (12707887931929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673876573/5000000000 : ℝ)|^2193 ≤ (22097727901903/50000000000000 : ℝ)^1681
        have hw : |(2673876573/5000000000 : ℝ)|=(2673876573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(327846159/625000000 : ℝ)|^2193 ≤ (43096656260809/100000000000000 : ℝ)^1681
        have hw : |(327846159/625000000 : ℝ)|=(327846159/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-205705301/1000000000 : ℝ)|^2193 ≤ (12707887931929/100000000000000 : ℝ)^1681
        have hw : |(-205705301/1000000000 : ℝ)|=(205705301/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s4_3 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4305028019/10000000000 : ℝ)*x 0 + (826172701/2000000000 : ℝ)*x 1 + (2242890311/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4305028019/10000000000 : ℝ)^2193 ≤ (33303675401453/100000000000000 : ℝ)^1681 := by
    have hnat : (4305028019 : ℕ)^2193*100000000000000^1681 ≤ 33303675401453^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4305028019 10000000000 33303675401453 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (826172701/2000000000 : ℝ)^2193 ≤ (31556899920517/100000000000000 : ℝ)^1681 := by
    have hnat : (826172701 : ℕ)^2193*100000000000000^1681 ≤ 31556899920517^1681*2000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      826172701 2000000000 31556899920517 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2242890311/5000000000 : ℝ)^2193 ≤ (4392428083457/12500000000000 : ℝ)^1681 := by
    have hnat : (2242890311 : ℕ)^2193*12500000000000^1681 ≤ 4392428083457^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242890311 5000000000 4392428083457 12500000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4305028019/10000000000 : ℝ), (826172701/2000000000 : ℝ), (2242890311/5000000000 : ℝ)] ![(33303675401453/100000000000000 : ℝ), (31556899920517/100000000000000 : ℝ), (4392428083457/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4305028019/10000000000 : ℝ)|^2193 ≤ (33303675401453/100000000000000 : ℝ)^1681
        have hw : |(4305028019/10000000000 : ℝ)|=(4305028019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(826172701/2000000000 : ℝ)|^2193 ≤ (31556899920517/100000000000000 : ℝ)^1681
        have hw : |(826172701/2000000000 : ℝ)|=(826172701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2242890311/5000000000 : ℝ)|^2193 ≤ (4392428083457/12500000000000 : ℝ)^1681
        have hw : |(2242890311/5000000000 : ℝ)|=(2242890311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s4_4 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-986710181/5000000000 : ℝ)*x 0 + (2623070209/5000000000 : ℝ)*x 1 + (1081834751/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (986710181/5000000000 : ℝ)^2193 ≤ (6019039161507/50000000000000 : ℝ)^1681 := by
    have hnat : (986710181 : ℕ)^2193*50000000000000^1681 ≤ 6019039161507^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      986710181 5000000000 6019039161507 50000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623070209/5000000000 : ℝ)^2193 ≤ (10775776854347/25000000000000 : ℝ)^1681 := by
    have hnat : (2623070209 : ℕ)^2193*25000000000000^1681 ≤ 10775776854347^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623070209 5000000000 10775776854347 25000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081834751/2000000000 : ℝ)^2193 ≤ (22429407118307/50000000000000 : ℝ)^1681 := by
    have hnat : (1081834751 : ℕ)^2193*50000000000000^1681 ≤ 22429407118307^1681*2000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081834751 2000000000 22429407118307 50000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-986710181/5000000000 : ℝ), (2623070209/5000000000 : ℝ), (1081834751/2000000000 : ℝ)] ![(6019039161507/50000000000000 : ℝ), (10775776854347/25000000000000 : ℝ), (22429407118307/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-986710181/5000000000 : ℝ)|^2193 ≤ (6019039161507/50000000000000 : ℝ)^1681
        have hw : |(-986710181/5000000000 : ℝ)|=(986710181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623070209/5000000000 : ℝ)|^2193 ≤ (10775776854347/25000000000000 : ℝ)^1681
        have hw : |(2623070209/5000000000 : ℝ)|=(2623070209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081834751/2000000000 : ℝ)|^2193 ≤ (22429407118307/50000000000000 : ℝ)^1681
        have hw : |(1081834751/2000000000 : ℝ)|=(1081834751/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s4_5 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305067869/10000000000 : ℝ)*x 0 + (-118338603/625000000 : ℝ)*x 1 + (1081834757/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305067869/10000000000 : ℝ)^2193 ≤ (10933951766697/25000000000000 : ℝ)^1681 := by
    have hnat : (5305067869 : ℕ)^2193*25000000000000^1681 ≤ 10933951766697^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305067869 10000000000 10933951766697 25000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (118338603/625000000 : ℝ)^2193 ≤ (356418073707/3125000000000 : ℝ)^1681 := by
    have hnat : (118338603 : ℕ)^2193*3125000000000^1681 ≤ 356418073707^1681*625000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118338603 625000000 356418073707 3125000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081834757/2000000000 : ℝ)^2193 ≤ (8971762912237/20000000000000 : ℝ)^1681 := by
    have hnat : (1081834757 : ℕ)^2193*20000000000000^1681 ≤ 8971762912237^1681*2000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081834757 2000000000 8971762912237 20000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305067869/10000000000 : ℝ), (-118338603/625000000 : ℝ), (1081834757/2000000000 : ℝ)] ![(10933951766697/25000000000000 : ℝ), (356418073707/3125000000000 : ℝ), (8971762912237/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305067869/10000000000 : ℝ)|^2193 ≤ (10933951766697/25000000000000 : ℝ)^1681
        have hw : |(5305067869/10000000000 : ℝ)|=(5305067869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-118338603/625000000 : ℝ)|^2193 ≤ (356418073707/3125000000000 : ℝ)^1681
        have hw : |(-118338603/625000000 : ℝ)|=(118338603/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081834757/2000000000 : ℝ)|^2193 ≤ (8971762912237/20000000000000 : ℝ)^1681
        have hw : |(1081834757/2000000000 : ℝ)|=(1081834757/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s4_6 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305067869/10000000000 : ℝ)*x 0 + (5409173789/10000000000 : ℝ)*x 1 + (-946708821/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305067869/10000000000 : ℝ)^2193 ≤ (10933951766697/25000000000000 : ℝ)^1681 := by
    have hnat : (5305067869 : ℕ)^2193*25000000000000^1681 ≤ 10933951766697^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305067869 10000000000 10933951766697 25000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409173789/10000000000 : ℝ)^2193 ≤ (44858814604461/100000000000000 : ℝ)^1681 := by
    have hnat : (5409173789 : ℕ)^2193*100000000000000^1681 ≤ 44858814604461^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409173789 10000000000 44858814604461 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (946708821/5000000000 : ℝ)^2193 ≤ (11405378311473/100000000000000 : ℝ)^1681 := by
    have hnat : (946708821 : ℕ)^2193*100000000000000^1681 ≤ 11405378311473^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      946708821 5000000000 11405378311473 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305067869/10000000000 : ℝ), (5409173789/10000000000 : ℝ), (-946708821/5000000000 : ℝ)] ![(10933951766697/25000000000000 : ℝ), (44858814604461/100000000000000 : ℝ), (11405378311473/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305067869/10000000000 : ℝ)|^2193 ≤ (10933951766697/25000000000000 : ℝ)^1681
        have hw : |(5305067869/10000000000 : ℝ)|=(5305067869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409173789/10000000000 : ℝ)|^2193 ≤ (44858814604461/100000000000000 : ℝ)^1681
        have hw : |(5409173789/10000000000 : ℝ)|=(5409173789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-946708821/5000000000 : ℝ)|^2193 ≤ (11405378311473/100000000000000 : ℝ)^1681
        have hw : |(-946708821/5000000000 : ℝ)|=(946708821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s4_7 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4305053809/10000000000 : ℝ)*x 0 + (4484479561/10000000000 : ℝ)*x 1 + (4132171403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4305053809/10000000000 : ℝ)^2193 ≤ (33303935680279/100000000000000 : ℝ)^1681 := by
    have hnat : (4305053809 : ℕ)^2193*100000000000000^1681 ≤ 33303935680279^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4305053809 10000000000 33303935680279 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4484479561/10000000000 : ℝ)^2193 ≤ (35126129126813/100000000000000 : ℝ)^1681 := by
    have hnat : (4484479561 : ℕ)^2193*100000000000000^1681 ≤ 35126129126813^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484479561 10000000000 35126129126813 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4132171403/10000000000 : ℝ)^2193 ≤ (7892483791543/25000000000000 : ℝ)^1681 := by
    have hnat : (4132171403 : ℕ)^2193*25000000000000^1681 ≤ 7892483791543^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4132171403 10000000000 7892483791543 25000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4305053809/10000000000 : ℝ), (4484479561/10000000000 : ℝ), (4132171403/10000000000 : ℝ)] ![(33303935680279/100000000000000 : ℝ), (35126129126813/100000000000000 : ℝ), (7892483791543/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4305053809/10000000000 : ℝ)|^2193 ≤ (33303935680279/100000000000000 : ℝ)^1681
        have hw : |(4305053809/10000000000 : ℝ)|=(4305053809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4484479561/10000000000 : ℝ)|^2193 ≤ (35126129126813/100000000000000 : ℝ)^1681
        have hw : |(4484479561/10000000000 : ℝ)|=(4484479561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4132171403/10000000000 : ℝ)|^2193 ≤ (7892483791543/25000000000000 : ℝ)^1681
        have hw : |(4132171403/10000000000 : ℝ)|=(4132171403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1426_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79023921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3737/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (697/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (5653/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2957/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3737/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (697/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3737/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (697/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3737/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (697/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3737/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (697/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3737/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (697/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3737/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (697/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (697/6250 : ℝ) ^ (4385/1024 : ℝ) ≤ (130127388295659/1562500000000000000 : ℝ) := by
    have hpowers : (697/6250 : ℝ)^4385 ≤ (130127388295659/1562500000000000000 : ℝ)^1024 := by
      have hnat : (697 : ℕ)^4385*1562500000000000000^1024 ≤ 130127388295659^1024*6250^4385 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        697 6250 130127388295659 1562500000000000000 4385 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (697/6250 : ℝ)) (X := (130127388295659/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3737/25000 : ℝ) ^ (4385/1024 : ℝ) ≤ (7299914744074537/25000000000000000000 : ℝ) := by
    have hpowers : (3737/25000 : ℝ)^4385 ≤ (7299914744074537/25000000000000000000 : ℝ)^1024 := by
      have hnat : (3737 : ℕ)^4385*25000000000000000000^1024 ≤ 7299914744074537^1024*25000^4385 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3737 25000 7299914744074537 25000000000000000000 4385 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3737/25000 : ℝ)) (X := (7299914744074537/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (781380127388295659/781250000000000000 : ℝ) ≤ (10000388938846073/10000000000000000 : ℝ) ^ (4385/1024 : ℝ) := by
    have hpowers : (781380127388295659/781250000000000000 : ℝ)^1024 ≤ (10000388938846073/10000000000000000 : ℝ)^4385 := by
      have hnat : (781380127388295659 : ℕ)^1024*10000000000000000^4385 ≤ 10000388938846073^4385*781250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781380127388295659 781250000000000000 10000388938846073 10000000000000000 1024 4385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000388938846073/10000000000000000 : ℝ)) (X := (781380127388295659/781250000000000000 : ℝ)) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25009381952956805081/25000000000000000000 : ℝ) ≤ (10000876236116569/10000000000000000 : ℝ) ^ (4385/1024 : ℝ) := by
    have hpowers : (25009381952956805081/25000000000000000000 : ℝ)^1024 ≤ (10000876236116569/10000000000000000 : ℝ)^4385 := by
      have hnat : (25009381952956805081 : ℕ)^1024*10000000000000000^4385 ≤ 10000876236116569^4385*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009381952956805081 25000000000000000000 10000876236116569 10000000000000000 1024 4385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000876236116569/10000000000000000 : ℝ)) (X := (25009381952956805081/25000000000000000000 : ℝ)) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507299914744074537/12500000000000000000 : ℝ) ≤ (2000272706677413/2000000000000000 : ℝ) ^ (4385/1024 : ℝ) := by
    have hpowers : (12507299914744074537/12500000000000000000 : ℝ)^1024 ≤ (2000272706677413/2000000000000000 : ℝ)^4385 := by
      have hnat : (12507299914744074537 : ℕ)^1024*2000000000000000^4385 ≤ 2000272706677413^4385*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507299914744074537 12500000000000000000 2000272706677413 2000000000000000 1024 4385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000272706677413/2000000000000000 : ℝ)) (X := (12507299914744074537/12500000000000000000 : ℝ)) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(130127388295659/1562500000000000000 : ℝ) ≤ ((9487651933384637581/9490000000000000000 : ℝ)+2*(15228039703/11862500000000 : ℝ)*(697/6250 : ℝ))^(4385/1024 : ℝ) := by
    rw [show (9487651933384637581/9490000000000000000 : ℝ)+2*(15228039703/11862500000000 : ℝ)*(697/6250 : ℝ)=(10000388938846073/10000000000000000 : ℝ) by norm_num, show 1+2*(130127388295659/1562500000000000000 : ℝ)=(781380127388295659/781250000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7299914744074537/25000000000000000000 : ℝ)+(130127388295659/1562500000000000000 : ℝ) ≤ ((9487651933384637581/9490000000000000000 : ℝ)+(15228039703/11862500000000 : ℝ)*((3737/25000 : ℝ)+(697/6250 : ℝ)))^(4385/1024 : ℝ) := by
    rw [show (9487651933384637581/9490000000000000000 : ℝ)+(15228039703/11862500000000 : ℝ)*((3737/25000 : ℝ)+(697/6250 : ℝ))=(10000876236116569/10000000000000000 : ℝ) by norm_num, show 1+(7299914744074537/25000000000000000000 : ℝ)+(130127388295659/1562500000000000000 : ℝ)=(25009381952956805081/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7299914744074537/25000000000000000000 : ℝ) ≤ ((9487651933384637581/9490000000000000000 : ℝ)+2*(15228039703/11862500000000 : ℝ)*(3737/25000 : ℝ))^(4385/1024 : ℝ) := by
    rw [show (9487651933384637581/9490000000000000000 : ℝ)+2*(15228039703/11862500000000 : ℝ)*(3737/25000 : ℝ)=(2000272706677413/2000000000000000 : ℝ) by norm_num, show 1+2*(7299914744074537/25000000000000000000 : ℝ)=(12507299914744074537/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9487651933384637581/9490000000000000000 : ℝ)*(X 1 0+X 2 0)+(15228039703/11862500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4385/1024 : ℝ)) (lo := (697/6250 : ℝ)) (hi := (3737/25000 : ℝ)) (c := (9487651933384637581/9490000000000000000 : ℝ)) (alpha := (15228039703/11862500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9487651933384637581/9490000000000000000 : ℝ)*(X 0 1+X 2 1)+(15228039703/11862500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4385/1024 : ℝ)) (lo := (697/6250 : ℝ)) (hi := (3737/25000 : ℝ)) (c := (9487651933384637581/9490000000000000000 : ℝ)) (alpha := (15228039703/11862500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9487651933384637581/9490000000000000000 : ℝ)*(X 0 2+X 1 2)+(15228039703/11862500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4385/1024 : ℝ)) (lo := (697/6250 : ℝ)) (hi := (3737/25000 : ℝ)) (c := (9487651933384637581/9490000000000000000 : ℝ)) (alpha := (15228039703/11862500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1973408369/10000000000 : ℝ)*X 0 0+(5409779163/10000000000 : ℝ)*X 0 1+(209821529/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((33423457/62500000 : ℝ)*X 1 0+(-411410629/2000000000 : ℝ)*X 1 1+(1311384617/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673876573/5000000000 : ℝ)*X 2 0+(327846159/625000000 : ℝ)*X 2 1+(-205705301/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4305028019/10000000000 : ℝ)*X 0 0+(826172701/2000000000 : ℝ)*X 0 1+(2242890311/5000000000 : ℝ)*X 0 2+(4305028019/10000000000 : ℝ)*X 1 0+(826172701/2000000000 : ℝ)*X 1 1+(2242890311/5000000000 : ℝ)*X 1 2+(4305028019/10000000000 : ℝ)*X 2 0+(826172701/2000000000 : ℝ)*X 2 1+(2242890311/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-986710181/5000000000 : ℝ)*X 0 0+(2623070209/5000000000 : ℝ)*X 0 1+(1081834751/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305067869/10000000000 : ℝ)*X 1 0+(-118338603/625000000 : ℝ)*X 1 1+(1081834757/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305067869/10000000000 : ℝ)*X 2 0+(5409173789/10000000000 : ℝ)*X 2 1+(-946708821/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4305053809/10000000000 : ℝ)*X 0 0+(4484479561/10000000000 : ℝ)*X 0 1+(4132171403/10000000000 : ℝ)*X 0 2+(4305053809/10000000000 : ℝ)*X 1 0+(4484479561/10000000000 : ℝ)*X 1 1+(4132171403/10000000000 : ℝ)*X 1 2+(4305053809/10000000000 : ℝ)*X 2 0+(4484479561/10000000000 : ℝ)*X 2 1+(4132171403/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2020125243110949925858154643/237250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (221632111/20000000000000 : ℝ)*(base19) + (488236831/50000000000000 : ℝ)*(base23) + (43126731/50000000000000 : ℝ)*(lower2) + (122301149/100000000000000 : ℝ)*(upper3) + (179197367/100000000000000 : ℝ)*(upper5) + (2226565965966699/50000000000000 : ℝ)*(major0) + (2226565965966699/50000000000000 : ℝ)*(major1) + (2226565965966699/50000000000000 : ℝ)*(major2) + (6088645040421631/100000000000000 : ℝ)*(sp0) + (761084712226771/12500000000000 : ℝ)*(sp1) + (6088677829501061/100000000000000 : ℝ)*(sp2) + (281757198176773/10000000000000 : ℝ)*(sp3) + (8441388273/25000000000000 : ℝ)*(sp4) + (511691969/4000000000000 : ℝ)*(sp7) + (563516954813391/20000000000000 : ℝ)*(f.failure) + (6088678805974723/100000000000000 : ℝ)*(f.sum) + (1183624557889/593125000000000000000000000 : ℝ)*base65 + (584007184939515119/474500000000000000000000000000000 : ℝ)*base67 + (2999043744082515119/474500000000000000000000000000000 : ℝ)*base69 + (328146879849984881/474500000000000000000000000000000 : ℝ)*base72 + (22024706212323/4745000000000000000000000000 : ℝ)*base74 + (3609113336097984881/474500000000000000000000000000000 : ℝ)*base76 + (1346418782673015119/474500000000000000000000000000000 : ℝ)*base77 + (9324274468252015119/474500000000000000000000000000000 : ℝ)*base79 + (14358190498227/4745000000000000000000000000 : ℝ)*base81 + (126111/1000000000000000000000 : ℝ)*base89 + (126111/1000000000000000000000 : ℝ)*base91 + (126111/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (479572081824528676497389073/59312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1345550059/100000000000000 : ℝ)*(base19) + (22846563/1562500000000 : ℝ)*(base23) + (45274589/25000000000000 : ℝ)*(upper3) + (23898233/50000000000000 : ℝ)*(lower4) + (72033859/50000000000000 : ℝ)*(upper5) + (560758573032311/12500000000000 : ℝ)*(major0) + (560758573032311/12500000000000 : ℝ)*(major1) + (560758573032311/12500000000000 : ℝ)*(major2) + (2780704301/10000000000000 : ℝ)*(sp1) + (31104773401/100000000000000 : ℝ)*(sp2) + (3066856226324319/50000000000000 : ℝ)*(sp4) + (613368330005557/10000000000000 : ℝ)*(sp5) + (3066839942847603/50000000000000 : ℝ)*(sp6) + (141921222317559/5000000000000 : ℝ)*(sp7) + (141921222317559/5000000000000 : ℝ)*(f.failure) + (3066856226324319/50000000000000 : ℝ)*(f.sum) + (45641860099/148281250000000000000000000 : ℝ)*base66 + (946016866827279691/118625000000000000000000000000000 : ℝ)*base67 + (416911576935529691/118625000000000000000000000000000 : ℝ)*base69 + (534415242949470309/118625000000000000000000000000000 : ℝ)*base72 + (11846617257931/2372500000000000000000000000 : ℝ)*base73 + (255294238384470309/118625000000000000000000000000000 : ℝ)*base76 + (44450579758220309/118625000000000000000000000000000 : ℝ)*base78 + (323884279585970309/118625000000000000000000000000000 : ℝ)*base80 + (6930018821701/2372500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (671161/250000000000000000000 : ℝ)*base90 + (671161/250000000000000000000 : ℝ)*base92 + (671161/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1426_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79023921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3737/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (697/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5653/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2957/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1426_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1426_s5_0 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-123346577/625000000 : ℝ)*x 0 + (5408560697/10000000000 : ℝ)*x 1 + (5246666489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (123346577/625000000 : ℝ)^2193 ≤ (2407814411689/20000000000000 : ℝ)^1681 := by
    have hnat : (123346577 : ℕ)^2193*20000000000000^1681 ≤ 2407814411689^1681*625000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123346577 625000000 2407814411689 20000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408560697/10000000000 : ℝ)^2193 ≤ (8970436333319/20000000000000 : ℝ)^1681 := by
    have hnat : (5408560697 : ℕ)^2193*20000000000000^1681 ≤ 8970436333319^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408560697 10000000000 8970436333319 20000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246666489/10000000000 : ℝ)^2193 ≤ (43108746267907/100000000000000 : ℝ)^1681 := by
    have hnat : (5246666489 : ℕ)^2193*100000000000000^1681 ≤ 43108746267907^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246666489 10000000000 43108746267907 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-123346577/625000000 : ℝ), (5408560697/10000000000 : ℝ), (5246666489/10000000000 : ℝ)] ![(2407814411689/20000000000000 : ℝ), (8970436333319/20000000000000 : ℝ), (43108746267907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-123346577/625000000 : ℝ)|^2193 ≤ (2407814411689/20000000000000 : ℝ)^1681
        have hw : |(-123346577/625000000 : ℝ)|=(123346577/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408560697/10000000000 : ℝ)|^2193 ≤ (8970436333319/20000000000000 : ℝ)^1681
        have hw : |(5408560697/10000000000 : ℝ)|=(5408560697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246666489/10000000000 : ℝ)|^2193 ≤ (43108746267907/100000000000000 : ℝ)^1681
        have hw : |(5246666489/10000000000 : ℝ)|=(5246666489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s5_1 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2673719323/5000000000 : ℝ)*x 0 + (-205597343/1000000000 : ℝ)*x 1 + (1049333311/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673719323/5000000000 : ℝ)^2193 ≤ (11048016267017/25000000000000 : ℝ)^1681 := by
    have hnat : (2673719323 : ℕ)^2193*25000000000000^1681 ≤ 11048016267017^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673719323 5000000000 11048016267017 25000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (205597343/1000000000 : ℝ)^2193 ≤ (12699187938497/100000000000000 : ℝ)^1681 := by
    have hnat : (205597343 : ℕ)^2193*100000000000000^1681 ≤ 12699187938497^1681*1000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205597343 1000000000 12699187938497 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049333311/2000000000 : ℝ)^2193 ≤ (43108746975359/100000000000000 : ℝ)^1681 := by
    have hnat : (1049333311 : ℕ)^2193*100000000000000^1681 ≤ 43108746975359^1681*2000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049333311 2000000000 43108746975359 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673719323/5000000000 : ℝ), (-205597343/1000000000 : ℝ), (1049333311/2000000000 : ℝ)] ![(11048016267017/25000000000000 : ℝ), (12699187938497/100000000000000 : ℝ), (43108746975359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673719323/5000000000 : ℝ)|^2193 ≤ (11048016267017/25000000000000 : ℝ)^1681
        have hw : |(2673719323/5000000000 : ℝ)|=(2673719323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-205597343/1000000000 : ℝ)|^2193 ≤ (12699187938497/100000000000000 : ℝ)^1681
        have hw : |(-205597343/1000000000 : ℝ)|=(205597343/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049333311/2000000000 : ℝ)|^2193 ≤ (43108746975359/100000000000000 : ℝ)^1681
        have hw : |(1049333311/2000000000 : ℝ)|=(1049333311/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s5_2 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5347438783/10000000000 : ℝ)*x 0 + (209866659/400000000 : ℝ)*x 1 + (-2055973353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347438783/10000000000 : ℝ)^2193 ≤ (441920665451/1000000000000 : ℝ)^1681 := by
    have hnat : (5347438783 : ℕ)^2193*1000000000000^1681 ≤ 441920665451^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347438783 10000000000 441920665451 1000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209866659/400000000 : ℝ)^2193 ≤ (21554373058921/50000000000000 : ℝ)^1681 := by
    have hnat : (209866659 : ℕ)^2193*50000000000000^1681 ≤ 21554373058921^1681*400000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209866659 400000000 21554373058921 50000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2055973353/10000000000 : ℝ)^2193 ≤ (3174796829507/25000000000000 : ℝ)^1681 := by
    have hnat : (2055973353 : ℕ)^2193*25000000000000^1681 ≤ 3174796829507^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2055973353 10000000000 3174796829507 25000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347438783/10000000000 : ℝ), (209866659/400000000 : ℝ), (-2055973353/10000000000 : ℝ)] ![(441920665451/1000000000000 : ℝ), (21554373058921/50000000000000 : ℝ), (3174796829507/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347438783/10000000000 : ℝ)|^2193 ≤ (441920665451/1000000000000 : ℝ)^1681
        have hw : |(5347438783/10000000000 : ℝ)|=(5347438783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209866659/400000000 : ℝ)|^2193 ≤ (21554373058921/50000000000000 : ℝ)^1681
        have hw : |(209866659/400000000 : ℝ)|=(209866659/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2055973353/10000000000 : ℝ)|^2193 ≤ (3174796829507/25000000000000 : ℝ)^1681
        have hw : |(-2055973353/10000000000 : ℝ)|=(2055973353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s5_3 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4305111511/10000000000 : ℝ)*x 0 + (4133388797/10000000000 : ℝ)*x 1 + (4483235037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4305111511/10000000000 : ℝ)^2193 ≤ (16652259012167/50000000000000 : ℝ)^1681 := by
    have hnat : (4305111511 : ℕ)^2193*50000000000000^1681 ≤ 16652259012167^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4305111511 10000000000 16652259012167 50000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4133388797/10000000000 : ℝ)^2193 ≤ (3947758690931/12500000000000 : ℝ)^1681 := by
    have hnat : (4133388797 : ℕ)^2193*12500000000000^1681 ≤ 3947758690931^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4133388797 10000000000 3947758690931 12500000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4483235037/10000000000 : ℝ)^2193 ≤ (17556706218433/50000000000000 : ℝ)^1681 := by
    have hnat : (4483235037 : ℕ)^2193*50000000000000^1681 ≤ 17556706218433^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483235037 10000000000 17556706218433 50000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4305111511/10000000000 : ℝ), (4133388797/10000000000 : ℝ), (4483235037/10000000000 : ℝ)] ![(16652259012167/50000000000000 : ℝ), (3947758690931/12500000000000 : ℝ), (17556706218433/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4305111511/10000000000 : ℝ)|^2193 ≤ (16652259012167/50000000000000 : ℝ)^1681
        have hw : |(4305111511/10000000000 : ℝ)|=(4305111511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4133388797/10000000000 : ℝ)|^2193 ≤ (3947758690931/12500000000000 : ℝ)^1681
        have hw : |(4133388797/10000000000 : ℝ)|=(4133388797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4483235037/10000000000 : ℝ)|^2193 ≤ (17556706218433/50000000000000 : ℝ)^1681
        have hw : |(4483235037/10000000000 : ℝ)|=(4483235037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s5_4 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-986778277/5000000000 : ℝ)*x 0 + (2623625817/5000000000 : ℝ)*x 1 + (1081594519/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (986778277/5000000000 : ℝ)^2193 ≤ (6019581080839/50000000000000 : ℝ)^1681 := by
    have hnat : (986778277 : ℕ)^2193*50000000000000^1681 ≤ 6019581080839^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      986778277 5000000000 6019581080839 50000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623625817/5000000000 : ℝ)^2193 ≤ (21557509261599/50000000000000 : ℝ)^1681 := by
    have hnat : (2623625817 : ℕ)^2193*50000000000000^1681 ≤ 21557509261599^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623625817 5000000000 21557509261599 50000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081594519/2000000000 : ℝ)^2193 ≤ (22422909653237/50000000000000 : ℝ)^1681 := by
    have hnat : (1081594519 : ℕ)^2193*50000000000000^1681 ≤ 22422909653237^1681*2000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081594519 2000000000 22422909653237 50000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-986778277/5000000000 : ℝ), (2623625817/5000000000 : ℝ), (1081594519/2000000000 : ℝ)] ![(6019581080839/50000000000000 : ℝ), (21557509261599/50000000000000 : ℝ), (22422909653237/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-986778277/5000000000 : ℝ)|^2193 ≤ (6019581080839/50000000000000 : ℝ)^1681
        have hw : |(-986778277/5000000000 : ℝ)|=(986778277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623625817/5000000000 : ℝ)|^2193 ≤ (21557509261599/50000000000000 : ℝ)^1681
        have hw : |(2623625817/5000000000 : ℝ)|=(2623625817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081594519/2000000000 : ℝ)|^2193 ≤ (22422909653237/50000000000000 : ℝ)^1681
        have hw : |(1081594519/2000000000 : ℝ)|=(1081594519/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s5_5 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (331585187/625000000 : ℝ)*x 0 + (-189466733/1000000000 : ℝ)*x 1 + (2703986281/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331585187/625000000 : ℝ)^2193 ≤ (21869490595271/50000000000000 : ℝ)^1681 := by
    have hnat : (331585187 : ℕ)^2193*50000000000000^1681 ≤ 21869490595271^1681*625000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331585187 625000000 21869490595271 50000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (189466733/1000000000 : ℝ)^2193 ≤ (356724995251/3125000000000 : ℝ)^1681 := by
    have hnat : (189466733 : ℕ)^2193*3125000000000^1681 ≤ 356724995251^1681*1000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      189466733 1000000000 356724995251 3125000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703986281/5000000000 : ℝ)^2193 ≤ (4484581894947/10000000000000 : ℝ)^1681 := by
    have hnat : (2703986281 : ℕ)^2193*10000000000000^1681 ≤ 4484581894947^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703986281 5000000000 4484581894947 10000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331585187/625000000 : ℝ), (-189466733/1000000000 : ℝ), (2703986281/5000000000 : ℝ)] ![(21869490595271/50000000000000 : ℝ), (356724995251/3125000000000 : ℝ), (4484581894947/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331585187/625000000 : ℝ)|^2193 ≤ (21869490595271/50000000000000 : ℝ)^1681
        have hw : |(331585187/625000000 : ℝ)|=(331585187/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-189466733/1000000000 : ℝ)|^2193 ≤ (356724995251/3125000000000 : ℝ)^1681
        have hw : |(-189466733/1000000000 : ℝ)|=(189466733/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703986281/5000000000 : ℝ)|^2193 ≤ (4484581894947/10000000000000 : ℝ)^1681
        have hw : |(2703986281/5000000000 : ℝ)|=(2703986281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s5_6 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (26526817/50000000 : ℝ)*x 0 + (43263779/80000000 : ℝ)*x 1 + (-189466703/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26526817/50000000 : ℝ)^2193 ≤ (10934746394681/25000000000000 : ℝ)^1681 := by
    have hnat : (26526817 : ℕ)^2193*25000000000000^1681 ≤ 10934746394681^1681*50000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26526817 50000000 10934746394681 25000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43263779/80000000 : ℝ)^2193 ≤ (44845816926451/100000000000000 : ℝ)^1681 := by
    have hnat : (43263779 : ℕ)^2193*100000000000000^1681 ≤ 44845816926451^1681*80000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43263779 80000000 44845816926451 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (189466703/1000000000 : ℝ)^2193 ≤ (5707598745019/50000000000000 : ℝ)^1681 := by
    have hnat : (189466703 : ℕ)^2193*50000000000000^1681 ≤ 5707598745019^1681*1000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      189466703 1000000000 5707598745019 50000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26526817/50000000 : ℝ), (43263779/80000000 : ℝ), (-189466703/1000000000 : ℝ)] ![(10934746394681/25000000000000 : ℝ), (44845816926451/100000000000000 : ℝ), (5707598745019/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26526817/50000000 : ℝ)|^2193 ≤ (10934746394681/25000000000000 : ℝ)^1681
        have hw : |(26526817/50000000 : ℝ)|=(26526817/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(43263779/80000000 : ℝ)|^2193 ≤ (44845816926451/100000000000000 : ℝ)^1681
        have hw : |(43263779/80000000 : ℝ)|=(43263779/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-189466703/1000000000 : ℝ)|^2193 ≤ (5707598745019/50000000000000 : ℝ)^1681
        have hw : |(-189466703/1000000000 : ℝ)|=(189466703/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s5_7 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4305136157/10000000000 : ℝ)*x 0 + (2240985361/5000000000 : ℝ)*x 1 + (103366493/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4305136157/10000000000 : ℝ)^2193 ≤ (33304766759099/100000000000000 : ℝ)^1681 := by
    have hnat : (4305136157 : ℕ)^2193*100000000000000^1681 ≤ 33304766759099^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4305136157 10000000000 33304766759099 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2240985361/5000000000 : ℝ)^2193 ≤ (3510049462113/10000000000000 : ℝ)^1681 := by
    have hnat : (2240985361 : ℕ)^2193*10000000000000^1681 ≤ 3510049462113^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240985361 5000000000 3510049462113 10000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (103366493/250000000 : ℝ)^2193 ≤ (7898684649969/25000000000000 : ℝ)^1681 := by
    have hnat : (103366493 : ℕ)^2193*25000000000000^1681 ≤ 7898684649969^1681*250000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103366493 250000000 7898684649969 25000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4305136157/10000000000 : ℝ), (2240985361/5000000000 : ℝ), (103366493/250000000 : ℝ)] ![(33304766759099/100000000000000 : ℝ), (3510049462113/10000000000000 : ℝ), (7898684649969/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4305136157/10000000000 : ℝ)|^2193 ≤ (33304766759099/100000000000000 : ℝ)^1681
        have hw : |(4305136157/10000000000 : ℝ)|=(4305136157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2240985361/5000000000 : ℝ)|^2193 ≤ (3510049462113/10000000000000 : ℝ)^1681
        have hw : |(2240985361/5000000000 : ℝ)|=(2240985361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(103366493/250000000 : ℝ)|^2193 ≤ (7898684649969/25000000000000 : ℝ)^1681
        have hw : |(103366493/250000000 : ℝ)|=(103366493/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1426_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79023921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2957/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5653/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1133/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14759/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2957/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5653/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2957/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5653/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2957/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5653/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2957/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5653/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2957/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5653/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2957/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5653/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5653/50000 : ℝ) ^ (4385/1024 : ℝ) ≤ (8831908732688063/100000000000000000000 : ℝ) := by
    have hpowers : (5653/50000 : ℝ)^4385 ≤ (8831908732688063/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5653 : ℕ)^4385*100000000000000000000^1024 ≤ 8831908732688063^1024*50000^4385 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5653 50000 8831908732688063 100000000000000000000 4385 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5653/50000 : ℝ)) (X := (8831908732688063/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2957/20000 : ℝ) ^ (4385/1024 : ℝ) ≤ (5572073525961319/20000000000000000000 : ℝ) := by
    have hpowers : (2957/20000 : ℝ)^4385 ≤ (5572073525961319/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2957 : ℕ)^4385*20000000000000000000^1024 ≤ 5572073525961319^1024*20000^4385 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2957 20000 5572073525961319 20000000000000000000 4385 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2957/20000 : ℝ)) (X := (5572073525961319/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008831908732688063/50000000000000000000 : ℝ) ≤ (10000412463506739/10000000000000000 : ℝ) ^ (4385/1024 : ℝ) := by
    have hpowers : (50008831908732688063/50000000000000000000 : ℝ)^1024 ≤ (10000412463506739/10000000000000000 : ℝ)^4385 := by
      have hnat : (50008831908732688063 : ℕ)^1024*10000000000000000^4385 ≤ 10000412463506739^4385*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008831908732688063 50000000000000000000 10000412463506739 10000000000000000 1024 4385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000412463506739/10000000000000000 : ℝ)) (X := (50008831908732688063/50000000000000000000 : ℝ)) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018346138181247329/50000000000000000000 : ℝ) ≤ (10000856729958479/10000000000000000 : ℝ) ^ (4385/1024 : ℝ) := by
    have hpowers : (50018346138181247329/50000000000000000000 : ℝ)^1024 ≤ (10000856729958479/10000000000000000 : ℝ)^4385 := by
      have hnat : (50018346138181247329 : ℕ)^1024*10000000000000000^4385 ≤ 10000856729958479^4385*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018346138181247329 50000000000000000000 10000856729958479 10000000000000000 1024 4385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000856729958479/10000000000000000 : ℝ)) (X := (50018346138181247329/50000000000000000000 : ℝ)) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10005572073525961319/10000000000000000000 : ℝ) ≤ (10001300996410219/10000000000000000 : ℝ) ^ (4385/1024 : ℝ) := by
    have hpowers : (10005572073525961319/10000000000000000000 : ℝ)^1024 ≤ (10001300996410219/10000000000000000 : ℝ)^4385 := by
      have hnat : (10005572073525961319 : ℕ)^1024*10000000000000000^4385 ≤ 10001300996410219^4385*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005572073525961319 10000000000000000000 10001300996410219 10000000000000000 1024 4385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001300996410219/10000000000000000 : ℝ)) (X := (10005572073525961319/10000000000000000000 : ℝ)) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8831908732688063/100000000000000000000 : ℝ) ≤ ((34781389207533200101/34790000000000000000 : ℝ)+2*(22213322587/17395000000000 : ℝ)*(5653/50000 : ℝ))^(4385/1024 : ℝ) := by
    rw [show (34781389207533200101/34790000000000000000 : ℝ)+2*(22213322587/17395000000000 : ℝ)*(5653/50000 : ℝ)=(10000412463506739/10000000000000000 : ℝ) by norm_num, show 1+2*(8831908732688063/100000000000000000000 : ℝ)=(50008831908732688063/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5572073525961319/20000000000000000000 : ℝ)+(8831908732688063/100000000000000000000 : ℝ) ≤ ((34781389207533200101/34790000000000000000 : ℝ)+(22213322587/17395000000000 : ℝ)*((2957/20000 : ℝ)+(5653/50000 : ℝ)))^(4385/1024 : ℝ) := by
    rw [show (34781389207533200101/34790000000000000000 : ℝ)+(22213322587/17395000000000 : ℝ)*((2957/20000 : ℝ)+(5653/50000 : ℝ))=(10000856729958479/10000000000000000 : ℝ) by norm_num, show 1+(5572073525961319/20000000000000000000 : ℝ)+(8831908732688063/100000000000000000000 : ℝ)=(50018346138181247329/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5572073525961319/20000000000000000000 : ℝ) ≤ ((34781389207533200101/34790000000000000000 : ℝ)+2*(22213322587/17395000000000 : ℝ)*(2957/20000 : ℝ))^(4385/1024 : ℝ) := by
    rw [show (34781389207533200101/34790000000000000000 : ℝ)+2*(22213322587/17395000000000 : ℝ)*(2957/20000 : ℝ)=(10001300996410219/10000000000000000 : ℝ) by norm_num, show 1+2*(5572073525961319/20000000000000000000 : ℝ)=(10005572073525961319/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34781389207533200101/34790000000000000000 : ℝ)*(X 1 0+X 2 0)+(22213322587/17395000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4385/1024 : ℝ)) (lo := (5653/50000 : ℝ)) (hi := (2957/20000 : ℝ)) (c := (34781389207533200101/34790000000000000000 : ℝ)) (alpha := (22213322587/17395000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34781389207533200101/34790000000000000000 : ℝ)*(X 0 1+X 2 1)+(22213322587/17395000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4385/1024 : ℝ)) (lo := (5653/50000 : ℝ)) (hi := (2957/20000 : ℝ)) (c := (34781389207533200101/34790000000000000000 : ℝ)) (alpha := (22213322587/17395000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34781389207533200101/34790000000000000000 : ℝ)*(X 0 2+X 1 2)+(22213322587/17395000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4385/1024 : ℝ)) (lo := (5653/50000 : ℝ)) (hi := (2957/20000 : ℝ)) (c := (34781389207533200101/34790000000000000000 : ℝ)) (alpha := (22213322587/17395000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-123346577/625000000 : ℝ)*X 0 0+(5408560697/10000000000 : ℝ)*X 0 1+(5246666489/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673719323/5000000000 : ℝ)*X 1 0+(-205597343/1000000000 : ℝ)*X 1 1+(1049333311/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347438783/10000000000 : ℝ)*X 2 0+(209866659/400000000 : ℝ)*X 2 1+(-2055973353/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4305111511/10000000000 : ℝ)*X 0 0+(4133388797/10000000000 : ℝ)*X 0 1+(4483235037/10000000000 : ℝ)*X 0 2+(4305111511/10000000000 : ℝ)*X 1 0+(4133388797/10000000000 : ℝ)*X 1 1+(4483235037/10000000000 : ℝ)*X 1 2+(4305111511/10000000000 : ℝ)*X 2 0+(4133388797/10000000000 : ℝ)*X 2 1+(4483235037/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-986778277/5000000000 : ℝ)*X 0 0+(2623625817/5000000000 : ℝ)*X 0 1+(1081594519/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((331585187/625000000 : ℝ)*X 1 0+(-189466733/1000000000 : ℝ)*X 1 1+(2703986281/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((26526817/50000000 : ℝ)*X 2 0+(43263779/80000000 : ℝ)*X 2 1+(-189466703/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4305136157/10000000000 : ℝ)*X 0 0+(2240985361/5000000000 : ℝ)*X 0 1+(103366493/250000000 : ℝ)*X 0 2+(4305136157/10000000000 : ℝ)*X 1 0+(2240985361/5000000000 : ℝ)*X 1 1+(103366493/250000000 : ℝ)*X 1 2+(4305136157/10000000000 : ℝ)*X 2 0+(2240985361/5000000000 : ℝ)*X 2 1+(103366493/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13720491004358972241097439079/1739500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (319302089/20000000000000 : ℝ)*(base19) + (1555127537/100000000000000 : ℝ)*(base23) + (26688347/25000000000000 : ℝ)*(lower2) + (95354139/50000000000000 : ℝ)*(upper3) + (42407329/25000000000000 : ℝ)*(upper5) + (2258844158920197/50000000000000 : ℝ)*(major0) + (2258844158920197/50000000000000 : ℝ)*(major1) + (903537663568079/20000000000000 : ℝ)*(major2) + (3088453872235223/50000000000000 : ℝ)*(sp0) + (1235388779637403/20000000000000 : ℝ)*(sp1) + (1544235984892481/25000000000000 : ℝ)*(sp2) + (178650863376143/6250000000000 : ℝ)*(sp3) + (18875113507/50000000000000 : ℝ)*(sp4) + (17064044821/100000000000000 : ℝ)*(sp7) + (714607719515777/25000000000000 : ℝ)*(f.failure) + (6176945494697461/100000000000000 : ℝ)*(f.sum) + (3121133347/49000000000000000000000000 : ℝ)*base66 + (15847630776665660103/1739500000000000000000000000000000 : ℝ)*base68 + (6410282303694375979/695800000000000000000000000000000 : ℝ)*base69 + (5583599209866160103/1739500000000000000000000000000000 : ℝ)*base72 + (122242568943/24500000000000000000000000 : ℝ)*base74 + (9251917048178575979/695800000000000000000000000000000 : ℝ)*base75 + (17071867337532160103/1739500000000000000000000000000000 : ℝ)*base78 + (15474970923051660103/1739500000000000000000000000000000 : ℝ)*base80 + (536935541699/869750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (5098383/1250000000000000000000 : ℝ)*base90 + (5098383/1250000000000000000000 : ℝ)*base92 + (17598383/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (81396781869267864238214079/49700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (470188787/100000000000000 : ℝ)*(base19) + (1313965013/100000000000000 : ℝ)*(base23) + (23552913/20000000000000 : ℝ)*(lower4) + (25042627/100000000000000 : ℝ)*(upper5) + (910123137414083/20000000000000 : ℝ)*(major0) + (910123137414083/20000000000000 : ℝ)*(major1) + (910123137414083/20000000000000 : ℝ)*(major2) + (12177141/100000000000000 : ℝ)*(sp0) + (1515565963/12500000000000 : ℝ)*(sp1) + (30195306583/100000000000000 : ℝ)*(sp2) + (6221966630622387/100000000000000 : ℝ)*(sp4) + (3110977024041519/50000000000000 : ℝ)*(sp5) + (6221935133527933/100000000000000 : ℝ)*(sp6) + (1439632338374609/50000000000000 : ℝ)*(sp7) + (1439632338374609/50000000000000 : ℝ)*(f.failure) + (6221966642799529/100000000000000 : ℝ)*(f.sum) + (208222058673/27179687500000000000000000 : ℝ)*base66 + (12341666393406622383/695800000000000000000000000000000 : ℝ)*base67 + (12597680337507222383/695800000000000000000000000000000 : ℝ)*base69 + (3436052143741622383/695800000000000000000000000000000 : ℝ)*base71 + (2770739240819/869750000000000000000000000 : ℝ)*base73 + (3104650723727622383/695800000000000000000000000000000 : ℝ)*base75 + (4890356102719422383/695800000000000000000000000000000 : ℝ)*base77 + (6433908190199622383/695800000000000000000000000000000 : ℝ)*base79 + (2769103566511/3479000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (4978111/2500000000000000000000 : ℝ)*base90 + (4978111/2500000000000000000000 : ℝ)*base92 + (4978111/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1426_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79023921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2957/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5653/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1133/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14759/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1426_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1426_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79023921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15809/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10351/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1133/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14759/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1426_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1426_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1426_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79023921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15809/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10351/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1133/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14759/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1426_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1267_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:19:55.676223+00:00
-- url     : https://prove2.me/submissions/3e4c8fb9-25ec-4228-91f6-d8919935f697

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
theorem support_rectangle_w1267_s6_0 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2108490067/10000000000 : ℝ)*x 0 + (1078179569/2000000000 : ℝ)*x 1 + (5267382911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2108490067/10000000000 : ℝ)^2115 ≤ (3206175750451/25000000000000 : ℝ)^1603 := by
    have hnat : (2108490067 : ℕ)^2115*25000000000000^1603 ≤ 3206175750451^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108490067 10000000000 3206175750451 25000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078179569/2000000000 : ℝ)^2115 ≤ (553176051399/1250000000000 : ℝ)^1603 := by
    have hnat : (1078179569 : ℕ)^2115*1250000000000^1603 ≤ 553176051399^1603*2000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078179569 2000000000 553176051399 1250000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267382911/10000000000 : ℝ)^2115 ≤ (42921212872469/100000000000000 : ℝ)^1603 := by
    have hnat : (5267382911 : ℕ)^2115*100000000000000^1603 ≤ 42921212872469^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267382911 10000000000 42921212872469 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2108490067/10000000000 : ℝ), (1078179569/2000000000 : ℝ), (5267382911/10000000000 : ℝ)] ![(3206175750451/25000000000000 : ℝ), (553176051399/1250000000000 : ℝ), (42921212872469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2108490067/10000000000 : ℝ)|^2115 ≤ (3206175750451/25000000000000 : ℝ)^1603
        have hw : |(-2108490067/10000000000 : ℝ)|=(2108490067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078179569/2000000000 : ℝ)|^2115 ≤ (553176051399/1250000000000 : ℝ)^1603
        have hw : |(1078179569/2000000000 : ℝ)|=(1078179569/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267382911/10000000000 : ℝ)|^2115 ≤ (42921212872469/100000000000000 : ℝ)^1603
        have hw : |(5267382911/10000000000 : ℝ)|=(5267382911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s6_1 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344215483/10000000000 : ℝ)*x 0 + (-2171111903/10000000000 : ℝ)*x 1 + (2633691453/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344215483/10000000000 : ℝ)^2115 ≤ (10937291854887/25000000000000 : ℝ)^1603 := by
    have hnat : (5344215483 : ℕ)^2115*25000000000000^1603 ≤ 10937291854887^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344215483 10000000000 10937291854887 25000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2171111903/10000000000 : ℝ)^2115 ≤ (6664809878891/50000000000000 : ℝ)^1603 := by
    have hnat : (2171111903 : ℕ)^2115*50000000000000^1603 ≤ 6664809878891^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171111903 10000000000 6664809878891 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633691453/5000000000 : ℝ)^2115 ≤ (42921212818713/100000000000000 : ℝ)^1603 := by
    have hnat : (2633691453 : ℕ)^2115*100000000000000^1603 ≤ 42921212818713^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633691453 5000000000 42921212818713 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344215483/10000000000 : ℝ), (-2171111903/10000000000 : ℝ), (2633691453/5000000000 : ℝ)] ![(10937291854887/25000000000000 : ℝ), (6664809878891/50000000000000 : ℝ), (42921212818713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344215483/10000000000 : ℝ)|^2115 ≤ (10937291854887/25000000000000 : ℝ)^1603
        have hw : |(5344215483/10000000000 : ℝ)|=(5344215483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2171111903/10000000000 : ℝ)|^2115 ≤ (6664809878891/50000000000000 : ℝ)^1603
        have hw : |(-2171111903/10000000000 : ℝ)|=(2171111903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633691453/5000000000 : ℝ)|^2115 ≤ (42921212818713/100000000000000 : ℝ)^1603
        have hw : |(2633691453/5000000000 : ℝ)|=(2633691453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s6_2 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (83503367/156250000 : ℝ)*x 0 + (1053476581/2000000000 : ℝ)*x 1 + (-271388987/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83503367/156250000 : ℝ)^2115 ≤ (43749167473553/100000000000000 : ℝ)^1603 := by
    have hnat : (83503367 : ℕ)^2115*100000000000000^1603 ≤ 43749167473553^1603*156250000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83503367 156250000 43749167473553 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053476581/2000000000 : ℝ)^2115 ≤ (21460606403981/50000000000000 : ℝ)^1603 := by
    have hnat : (1053476581 : ℕ)^2115*50000000000000^1603 ≤ 21460606403981^1603*2000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053476581 2000000000 21460606403981 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271388987/1250000000 : ℝ)^2115 ≤ (13329619701079/100000000000000 : ℝ)^1603 := by
    have hnat : (271388987 : ℕ)^2115*100000000000000^1603 ≤ 13329619701079^1603*1250000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271388987 1250000000 13329619701079 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83503367/156250000 : ℝ), (1053476581/2000000000 : ℝ), (-271388987/1250000000 : ℝ)] ![(43749167473553/100000000000000 : ℝ), (21460606403981/50000000000000 : ℝ), (13329619701079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83503367/156250000 : ℝ)|^2115 ≤ (43749167473553/100000000000000 : ℝ)^1603
        have hw : |(83503367/156250000 : ℝ)|=(83503367/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053476581/2000000000 : ℝ)|^2115 ≤ (21460606403981/50000000000000 : ℝ)^1603
        have hw : |(1053476581/2000000000 : ℝ)|=(1053476581/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-271388987/1250000000 : ℝ)|^2115 ≤ (13329619701079/100000000000000 : ℝ)^1603
        have hw : |(-271388987/1250000000 : ℝ)|=(271388987/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s6_3 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2173673803/5000000000 : ℝ)*x 0 + (844645013/2000000000 : ℝ)*x 1 + (447499389/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173673803/5000000000 : ℝ)^2115 ≤ (6663506400593/20000000000000 : ℝ)^1603 := by
    have hnat : (2173673803 : ℕ)^2115*20000000000000^1603 ≤ 6663506400593^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173673803 5000000000 6663506400593 20000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (844645013/2000000000 : ℝ)^2115 ≤ (4008524895263/12500000000000 : ℝ)^1603 := by
    have hnat : (844645013 : ℕ)^2115*12500000000000^1603 ≤ 4008524895263^1603*2000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844645013 2000000000 4008524895263 12500000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (447499389/1000000000 : ℝ)^2115 ≤ (4326783601233/12500000000000 : ℝ)^1603 := by
    have hnat : (447499389 : ℕ)^2115*12500000000000^1603 ≤ 4326783601233^1603*1000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447499389 1000000000 4326783601233 12500000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2173673803/5000000000 : ℝ), (844645013/2000000000 : ℝ), (447499389/1000000000 : ℝ)] ![(6663506400593/20000000000000 : ℝ), (4008524895263/12500000000000 : ℝ), (4326783601233/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2173673803/5000000000 : ℝ)|^2115 ≤ (6663506400593/20000000000000 : ℝ)^1603
        have hw : |(2173673803/5000000000 : ℝ)|=(2173673803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(844645013/2000000000 : ℝ)|^2115 ≤ (4008524895263/12500000000000 : ℝ)^1603
        have hw : |(844645013/2000000000 : ℝ)|=(844645013/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(447499389/1000000000 : ℝ)|^2115 ≤ (4326783601233/12500000000000 : ℝ)^1603
        have hw : |(447499389/1000000000 : ℝ)|=(447499389/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s6_4 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-421698941/2000000000 : ℝ)*x 0 + (5267695507/10000000000 : ℝ)*x 1 + (336911507/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (421698941/2000000000 : ℝ)^2115 ≤ (801546263901/6250000000000 : ℝ)^1603 := by
    have hnat : (421698941 : ℕ)^2115*6250000000000^1603 ≤ 801546263901^1603*2000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421698941 2000000000 801546263901 6250000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267695507/10000000000 : ℝ)^2115 ≤ (42924573663249/100000000000000 : ℝ)^1603 := by
    have hnat : (5267695507 : ℕ)^2115*100000000000000^1603 ≤ 42924573663249^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267695507 10000000000 42924573663249 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (336911507/625000000 : ℝ)^2115 ≤ (44250686097089/100000000000000 : ℝ)^1603 := by
    have hnat : (336911507 : ℕ)^2115*100000000000000^1603 ≤ 44250686097089^1603*625000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336911507 625000000 44250686097089 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-421698941/2000000000 : ℝ), (5267695507/10000000000 : ℝ), (336911507/625000000 : ℝ)] ![(801546263901/6250000000000 : ℝ), (42924573663249/100000000000000 : ℝ), (44250686097089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-421698941/2000000000 : ℝ)|^2115 ≤ (801546263901/6250000000000 : ℝ)^1603
        have hw : |(-421698941/2000000000 : ℝ)|=(421698941/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267695507/10000000000 : ℝ)|^2115 ≤ (42924573663249/100000000000000 : ℝ)^1603
        have hw : |(5267695507/10000000000 : ℝ)|=(5267695507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(336911507/625000000 : ℝ)|^2115 ≤ (44250686097089/100000000000000 : ℝ)^1603
        have hw : |(336911507/625000000 : ℝ)|=(336911507/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s6_5 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312647381/10000000000 : ℝ)*x 0 + (-204791069/1000000000 : ℝ)*x 1 + (2695292057/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312647381/10000000000 : ℝ)^2115 ≤ (4340852343987/10000000000000 : ℝ)^1603 := by
    have hnat : (5312647381 : ℕ)^2115*10000000000000^1603 ≤ 4340852343987^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312647381 10000000000 4340852343987 10000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (204791069/1000000000 : ℝ)^2115 ≤ (6170395214989/50000000000000 : ℝ)^1603 := by
    have hnat : (204791069 : ℕ)^2115*50000000000000^1603 ≤ 6170395214989^1603*1000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204791069 1000000000 6170395214989 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695292057/5000000000 : ℝ)^2115 ≤ (44250686118751/100000000000000 : ℝ)^1603 := by
    have hnat : (2695292057 : ℕ)^2115*100000000000000^1603 ≤ 44250686118751^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695292057 5000000000 44250686118751 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312647381/10000000000 : ℝ), (-204791069/1000000000 : ℝ), (2695292057/5000000000 : ℝ)] ![(4340852343987/10000000000000 : ℝ), (6170395214989/50000000000000 : ℝ), (44250686118751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312647381/10000000000 : ℝ)|^2115 ≤ (4340852343987/10000000000000 : ℝ)^1603
        have hw : |(5312647381/10000000000 : ℝ)|=(5312647381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-204791069/1000000000 : ℝ)|^2115 ≤ (6170395214989/50000000000000 : ℝ)^1603
        have hw : |(-204791069/1000000000 : ℝ)|=(204791069/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695292057/5000000000 : ℝ)|^2115 ≤ (44250686118751/100000000000000 : ℝ)^1603
        have hw : |(2695292057/5000000000 : ℝ)|=(2695292057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s6_6 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (265632369/500000000 : ℝ)*x 0 + (2695292057/5000000000 : ℝ)*x 1 + (-2047910691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265632369/500000000 : ℝ)^2115 ≤ (43408523429089/100000000000000 : ℝ)^1603 := by
    have hnat : (265632369 : ℕ)^2115*100000000000000^1603 ≤ 43408523429089^1603*500000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265632369 500000000 43408523429089 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695292057/5000000000 : ℝ)^2115 ≤ (44250686118751/100000000000000 : ℝ)^1603 := by
    have hnat : (2695292057 : ℕ)^2115*100000000000000^1603 ≤ 44250686118751^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695292057 5000000000 44250686118751 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2047910691/10000000000 : ℝ)^2115 ≤ (12340790437929/100000000000000 : ℝ)^1603 := by
    have hnat : (2047910691 : ℕ)^2115*100000000000000^1603 ≤ 12340790437929^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2047910691 10000000000 12340790437929 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265632369/500000000 : ℝ), (2695292057/5000000000 : ℝ), (-2047910691/10000000000 : ℝ)] ![(43408523429089/100000000000000 : ℝ), (44250686118751/100000000000000 : ℝ), (12340790437929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265632369/500000000 : ℝ)|^2115 ≤ (43408523429089/100000000000000 : ℝ)^1603
        have hw : |(265632369/500000000 : ℝ)|=(265632369/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695292057/5000000000 : ℝ)|^2115 ≤ (44250686118751/100000000000000 : ℝ)^1603
        have hw : |(2695292057/5000000000 : ℝ)|=(2695292057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2047910691/10000000000 : ℝ)|^2115 ≤ (12340790437929/100000000000000 : ℝ)^1603
        have hw : |(-2047910691/10000000000 : ℝ)|=(2047910691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s6_7 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (33963727/78125000 : ℝ)*x 0 + (2237178351/5000000000 : ℝ)*x 1 + (211193229/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33963727/78125000 : ℝ)^2115 ≤ (33317627558811/100000000000000 : ℝ)^1603 := by
    have hnat : (33963727 : ℕ)^2115*100000000000000^1603 ≤ 33317627558811^1603*78125000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33963727 78125000 33317627558811 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2237178351/5000000000 : ℝ)^2115 ≤ (4325970757073/12500000000000 : ℝ)^1603 := by
    have hnat : (2237178351 : ℕ)^2115*12500000000000^1603 ≤ 4325970757073^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237178351 5000000000 4325970757073 12500000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (211193229/500000000 : ℝ)^2115 ≤ (4009325795543/12500000000000 : ℝ)^1603 := by
    have hnat : (211193229 : ℕ)^2115*12500000000000^1603 ≤ 4009325795543^1603*500000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211193229 500000000 4009325795543 12500000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33963727/78125000 : ℝ), (2237178351/5000000000 : ℝ), (211193229/500000000 : ℝ)] ![(33317627558811/100000000000000 : ℝ), (4325970757073/12500000000000 : ℝ), (4009325795543/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33963727/78125000 : ℝ)|^2115 ≤ (33317627558811/100000000000000 : ℝ)^1603
        have hw : |(33963727/78125000 : ℝ)|=(33963727/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2237178351/5000000000 : ℝ)|^2115 ≤ (4325970757073/12500000000000 : ℝ)^1603
        have hw : |(2237178351/5000000000 : ℝ)|=(2237178351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(211193229/500000000 : ℝ)|^2115 ≤ (4009325795543/12500000000000 : ℝ)^1603
        have hw : |(211193229/500000000 : ℝ)|=(211193229/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1267_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4747449/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14141/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5743/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2301/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14121/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14141/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5743/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14141/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5743/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14141/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5743/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14141/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5743/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14141/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5743/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14141/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5743/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5743/50000 : ℝ) ^ (8459/2048 : ℝ) ≤ (6563242216438907/50000000000000000000 : ℝ) := by
    have hpowers : (5743/50000 : ℝ)^8459 ≤ (6563242216438907/50000000000000000000 : ℝ)^2048 := by
      have hnat : (5743 : ℕ)^8459*50000000000000000000^2048 ≤ 6563242216438907^2048*50000^8459 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5743 50000 6563242216438907 50000000000000000000 8459 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5743/50000 : ℝ)) (X := (6563242216438907/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14141/100000 : ℝ) ^ (8459/2048 : ℝ) ≤ (30986152465015009/100000000000000000000 : ℝ) := by
    have hpowers : (14141/100000 : ℝ)^8459 ≤ (30986152465015009/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14141 : ℕ)^8459*100000000000000000000^2048 ≤ 30986152465015009^2048*100000^8459 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14141 100000 30986152465015009 100000000000000000000 8459 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14141/100000 : ℝ)) (X := (30986152465015009/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006563242216438907/25000000000000000000 : ℝ) ≤ (10000635544770909/10000000000000000 : ℝ) ^ (8459/2048 : ℝ) := by
    have hpowers : (25006563242216438907/25000000000000000000 : ℝ)^2048 ≤ (10000635544770909/10000000000000000 : ℝ)^8459 := by
      have hnat : (25006563242216438907 : ℕ)^2048*10000000000000000^8459 ≤ 10000635544770909^8459*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006563242216438907 25000000000000000000 10000635544770909 10000000000000000 2048 8459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000635544770909/10000000000000000 : ℝ)) (X := (25006563242216438907/25000000000000000000 : ℝ)) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044112636897892823/100000000000000000000 : ℝ) ≤ (2500266957034901/2500000000000000 : ℝ) ^ (8459/2048 : ℝ) := by
    have hpowers : (100044112636897892823/100000000000000000000 : ℝ)^2048 ≤ (2500266957034901/2500000000000000 : ℝ)^8459 := by
      have hnat : (100044112636897892823 : ℕ)^2048*2500000000000000^8459 ≤ 2500266957034901^8459*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044112636897892823 100000000000000000000 2500266957034901 2500000000000000 2048 8459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500266957034901/2500000000000000 : ℝ)) (X := (100044112636897892823/100000000000000000000 : ℝ)) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030986152465015009/50000000000000000000 : ℝ) ≤ (10001500111508299/10000000000000000 : ℝ) ^ (8459/2048 : ℝ) := by
    have hpowers : (50030986152465015009/50000000000000000000 : ℝ)^2048 ≤ (10001500111508299/10000000000000000 : ℝ)^8459 := by
      have hnat : (50030986152465015009 : ℕ)^2048*10000000000000000^8459 ≤ 10001500111508299^8459*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030986152465015009 50000000000000000000 10001500111508299 10000000000000000 2048 8459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001500111508299/10000000000000000 : ℝ)) (X := (50030986152465015009/50000000000000000000 : ℝ)) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6563242216438907/50000000000000000000 : ℝ) ≤ ((5308351391564220371/5310000000000000000 : ℝ)+2*(86456673739/53100000000000 : ℝ)*(5743/50000 : ℝ))^(8459/2048 : ℝ) := by
    rw [show (5308351391564220371/5310000000000000000 : ℝ)+2*(86456673739/53100000000000 : ℝ)*(5743/50000 : ℝ)=(10000635544770909/10000000000000000 : ℝ) by norm_num, show 1+2*(6563242216438907/50000000000000000000 : ℝ)=(25006563242216438907/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30986152465015009/100000000000000000000 : ℝ)+(6563242216438907/50000000000000000000 : ℝ) ≤ ((5308351391564220371/5310000000000000000 : ℝ)+(86456673739/53100000000000 : ℝ)*((14141/100000 : ℝ)+(5743/50000 : ℝ)))^(8459/2048 : ℝ) := by
    rw [show (5308351391564220371/5310000000000000000 : ℝ)+(86456673739/53100000000000 : ℝ)*((14141/100000 : ℝ)+(5743/50000 : ℝ))=(2500266957034901/2500000000000000 : ℝ) by norm_num, show 1+(30986152465015009/100000000000000000000 : ℝ)+(6563242216438907/50000000000000000000 : ℝ)=(100044112636897892823/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30986152465015009/100000000000000000000 : ℝ) ≤ ((5308351391564220371/5310000000000000000 : ℝ)+2*(86456673739/53100000000000 : ℝ)*(14141/100000 : ℝ))^(8459/2048 : ℝ) := by
    rw [show (5308351391564220371/5310000000000000000 : ℝ)+2*(86456673739/53100000000000 : ℝ)*(14141/100000 : ℝ)=(10001500111508299/10000000000000000 : ℝ) by norm_num, show 1+2*(30986152465015009/100000000000000000000 : ℝ)=(50030986152465015009/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5308351391564220371/5310000000000000000 : ℝ)*(X 1 0+X 2 0)+(86456673739/53100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8459/2048 : ℝ)) (lo := (5743/50000 : ℝ)) (hi := (14141/100000 : ℝ)) (c := (5308351391564220371/5310000000000000000 : ℝ)) (alpha := (86456673739/53100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5308351391564220371/5310000000000000000 : ℝ)*(X 0 1+X 2 1)+(86456673739/53100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8459/2048 : ℝ)) (lo := (5743/50000 : ℝ)) (hi := (14141/100000 : ℝ)) (c := (5308351391564220371/5310000000000000000 : ℝ)) (alpha := (86456673739/53100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5308351391564220371/5310000000000000000 : ℝ)*(X 0 2+X 1 2)+(86456673739/53100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8459/2048 : ℝ)) (lo := (5743/50000 : ℝ)) (hi := (14141/100000 : ℝ)) (c := (5308351391564220371/5310000000000000000 : ℝ)) (alpha := (86456673739/53100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2108490067/10000000000 : ℝ)*X 0 0+(1078179569/2000000000 : ℝ)*X 0 1+(5267382911/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344215483/10000000000 : ℝ)*X 1 0+(-2171111903/10000000000 : ℝ)*X 1 1+(2633691453/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((83503367/156250000 : ℝ)*X 2 0+(1053476581/2000000000 : ℝ)*X 2 1+(-271388987/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2173673803/5000000000 : ℝ)*X 0 0+(844645013/2000000000 : ℝ)*X 0 1+(447499389/1000000000 : ℝ)*X 0 2+(2173673803/5000000000 : ℝ)*X 1 0+(844645013/2000000000 : ℝ)*X 1 1+(447499389/1000000000 : ℝ)*X 1 2+(2173673803/5000000000 : ℝ)*X 2 0+(844645013/2000000000 : ℝ)*X 2 1+(447499389/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-421698941/2000000000 : ℝ)*X 0 0+(5267695507/10000000000 : ℝ)*X 0 1+(336911507/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312647381/10000000000 : ℝ)*X 1 0+(-204791069/1000000000 : ℝ)*X 1 1+(2695292057/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((265632369/500000000 : ℝ)*X 2 0+(2695292057/5000000000 : ℝ)*X 2 1+(-2047910691/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((33963727/78125000 : ℝ)*X 0 0+(2237178351/5000000000 : ℝ)*X 0 1+(211193229/500000000 : ℝ)*X 0 2+(33963727/78125000 : ℝ)*X 1 0+(2237178351/5000000000 : ℝ)*X 1 1+(211193229/500000000 : ℝ)*X 1 2+(33963727/78125000 : ℝ)*X 2 0+(2237178351/5000000000 : ℝ)*X 2 1+(211193229/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (117440221438646196500339641/44250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (65561829/12500000000000 : ℝ)*(base19) + (494046489/100000000000000 : ℝ)*(base23) + (20320253/100000000000000 : ℝ)*(lower2) + (65440247/100000000000000 : ℝ)*(upper3) + (6166721/12500000000000 : ℝ)*(upper5) + (3017032056302543/50000000000000 : ℝ)*(major0) + (3017032056302543/50000000000000 : ℝ)*(major1) + (3017032056302543/50000000000000 : ℝ)*(major2) + (8096201481861941/100000000000000 : ℝ)*(sp0) + (1619243092985297/20000000000000 : ℝ)*(sp1) + (2024053873843657/25000000000000 : ℝ)*(sp2) + (496488071206801/12500000000000 : ℝ)*(sp3) + (1813444897/12500000000000 : ℝ)*(sp4) + (303106697/4000000000000 : ℝ)*(sp7) + (1985956073660917/50000000000000 : ℝ)*(f.failure) + (8096215989421117/100000000000000 : ℝ)*(f.sum) + (10587681228701/2655000000000000000000000000 : ℝ)*base66 + (184093996316301151/88500000000000000000000000000000 : ℝ)*base67 + (2266351437080301151/88500000000000000000000000000000 : ℝ)*base69 + (349013121860301151/88500000000000000000000000000000 : ℝ)*base71 + (11718372972229/2655000000000000000000000000 : ℝ)*base73 + (2522509072020801151/88500000000000000000000000000000 : ℝ)*base75 + (1700755819863801151/88500000000000000000000000000000 : ℝ)*base77 + (288373992090801151/88500000000000000000000000000000 : ℝ)*base79 + (5015187186047/1327500000000000000000000000 : ℝ)*base81 + (124267/156250000000000000000 : ℝ)*base90 + (124267/156250000000000000000 : ℝ)*base92 + (124267/156250000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (43687577832639002881282023/14750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (537134297/100000000000000 : ℝ)*(base19) + (581084709/100000000000000 : ℝ)*(base23) + (61149379/100000000000000 : ℝ)*(upper3) + (20916017/100000000000000 : ℝ)*(lower4) + (61963137/100000000000000 : ℝ)*(upper5) + (3032397960000361/50000000000000 : ℝ)*(major0) + (3032397960000361/50000000000000 : ℝ)*(major1) + (3032397960000361/50000000000000 : ℝ)*(major2) + (15264918999/100000000000000 : ℝ)*(sp1) + (8146748133/50000000000000 : ℝ)*(sp2) + (8137450435488593/100000000000000 : ℝ)*(sp4) + (4068717316717649/50000000000000 : ℝ)*(sp5) + (4068716780453809/50000000000000 : ℝ)*(sp6) + (798428261156771/20000000000000 : ℝ)*(sp7) + (798428261156771/20000000000000 : ℝ)*(f.failure) + (8137450435488593/100000000000000 : ℝ)*(f.sum) + (6826178125733/2655000000000000000000000000 : ℝ)*base65 + (1096202462575317977/88500000000000000000000000000000 : ℝ)*base67 + (307376080307817977/88500000000000000000000000000000 : ℝ)*base69 + (480255819526317977/88500000000000000000000000000000 : ℝ)*base71 + (21405753055643/2655000000000000000000000000 : ℝ)*base73 + (1203305879217182023/88500000000000000000000000000000 : ℝ)*base76 + (173356175045817977/88500000000000000000000000000000 : ℝ)*base77 + (366371682918182023/88500000000000000000000000000000 : ℝ)*base80 + (1743780434507/663750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (77179/62500000000000000000 : ℝ)*base89 + (77179/62500000000000000000 : ℝ)*base91 + (77179/62500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1267_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4747449/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14141/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5743/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2301/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14121/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1267_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1267_s7_0 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1054252997/5000000000 : ℝ)*x 0 + (2695359119/5000000000 : ℝ)*x 1 + (2633775981/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054252997/5000000000 : ℝ)^2115 ≤ (320620770459/2500000000000 : ℝ)^1603 := by
    have hnat : (1054252997 : ℕ)^2115*2500000000000^1603 ≤ 320620770459^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054252997 5000000000 320620770459 2500000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695359119/5000000000 : ℝ)^2115 ≤ (22126069398199/50000000000000 : ℝ)^1603 := by
    have hnat : (2695359119 : ℕ)^2115*50000000000000^1603 ≤ 22126069398199^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695359119 5000000000 22126069398199 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633775981/5000000000 : ℝ)^2115 ≤ (10730757592589/25000000000000 : ℝ)^1603 := by
    have hnat : (2633775981 : ℕ)^2115*25000000000000^1603 ≤ 10730757592589^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633775981 5000000000 10730757592589 25000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1054252997/5000000000 : ℝ), (2695359119/5000000000 : ℝ), (2633775981/5000000000 : ℝ)] ![(320620770459/2500000000000 : ℝ), (22126069398199/50000000000000 : ℝ), (10730757592589/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1054252997/5000000000 : ℝ)|^2115 ≤ (320620770459/2500000000000 : ℝ)^1603
        have hw : |(-1054252997/5000000000 : ℝ)|=(1054252997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695359119/5000000000 : ℝ)|^2115 ≤ (22126069398199/50000000000000 : ℝ)^1603
        have hw : |(2695359119/5000000000 : ℝ)|=(2695359119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633775981/5000000000 : ℝ)|^2115 ≤ (10730757592589/25000000000000 : ℝ)^1603
        have hw : |(2633775981/5000000000 : ℝ)|=(2633775981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s7_1 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672085019/5000000000 : ℝ)*x 0 + (-108547391/500000000 : ℝ)*x 1 + (5267552187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672085019/5000000000 : ℝ)^2115 ≤ (21874338285111/50000000000000 : ℝ)^1603 := by
    have hnat : (2672085019 : ℕ)^2115*50000000000000^1603 ≤ 21874338285111^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672085019 5000000000 21874338285111 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108547391/500000000 : ℝ)^2115 ≤ (6664145308861/50000000000000 : ℝ)^1603 := by
    have hnat : (108547391 : ℕ)^2115*50000000000000^1603 ≤ 6664145308861^1603*500000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108547391 500000000 6664145308861 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267552187/10000000000 : ℝ)^2115 ≤ (8584606557877/20000000000000 : ℝ)^1603 := by
    have hnat : (5267552187 : ℕ)^2115*20000000000000^1603 ≤ 8584606557877^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267552187 10000000000 8584606557877 20000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672085019/5000000000 : ℝ), (-108547391/500000000 : ℝ), (5267552187/10000000000 : ℝ)] ![(21874338285111/50000000000000 : ℝ), (6664145308861/50000000000000 : ℝ), (8584606557877/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672085019/5000000000 : ℝ)|^2115 ≤ (21874338285111/50000000000000 : ℝ)^1603
        have hw : |(2672085019/5000000000 : ℝ)|=(2672085019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-108547391/500000000 : ℝ)|^2115 ≤ (6664145308861/50000000000000 : ℝ)^1603
        have hw : |(-108547391/500000000 : ℝ)|=(108547391/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267552187/10000000000 : ℝ)|^2115 ≤ (8584606557877/20000000000000 : ℝ)^1603
        have hw : |(5267552187/10000000000 : ℝ)|=(5267552187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s7_2 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (668021191/1250000000 : ℝ)*x 0 + (5267552727/10000000000 : ℝ)*x 1 + (-271368473/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668021191/1250000000 : ℝ)^2115 ≤ (2734291941359/6250000000000 : ℝ)^1603 := by
    have hnat : (668021191 : ℕ)^2115*6250000000000^1603 ≤ 2734291941359^1603*1250000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668021191 1250000000 2734291941359 6250000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267552727/10000000000 : ℝ)^2115 ≤ (10730759648763/25000000000000 : ℝ)^1603 := by
    have hnat : (5267552727 : ℕ)^2115*25000000000000^1603 ≤ 10730759648763^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267552727 10000000000 10730759648763 25000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271368473/1250000000 : ℝ)^2115 ≤ (13328290326111/100000000000000 : ℝ)^1603 := by
    have hnat : (271368473 : ℕ)^2115*100000000000000^1603 ≤ 13328290326111^1603*1250000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271368473 1250000000 13328290326111 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668021191/1250000000 : ℝ), (5267552727/10000000000 : ℝ), (-271368473/1250000000 : ℝ)] ![(2734291941359/6250000000000 : ℝ), (10730759648763/25000000000000 : ℝ), (13328290326111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668021191/1250000000 : ℝ)|^2115 ≤ (2734291941359/6250000000000 : ℝ)^1603
        have hw : |(668021191/1250000000 : ℝ)|=(668021191/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267552727/10000000000 : ℝ)|^2115 ≤ (10730759648763/25000000000000 : ℝ)^1603
        have hw : |(5267552727/10000000000 : ℝ)|=(5267552727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-271368473/1250000000 : ℝ)|^2115 ≤ (13328290326111/100000000000000 : ℝ)^1603
        have hw : |(-271368473/1250000000 : ℝ)|=(271368473/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s7_3 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (34778857/80000000 : ℝ)*x 0 + (422357999/1000000000 : ℝ)*x 1 + (447463603/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34778857/80000000 : ℝ)^2115 ≤ (33317628256521/100000000000000 : ℝ)^1603 := by
    have hnat : (34778857 : ℕ)^2115*100000000000000^1603 ≤ 33317628256521^1603*80000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34778857 80000000 33317628256521 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (422357999/1000000000 : ℝ)^2115 ≤ (16035877531361/50000000000000 : ℝ)^1603 := by
    have hnat : (422357999 : ℕ)^2115*50000000000000^1603 ≤ 16035877531361^1603*1000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422357999 1000000000 16035877531361 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (447463603/1000000000 : ℝ)^2115 ≤ (4326327083987/12500000000000 : ℝ)^1603 := by
    have hnat : (447463603 : ℕ)^2115*12500000000000^1603 ≤ 4326327083987^1603*1000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447463603 1000000000 4326327083987 12500000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34778857/80000000 : ℝ), (422357999/1000000000 : ℝ), (447463603/1000000000 : ℝ)] ![(33317628256521/100000000000000 : ℝ), (16035877531361/50000000000000 : ℝ), (4326327083987/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34778857/80000000 : ℝ)|^2115 ≤ (33317628256521/100000000000000 : ℝ)^1603
        have hw : |(34778857/80000000 : ℝ)|=(34778857/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(422357999/1000000000 : ℝ)|^2115 ≤ (16035877531361/50000000000000 : ℝ)^1603
        have hw : |(422357999/1000000000 : ℝ)|=(422357999/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(447463603/1000000000 : ℝ)|^2115 ≤ (4326327083987/12500000000000 : ℝ)^1603
        have hw : |(447463603/1000000000 : ℝ)|=(447463603/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s7_4 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2108509409/10000000000 : ℝ)*x 0 + (2633932029/5000000000 : ℝ)*x 1 + (5390405901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2108509409/10000000000 : ℝ)^2115 ≤ (2564971644857/20000000000000 : ℝ)^1603 := by
    have hnat : (2108509409 : ℕ)^2115*20000000000000^1603 ≤ 2564971644857^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108509409 10000000000 2564971644857 20000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633932029/5000000000 : ℝ)^2115 ≤ (42926385819867/100000000000000 : ℝ)^1603 := by
    have hnat : (2633932029 : ℕ)^2115*100000000000000^1603 ≤ 42926385819867^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633932029 5000000000 42926385819867 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390405901/10000000000 : ℝ)^2115 ≤ (22124377968691/50000000000000 : ℝ)^1603 := by
    have hnat : (5390405901 : ℕ)^2115*50000000000000^1603 ≤ 22124377968691^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390405901 10000000000 22124377968691 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2108509409/10000000000 : ℝ), (2633932029/5000000000 : ℝ), (5390405901/10000000000 : ℝ)] ![(2564971644857/20000000000000 : ℝ), (42926385819867/100000000000000 : ℝ), (22124377968691/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2108509409/10000000000 : ℝ)|^2115 ≤ (2564971644857/20000000000000 : ℝ)^1603
        have hw : |(-2108509409/10000000000 : ℝ)|=(2108509409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633932029/5000000000 : ℝ)|^2115 ≤ (42926385819867/100000000000000 : ℝ)^1603
        have hw : |(2633932029/5000000000 : ℝ)|=(2633932029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390405901/10000000000 : ℝ)|^2115 ≤ (22124377968691/50000000000000 : ℝ)^1603
        have hw : |(5390405901/10000000000 : ℝ)|=(5390405901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s7_5 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (332043219/625000000 : ℝ)*x 0 + (-512023347/2500000000 : ℝ)*x 1 + (1347601519/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332043219/625000000 : ℝ)^2115 ≤ (43408999110657/100000000000000 : ℝ)^1603 := by
    have hnat : (332043219 : ℕ)^2115*100000000000000^1603 ≤ 43408999110657^1603*625000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332043219 625000000 43408999110657 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (512023347/2500000000 : ℝ)^2115 ≤ (12342243039191/100000000000000 : ℝ)^1603 := by
    have hnat : (512023347 : ℕ)^2115*100000000000000^1603 ≤ 12342243039191^1603*2500000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512023347 2500000000 12342243039191 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347601519/2500000000 : ℝ)^2115 ≤ (22124378916377/50000000000000 : ℝ)^1603 := by
    have hnat : (1347601519 : ℕ)^2115*50000000000000^1603 ≤ 22124378916377^1603*2500000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347601519 2500000000 22124378916377 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(332043219/625000000 : ℝ), (-512023347/2500000000 : ℝ), (1347601519/2500000000 : ℝ)] ![(43408999110657/100000000000000 : ℝ), (12342243039191/100000000000000 : ℝ), (22124378916377/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(332043219/625000000 : ℝ)|^2115 ≤ (43408999110657/100000000000000 : ℝ)^1603
        have hw : |(332043219/625000000 : ℝ)|=(332043219/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-512023347/2500000000 : ℝ)|^2115 ≤ (12342243039191/100000000000000 : ℝ)^1603
        have hw : |(-512023347/2500000000 : ℝ)|=(512023347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347601519/2500000000 : ℝ)|^2115 ≤ (22124378916377/50000000000000 : ℝ)^1603
        have hw : |(1347601519/2500000000 : ℝ)|=(1347601519/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s7_6 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312690819/10000000000 : ℝ)*x 0 + (5390406379/10000000000 : ℝ)*x 1 + (-128005869/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312690819/10000000000 : ℝ)^2115 ≤ (21704495862981/50000000000000 : ℝ)^1603 := by
    have hnat : (5312690819 : ℕ)^2115*50000000000000^1603 ≤ 21704495862981^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312690819 10000000000 21704495862981 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390406379/10000000000 : ℝ)^2115 ≤ (5531095139307/12500000000000 : ℝ)^1603 := by
    have hnat : (5390406379 : ℕ)^2115*12500000000000^1603 ≤ 5531095139307^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390406379 10000000000 5531095139307 12500000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (128005869/625000000 : ℝ)^2115 ≤ (12342247141901/100000000000000 : ℝ)^1603 := by
    have hnat : (128005869 : ℕ)^2115*100000000000000^1603 ≤ 12342247141901^1603*625000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128005869 625000000 12342247141901 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312690819/10000000000 : ℝ), (5390406379/10000000000 : ℝ), (-128005869/625000000 : ℝ)] ![(21704495862981/50000000000000 : ℝ), (5531095139307/12500000000000 : ℝ), (12342247141901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312690819/10000000000 : ℝ)|^2115 ≤ (21704495862981/50000000000000 : ℝ)^1603
        have hw : |(5312690819/10000000000 : ℝ)|=(5312690819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390406379/10000000000 : ℝ)|^2115 ≤ (5531095139307/12500000000000 : ℝ)^1603
        have hw : |(5390406379/10000000000 : ℝ)|=(5390406379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-128005869/625000000 : ℝ)|^2115 ≤ (12342247141901/100000000000000 : ℝ)^1603
        have hw : |(-128005869/625000000 : ℝ)|=(128005869/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s7_7 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4347365573/10000000000 : ℝ)*x 0 + (2237001147/5000000000 : ℝ)*x 1 + (844843393/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4347365573/10000000000 : ℝ)^2115 ≤ (33317713680471/100000000000000 : ℝ)^1603 := by
    have hnat : (4347365573 : ℕ)^2115*100000000000000^1603 ≤ 33317713680471^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4347365573 10000000000 33317713680471 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2237001147/5000000000 : ℝ)^2115 ≤ (17302074656021/50000000000000 : ℝ)^1603 := by
    have hnat : (2237001147 : ℕ)^2115*50000000000000^1603 ≤ 17302074656021^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237001147 5000000000 17302074656021 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (844843393/2000000000 : ℝ)^2115 ≤ (4009767123471/12500000000000 : ℝ)^1603 := by
    have hnat : (844843393 : ℕ)^2115*12500000000000^1603 ≤ 4009767123471^1603*2000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844843393 2000000000 4009767123471 12500000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4347365573/10000000000 : ℝ), (2237001147/5000000000 : ℝ), (844843393/2000000000 : ℝ)] ![(33317713680471/100000000000000 : ℝ), (17302074656021/50000000000000 : ℝ), (4009767123471/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4347365573/10000000000 : ℝ)|^2115 ≤ (33317713680471/100000000000000 : ℝ)^1603
        have hw : |(4347365573/10000000000 : ℝ)|=(4347365573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2237001147/5000000000 : ℝ)|^2115 ≤ (17302074656021/50000000000000 : ℝ)^1603
        have hw : |(2237001147/5000000000 : ℝ)|=(2237001147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(844843393/2000000000 : ℝ)|^2115 ≤ (4009767123471/12500000000000 : ℝ)^1603
        have hw : |(844843393/2000000000 : ℝ)|=(844843393/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1267_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4747449/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14121/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2301/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2877/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7059/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14121/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2301/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14121/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2301/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14121/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2301/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14121/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2301/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14121/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2301/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14121/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2301/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2301/20000 : ℝ) ^ (8459/2048 : ℝ) ≤ (1652050302877199/12500000000000000000 : ℝ) := by
    have hpowers : (2301/20000 : ℝ)^8459 ≤ (1652050302877199/12500000000000000000 : ℝ)^2048 := by
      have hnat : (2301 : ℕ)^8459*12500000000000000000^2048 ≤ 1652050302877199^2048*20000^8459 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2301 20000 1652050302877199 12500000000000000000 8459 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2301/20000 : ℝ)) (X := (1652050302877199/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14121/100000 : ℝ) ^ (8459/2048 : ℝ) ≤ (1232221643412581/4000000000000000000 : ℝ) := by
    have hpowers : (14121/100000 : ℝ)^8459 ≤ (1232221643412581/4000000000000000000 : ℝ)^2048 := by
      have hnat : (14121 : ℕ)^8459*4000000000000000000^2048 ≤ 1232221643412581^2048*100000^8459 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14121 100000 1232221643412581 4000000000000000000 8459 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14121/100000 : ℝ)) (X := (1232221643412581/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251652050302877199/6250000000000000000 : ℝ) ≤ (10000639897892703/10000000000000000 : ℝ) ^ (8459/2048 : ℝ) := by
    have hpowers : (6251652050302877199/6250000000000000000 : ℝ)^2048 ≤ (10000639897892703/10000000000000000 : ℝ)^8459 := by
      have hnat : (6251652050302877199 : ℕ)^2048*10000000000000000^8459 ≤ 10000639897892703^8459*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251652050302877199 6250000000000000000 10000639897892703 10000000000000000 2048 8459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000639897892703/10000000000000000 : ℝ)) (X := (6251652050302877199/6250000000000000000 : ℝ)) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044021943508332117/100000000000000000000 : ℝ) ≤ (2500266408276029/2500000000000000 : ℝ) ^ (8459/2048 : ℝ) := by
    have hpowers : (100044021943508332117/100000000000000000000 : ℝ)^2048 ≤ (2500266408276029/2500000000000000 : ℝ)^8459 := by
      have hnat : (100044021943508332117 : ℕ)^2048*2500000000000000^8459 ≤ 2500266408276029^8459*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044021943508332117 100000000000000000000 2500266408276029 2500000000000000 2048 8459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500266408276029/2500000000000000 : ℝ)) (X := (100044021943508332117/100000000000000000000 : ℝ)) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001232221643412581/2000000000000000000 : ℝ) ≤ (10001491368315529/10000000000000000 : ℝ) ^ (8459/2048 : ℝ) := by
    have hpowers : (2001232221643412581/2000000000000000000 : ℝ)^2048 ≤ (10001491368315529/10000000000000000 : ℝ)^8459 := by
      have hnat : (2001232221643412581 : ℕ)^2048*10000000000000000^8459 ≤ 10001491368315529^8459*2000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001232221643412581 2000000000000000000 10001491368315529 10000000000000000 2048 8459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001491368315529/10000000000000000 : ℝ)) (X := (2001232221643412581/2000000000000000000 : ℝ)) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1652050302877199/12500000000000000000 : ℝ) ≤ ((4358646300945449653/4360000000000000000 : ℝ)+2*(425735211413/261600000000000 : ℝ)*(2301/20000 : ℝ))^(8459/2048 : ℝ) := by
    rw [show (4358646300945449653/4360000000000000000 : ℝ)+2*(425735211413/261600000000000 : ℝ)*(2301/20000 : ℝ)=(10000639897892703/10000000000000000 : ℝ) by norm_num, show 1+2*(1652050302877199/12500000000000000000 : ℝ)=(6251652050302877199/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1232221643412581/4000000000000000000 : ℝ)+(1652050302877199/12500000000000000000 : ℝ) ≤ ((4358646300945449653/4360000000000000000 : ℝ)+(425735211413/261600000000000 : ℝ)*((14121/100000 : ℝ)+(2301/20000 : ℝ)))^(8459/2048 : ℝ) := by
    rw [show (4358646300945449653/4360000000000000000 : ℝ)+(425735211413/261600000000000 : ℝ)*((14121/100000 : ℝ)+(2301/20000 : ℝ))=(2500266408276029/2500000000000000 : ℝ) by norm_num, show 1+(1232221643412581/4000000000000000000 : ℝ)+(1652050302877199/12500000000000000000 : ℝ)=(100044021943508332117/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1232221643412581/4000000000000000000 : ℝ) ≤ ((4358646300945449653/4360000000000000000 : ℝ)+2*(425735211413/261600000000000 : ℝ)*(14121/100000 : ℝ))^(8459/2048 : ℝ) := by
    rw [show (4358646300945449653/4360000000000000000 : ℝ)+2*(425735211413/261600000000000 : ℝ)*(14121/100000 : ℝ)=(10001491368315529/10000000000000000 : ℝ) by norm_num, show 1+2*(1232221643412581/4000000000000000000 : ℝ)=(2001232221643412581/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4358646300945449653/4360000000000000000 : ℝ)*(X 1 0+X 2 0)+(425735211413/261600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8459/2048 : ℝ)) (lo := (2301/20000 : ℝ)) (hi := (14121/100000 : ℝ)) (c := (4358646300945449653/4360000000000000000 : ℝ)) (alpha := (425735211413/261600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4358646300945449653/4360000000000000000 : ℝ)*(X 0 1+X 2 1)+(425735211413/261600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8459/2048 : ℝ)) (lo := (2301/20000 : ℝ)) (hi := (14121/100000 : ℝ)) (c := (4358646300945449653/4360000000000000000 : ℝ)) (alpha := (425735211413/261600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4358646300945449653/4360000000000000000 : ℝ)*(X 0 2+X 1 2)+(425735211413/261600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8459/2048 : ℝ)) (lo := (2301/20000 : ℝ)) (hi := (14121/100000 : ℝ)) (c := (4358646300945449653/4360000000000000000 : ℝ)) (alpha := (425735211413/261600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1054252997/5000000000 : ℝ)*X 0 0+(2695359119/5000000000 : ℝ)*X 0 1+(2633775981/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672085019/5000000000 : ℝ)*X 1 0+(-108547391/500000000 : ℝ)*X 1 1+(5267552187/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668021191/1250000000 : ℝ)*X 2 0+(5267552727/10000000000 : ℝ)*X 2 1+(-271368473/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((34778857/80000000 : ℝ)*X 0 0+(422357999/1000000000 : ℝ)*X 0 1+(447463603/1000000000 : ℝ)*X 0 2+(34778857/80000000 : ℝ)*X 1 0+(422357999/1000000000 : ℝ)*X 1 1+(447463603/1000000000 : ℝ)*X 1 2+(34778857/80000000 : ℝ)*X 2 0+(422357999/1000000000 : ℝ)*X 2 1+(447463603/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2108509409/10000000000 : ℝ)*X 0 0+(2633932029/5000000000 : ℝ)*X 0 1+(5390405901/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((332043219/625000000 : ℝ)*X 1 0+(-512023347/2500000000 : ℝ)*X 1 1+(1347601519/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312690819/10000000000 : ℝ)*X 2 0+(5390406379/10000000000 : ℝ)*X 2 1+(-128005869/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4347365573/10000000000 : ℝ)*X 0 0+(2237001147/5000000000 : ℝ)*X 0 1+(844843393/2000000000 : ℝ)*X 0 2+(4347365573/10000000000 : ℝ)*X 1 0+(2237001147/5000000000 : ℝ)*X 1 1+(844843393/2000000000 : ℝ)*X 1 2+(4347365573/10000000000 : ℝ)*X 2 0+(2237001147/5000000000 : ℝ)*X 2 1+(844843393/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (107956016376317000111539437/21800000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23136557/781250000000 : ℝ)*(base19) + (128780471/6250000000000 : ℝ)*(base23) + (67420927/100000000000000 : ℝ)*(lower2) + (227319383/50000000000000 : ℝ)*(upper3) + (283978071/100000000000000 : ℝ)*(upper5) + (1210254283438843/20000000000000 : ℝ)*(major0) + (1210254283438843/20000000000000 : ℝ)*(major1) + (1210254283438843/20000000000000 : ℝ)*(major2) + (8119211901319959/100000000000000 : ℝ)*(sp0) + (8119300882370197/100000000000000 : ℝ)*(sp1) + (4059650891680979/50000000000000 : ℝ)*(sp2) + (497900807792879/12500000000000 : ℝ)*(sp3) + (179575253/195312500000 : ℝ)*(sp4) + (6472625107/20000000000000 : ℝ)*(sp7) + (3983238825468567/100000000000000 : ℝ)*(f.failure) + (4059651921924747/50000000000000 : ℝ)*(f.sum) + (773603956799/2616000000000000000000000000 : ℝ)*base65 + (4116376287038835563/261600000000000000000000000000000 : ℝ)*base68 + (2283112113665235563/261600000000000000000000000000000 : ℝ)*base70 + (835527928884435563/261600000000000000000000000000000 : ℝ)*base72 + (3268679385721/2616000000000000000000000000 : ℝ)*base74 + (1448495454317235563/261600000000000000000000000000000 : ℝ)*base76 + (706222569894764437/261600000000000000000000000000000 : ℝ)*base77 + (1902829610616435563/261600000000000000000000000000000 : ℝ)*base80 + (19821044599249/2616000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base86 + (1060583/312500000000000000000 : ℝ)*base89 + (1060583/312500000000000000000 : ℝ)*base91 + (1060583/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1201540797397876510623770621/109000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1629845099/100000000000000 : ℝ)*(base19) + (1871054737/100000000000000 : ℝ)*(base23) + (52332261/25000000000000 : ℝ)*(lower3) + (705560187/100000000000000 : ℝ)*(lower4) + (153491339/100000000000000 : ℝ)*(lower5) + (3040967785788127/50000000000000 : ℝ)*(major0) + (3040967785788127/50000000000000 : ℝ)*(major1) + (3040967785788127/50000000000000 : ℝ)*(major2) + (44908194987/50000000000000 : ℝ)*(sp1) + (83963543493/100000000000000 : ℝ)*(sp2) + (8160447324256103/100000000000000 : ℝ)*(sp4) + (8160355878021031/100000000000000 : ℝ)*(sp5) + (8160361489657873/100000000000000 : ℝ)*(sp6) + (2001711725726363/50000000000000 : ℝ)*(sp7) + (2001711725726363/50000000000000 : ℝ)*(f.failure) + (8160447324256103/100000000000000 : ℝ)*(f.sum) + (38651753477111/6540000000000000000000000000 : ℝ)*base65 + (2537824284311559793/654000000000000000000000000000000 : ℝ)*base67 + (7563970606661559793/654000000000000000000000000000000 : ℝ)*base69 + (6140434155047559793/654000000000000000000000000000000 : ℝ)*base71 + (34942756860011/6540000000000000000000000000 : ℝ)*base73 + (15215578532747559793/654000000000000000000000000000000 : ℝ)*base75 + (5205194760677559793/654000000000000000000000000000000 : ℝ)*base77 + (2733251711495559793/654000000000000000000000000000000 : ℝ)*base79 + (4928138300989/6540000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (577013/156250000000000000000 : ℝ)*base90 + (577013/156250000000000000000 : ℝ)*base92 + (577013/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1267_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4747449/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14121/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2301/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2877/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7059/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1267_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1267_s8_0 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-421701523/2000000000 : ℝ)*x 0 + (134767267/250000000 : ℝ)*x 1 + (2633789257/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (421701523/2000000000 : ℝ)^2115 ≤ (1603105478393/12500000000000 : ℝ)^1603 := by
    have hnat : (421701523 : ℕ)^2115*12500000000000^1603 ≤ 1603105478393^1603*2000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421701523 2000000000 1603105478393 12500000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134767267/250000000 : ℝ)^2115 ≤ (44251840318743/100000000000000 : ℝ)^1603 := by
    have hnat : (134767267 : ℕ)^2115*100000000000000^1603 ≤ 44251840318743^1603*250000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134767267 250000000 44251840318743 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633789257/5000000000 : ℝ)^2115 ≤ (8584663167481/20000000000000 : ℝ)^1603 := by
    have hnat : (2633789257 : ℕ)^2115*20000000000000^1603 ≤ 8584663167481^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633789257 5000000000 8584663167481 20000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-421701523/2000000000 : ℝ), (134767267/250000000 : ℝ), (2633789257/5000000000 : ℝ)] ![(1603105478393/12500000000000 : ℝ), (44251840318743/100000000000000 : ℝ), (8584663167481/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-421701523/2000000000 : ℝ)|^2115 ≤ (1603105478393/12500000000000 : ℝ)^1603
        have hw : |(-421701523/2000000000 : ℝ)|=(421701523/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(134767267/250000000 : ℝ)|^2115 ≤ (44251840318743/100000000000000 : ℝ)^1603
        have hw : |(134767267/250000000 : ℝ)|=(134767267/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633789257/5000000000 : ℝ)|^2115 ≤ (8584663167481/20000000000000 : ℝ)^1603
        have hw : |(2633789257/5000000000 : ℝ)|=(2633789257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s8_1 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672081437/5000000000 : ℝ)*x 0 + (-542730611/2500000000 : ℝ)*x 1 + (658447313/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672081437/5000000000 : ℝ)^2115 ≤ (21874299596157/50000000000000 : ℝ)^1603 := by
    have hnat : (2672081437 : ℕ)^2115*50000000000000^1603 ≤ 21874299596157^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672081437 5000000000 21874299596157 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542730611/2500000000 : ℝ)^2115 ≤ (13328085064507/100000000000000 : ℝ)^1603 := by
    have hnat : (542730611 : ℕ)^2115*100000000000000^1603 ≤ 13328085064507^1603*2500000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542730611 2500000000 13328085064507 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658447313/1250000000 : ℝ)^2115 ≤ (42923315729893/100000000000000 : ℝ)^1603 := by
    have hnat : (658447313 : ℕ)^2115*100000000000000^1603 ≤ 42923315729893^1603*1250000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658447313 1250000000 42923315729893 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672081437/5000000000 : ℝ), (-542730611/2500000000 : ℝ), (658447313/1250000000 : ℝ)] ![(21874299596157/50000000000000 : ℝ), (13328085064507/100000000000000 : ℝ), (42923315729893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672081437/5000000000 : ℝ)|^2115 ≤ (21874299596157/50000000000000 : ℝ)^1603
        have hw : |(2672081437/5000000000 : ℝ)|=(2672081437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-542730611/2500000000 : ℝ)|^2115 ≤ (13328085064507/100000000000000 : ℝ)^1603
        have hw : |(-542730611/2500000000 : ℝ)|=(542730611/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658447313/1250000000 : ℝ)|^2115 ≤ (42923315729893/100000000000000 : ℝ)^1603
        have hw : |(658447313/1250000000 : ℝ)|=(658447313/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s8_2 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672081431/5000000000 : ℝ)*x 0 + (2633789257/5000000000 : ℝ)*x 1 + (-2170922447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672081431/5000000000 : ℝ)^2115 ≤ (43748599062703/100000000000000 : ℝ)^1603 := by
    have hnat : (2672081431 : ℕ)^2115*100000000000000^1603 ≤ 43748599062703^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672081431 5000000000 43748599062703 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633789257/5000000000 : ℝ)^2115 ≤ (8584663167481/20000000000000 : ℝ)^1603 := by
    have hnat : (2633789257 : ℕ)^2115*20000000000000^1603 ≤ 8584663167481^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633789257 5000000000 8584663167481 20000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2170922447/10000000000 : ℝ)^2115 ≤ (1666010636101/12500000000000 : ℝ)^1603 := by
    have hnat : (2170922447 : ℕ)^2115*12500000000000^1603 ≤ 1666010636101^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170922447 10000000000 1666010636101 12500000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672081431/5000000000 : ℝ), (2633789257/5000000000 : ℝ), (-2170922447/10000000000 : ℝ)] ![(43748599062703/100000000000000 : ℝ), (8584663167481/20000000000000 : ℝ), (1666010636101/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672081431/5000000000 : ℝ)|^2115 ≤ (43748599062703/100000000000000 : ℝ)^1603
        have hw : |(2672081431/5000000000 : ℝ)|=(2672081431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633789257/5000000000 : ℝ)|^2115 ≤ (8584663167481/20000000000000 : ℝ)^1603
        have hw : |(2633789257/5000000000 : ℝ)|=(2633789257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2170922447/10000000000 : ℝ)|^2115 ≤ (1666010636101/12500000000000 : ℝ)^1603
        have hw : |(-2170922447/10000000000 : ℝ)|=(2170922447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s8_3 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2173678877/5000000000 : ℝ)*x 0 + (4223634279/10000000000 : ℝ)*x 1 + (4474582109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173678877/5000000000 : ℝ)^2115 ≤ (33317634616801/100000000000000 : ℝ)^1603 := by
    have hnat : (2173678877 : ℕ)^2115*100000000000000^1603 ≤ 33317634616801^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173678877 5000000000 33317634616801 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4223634279/10000000000 : ℝ)^2115 ≤ (32072298978411/100000000000000 : ℝ)^1603 := by
    have hnat : (4223634279 : ℕ)^2115*100000000000000^1603 ≤ 32072298978411^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4223634279 10000000000 32072298978411 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4474582109/10000000000 : ℝ)^2115 ≤ (17305033194779/50000000000000 : ℝ)^1603 := by
    have hnat : (4474582109 : ℕ)^2115*50000000000000^1603 ≤ 17305033194779^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4474582109 10000000000 17305033194779 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2173678877/5000000000 : ℝ), (4223634279/10000000000 : ℝ), (4474582109/10000000000 : ℝ)] ![(33317634616801/100000000000000 : ℝ), (32072298978411/100000000000000 : ℝ), (17305033194779/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2173678877/5000000000 : ℝ)|^2115 ≤ (33317634616801/100000000000000 : ℝ)^1603
        have hw : |(2173678877/5000000000 : ℝ)|=(2173678877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4223634279/10000000000 : ℝ)|^2115 ≤ (32072298978411/100000000000000 : ℝ)^1603
        have hw : |(4223634279/10000000000 : ℝ)|=(4223634279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4474582109/10000000000 : ℝ)|^2115 ≤ (17305033194779/50000000000000 : ℝ)^1603
        have hw : |(4474582109/10000000000 : ℝ)|=(4474582109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s8_4 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2108512217/10000000000 : ℝ)*x 0 + (2633944543/5000000000 : ℝ)*x 1 + (168449343/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2108512217/10000000000 : ℝ)^2115 ≤ (12824880758949/100000000000000 : ℝ)^1603 := by
    have hnat : (2108512217 : ℕ)^2115*100000000000000^1603 ≤ 12824880758949^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108512217 10000000000 12824880758949 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633944543/5000000000 : ℝ)^2115 ≤ (21463327453549/50000000000000 : ℝ)^1603 := by
    have hnat : (2633944543 : ℕ)^2115*50000000000000^1603 ≤ 21463327453549^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633944543 5000000000 21463327453549 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168449343/312500000 : ℝ)^2115 ≤ (2765529020067/6250000000000 : ℝ)^1603 := by
    have hnat : (168449343 : ℕ)^2115*6250000000000^1603 ≤ 2765529020067^1603*312500000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168449343 312500000 2765529020067 6250000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2108512217/10000000000 : ℝ), (2633944543/5000000000 : ℝ), (168449343/312500000 : ℝ)] ![(12824880758949/100000000000000 : ℝ), (21463327453549/50000000000000 : ℝ), (2765529020067/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2108512217/10000000000 : ℝ)|^2115 ≤ (12824880758949/100000000000000 : ℝ)^1603
        have hw : |(-2108512217/10000000000 : ℝ)|=(2108512217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633944543/5000000000 : ℝ)|^2115 ≤ (21463327453549/50000000000000 : ℝ)^1603
        have hw : |(2633944543/5000000000 : ℝ)|=(2633944543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(168449343/312500000 : ℝ)|^2115 ≤ (2765529020067/6250000000000 : ℝ)^1603
        have hw : |(168449343/312500000 : ℝ)|=(168449343/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s8_5 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1328174411/2500000000 : ℝ)*x 0 + (-2048121979/10000000000 : ℝ)*x 1 + (215615159/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328174411/2500000000 : ℝ)^2115 ≤ (8681813060683/20000000000000 : ℝ)^1603 := by
    have hnat : (1328174411 : ℕ)^2115*20000000000000^1603 ≤ 8681813060683^1603*2500000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328174411 2500000000 8681813060683 20000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2048121979/10000000000 : ℝ)^2115 ≤ (6171235183221/50000000000000 : ℝ)^1603 := by
    have hnat : (2048121979 : ℕ)^2115*50000000000000^1603 ≤ 6171235183221^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2048121979 10000000000 6171235183221 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215615159/400000000 : ℝ)^2115 ≤ (44248464310241/100000000000000 : ℝ)^1603 := by
    have hnat : (215615159 : ℕ)^2115*100000000000000^1603 ≤ 44248464310241^1603*400000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215615159 400000000 44248464310241 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328174411/2500000000 : ℝ), (-2048121979/10000000000 : ℝ), (215615159/400000000 : ℝ)] ![(8681813060683/20000000000000 : ℝ), (6171235183221/50000000000000 : ℝ), (44248464310241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328174411/2500000000 : ℝ)|^2115 ≤ (8681813060683/20000000000000 : ℝ)^1603
        have hw : |(1328174411/2500000000 : ℝ)|=(1328174411/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2048121979/10000000000 : ℝ)|^2115 ≤ (6171235183221/50000000000000 : ℝ)^1603
        have hw : |(-2048121979/10000000000 : ℝ)|=(2048121979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215615159/400000000 : ℝ)|^2115 ≤ (44248464310241/100000000000000 : ℝ)^1603
        have hw : |(215615159/400000000 : ℝ)|=(215615159/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s8_6 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1328174411/2500000000 : ℝ)*x 0 + (168449343/312500000 : ℝ)*x 1 + (-2048121979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328174411/2500000000 : ℝ)^2115 ≤ (8681813060683/20000000000000 : ℝ)^1603 := by
    have hnat : (1328174411 : ℕ)^2115*20000000000000^1603 ≤ 8681813060683^1603*2500000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328174411 2500000000 8681813060683 20000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168449343/312500000 : ℝ)^2115 ≤ (2765529020067/6250000000000 : ℝ)^1603 := by
    have hnat : (168449343 : ℕ)^2115*6250000000000^1603 ≤ 2765529020067^1603*312500000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168449343 312500000 2765529020067 6250000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2048121979/10000000000 : ℝ)^2115 ≤ (6171235183221/50000000000000 : ℝ)^1603 := by
    have hnat : (2048121979 : ℕ)^2115*50000000000000^1603 ≤ 6171235183221^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2048121979 10000000000 6171235183221 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328174411/2500000000 : ℝ), (168449343/312500000 : ℝ), (-2048121979/10000000000 : ℝ)] ![(8681813060683/20000000000000 : ℝ), (2765529020067/6250000000000 : ℝ), (6171235183221/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328174411/2500000000 : ℝ)|^2115 ≤ (8681813060683/20000000000000 : ℝ)^1603
        have hw : |(1328174411/2500000000 : ℝ)|=(1328174411/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168449343/312500000 : ℝ)|^2115 ≤ (2765529020067/6250000000000 : ℝ)^1603
        have hw : |(168449343/312500000 : ℝ)|=(168449343/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2048121979/10000000000 : ℝ)|^2115 ≤ (6171235183221/50000000000000 : ℝ)^1603
        have hw : |(-2048121979/10000000000 : ℝ)|=(2048121979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s8_7 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (434736713/1000000000 : ℝ)*x 0 + (4473949033/10000000000 : ℝ)*x 1 + (4224269641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (434736713/1000000000 : ℝ)^2115 ≤ (33317729424451/100000000000000 : ℝ)^1603 := by
    have hnat : (434736713 : ℕ)^2115*100000000000000^1603 ≤ 33317729424451^1603*1000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434736713 1000000000 33317729424451 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4473949033/10000000000 : ℝ)^2115 ≤ (34603605789807/100000000000000 : ℝ)^1603 := by
    have hnat : (4473949033 : ℕ)^2115*100000000000000^1603 ≤ 34603605789807^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4473949033 10000000000 34603605789807 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4224269641/10000000000 : ℝ)^2115 ≤ (3207866476837/10000000000000 : ℝ)^1603 := by
    have hnat : (4224269641 : ℕ)^2115*10000000000000^1603 ≤ 3207866476837^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224269641 10000000000 3207866476837 10000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(434736713/1000000000 : ℝ), (4473949033/10000000000 : ℝ), (4224269641/10000000000 : ℝ)] ![(33317729424451/100000000000000 : ℝ), (34603605789807/100000000000000 : ℝ), (3207866476837/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(434736713/1000000000 : ℝ)|^2115 ≤ (33317729424451/100000000000000 : ℝ)^1603
        have hw : |(434736713/1000000000 : ℝ)|=(434736713/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4473949033/10000000000 : ℝ)|^2115 ≤ (34603605789807/100000000000000 : ℝ)^1603
        have hw : |(4473949033/10000000000 : ℝ)|=(4473949033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4224269641/10000000000 : ℝ)|^2115 ≤ (3207866476837/10000000000000 : ℝ)^1603
        have hw : |(4224269641/10000000000 : ℝ)|=(4224269641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1267_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4747449/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7059/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2877/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11509/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14117/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7059/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2877/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7059/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2877/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7059/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2877/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7059/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2877/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7059/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2877/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7059/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2877/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2877/25000 : ℝ) ^ (8459/2048 : ℝ) ≤ (6615321280611933/50000000000000000000 : ℝ) := by
    have hpowers : (2877/25000 : ℝ)^8459 ≤ (6615321280611933/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2877 : ℕ)^8459*50000000000000000000^2048 ≤ 6615321280611933^2048*25000^8459 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2877 25000 6615321280611933 50000000000000000000 8459 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2877/25000 : ℝ)) (X := (6615321280611933/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7059/50000 : ℝ) ^ (8459/2048 : ℝ) ≤ (3847314793802517/12500000000000000000 : ℝ) := by
    have hpowers : (7059/50000 : ℝ)^8459 ≤ (3847314793802517/12500000000000000000 : ℝ)^2048 := by
      have hnat : (7059 : ℕ)^8459*12500000000000000000^2048 ≤ 3847314793802517^2048*50000^8459 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7059 50000 3847314793802517 12500000000000000000 8459 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7059/50000 : ℝ)) (X := (3847314793802517/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006615321280611933/25000000000000000000 : ℝ) ≤ (10000640587287639/10000000000000000 : ℝ) ^ (8459/2048 : ℝ) := by
    have hpowers : (25006615321280611933/25000000000000000000 : ℝ)^2048 ≤ (10000640587287639/10000000000000000 : ℝ)^8459 := by
      have hnat : (25006615321280611933 : ℕ)^2048*10000000000000000^8459 ≤ 10000640587287639^8459*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006615321280611933 25000000000000000000 10000640587287639 10000000000000000 2048 8459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000640587287639/10000000000000000 : ℝ)) (X := (25006615321280611933/25000000000000000000 : ℝ)) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022004580455822001/50000000000000000000 : ℝ) ≤ (10001065323729149/10000000000000000 : ℝ) ^ (8459/2048 : ℝ) := by
    have hpowers : (50022004580455822001/50000000000000000000 : ℝ)^2048 ≤ (10001065323729149/10000000000000000 : ℝ)^8459 := by
      have hnat : (50022004580455822001 : ℕ)^2048*10000000000000000^8459 ≤ 10001065323729149^8459*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022004580455822001 50000000000000000000 10001065323729149 10000000000000000 2048 8459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001065323729149/10000000000000000 : ℝ)) (X := (50022004580455822001/50000000000000000000 : ℝ)) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253847314793802517/6250000000000000000 : ℝ) ≤ (10001490060170659/10000000000000000 : ℝ) ^ (8459/2048 : ℝ) := by
    have hpowers : (6253847314793802517/6250000000000000000 : ℝ)^2048 ≤ (10001490060170659/10000000000000000 : ℝ)^8459 := by
      have hnat : (6253847314793802517 : ℕ)^2048*10000000000000000^8459 ≤ 10001490060170659^8459*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253847314793802517 6250000000000000000 10001490060170659 10000000000000000 2048 8459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001490060170659/10000000000000000 : ℝ)) (X := (6253847314793802517/6250000000000000000 : ℝ)) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6615321280611933/50000000000000000000 : ℝ) ≤ ((29990685286072349/30000000000000000 : ℝ)+2*(1464608419/900000000000 : ℝ)*(2877/25000 : ℝ))^(8459/2048 : ℝ) := by
    rw [show (29990685286072349/30000000000000000 : ℝ)+2*(1464608419/900000000000 : ℝ)*(2877/25000 : ℝ)=(10000640587287639/10000000000000000 : ℝ) by norm_num, show 1+2*(6615321280611933/50000000000000000000 : ℝ)=(25006615321280611933/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3847314793802517/12500000000000000000 : ℝ)+(6615321280611933/50000000000000000000 : ℝ) ≤ ((29990685286072349/30000000000000000 : ℝ)+(1464608419/900000000000 : ℝ)*((7059/50000 : ℝ)+(2877/25000 : ℝ)))^(8459/2048 : ℝ) := by
    rw [show (29990685286072349/30000000000000000 : ℝ)+(1464608419/900000000000 : ℝ)*((7059/50000 : ℝ)+(2877/25000 : ℝ))=(10001065323729149/10000000000000000 : ℝ) by norm_num, show 1+(3847314793802517/12500000000000000000 : ℝ)+(6615321280611933/50000000000000000000 : ℝ)=(50022004580455822001/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3847314793802517/12500000000000000000 : ℝ) ≤ ((29990685286072349/30000000000000000 : ℝ)+2*(1464608419/900000000000 : ℝ)*(7059/50000 : ℝ))^(8459/2048 : ℝ) := by
    rw [show (29990685286072349/30000000000000000 : ℝ)+2*(1464608419/900000000000 : ℝ)*(7059/50000 : ℝ)=(10001490060170659/10000000000000000 : ℝ) by norm_num, show 1+2*(3847314793802517/12500000000000000000 : ℝ)=(6253847314793802517/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (29990685286072349/30000000000000000 : ℝ)*(X 1 0+X 2 0)+(1464608419/900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8459/2048 : ℝ)) (lo := (2877/25000 : ℝ)) (hi := (7059/50000 : ℝ)) (c := (29990685286072349/30000000000000000 : ℝ)) (alpha := (1464608419/900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (29990685286072349/30000000000000000 : ℝ)*(X 0 1+X 2 1)+(1464608419/900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8459/2048 : ℝ)) (lo := (2877/25000 : ℝ)) (hi := (7059/50000 : ℝ)) (c := (29990685286072349/30000000000000000 : ℝ)) (alpha := (1464608419/900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (29990685286072349/30000000000000000 : ℝ)*(X 0 2+X 1 2)+(1464608419/900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8459/2048 : ℝ)) (lo := (2877/25000 : ℝ)) (hi := (7059/50000 : ℝ)) (c := (29990685286072349/30000000000000000 : ℝ)) (alpha := (1464608419/900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-421701523/2000000000 : ℝ)*X 0 0+(134767267/250000000 : ℝ)*X 0 1+(2633789257/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672081437/5000000000 : ℝ)*X 1 0+(-542730611/2500000000 : ℝ)*X 1 1+(658447313/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672081431/5000000000 : ℝ)*X 2 0+(2633789257/5000000000 : ℝ)*X 2 1+(-2170922447/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2173678877/5000000000 : ℝ)*X 0 0+(4223634279/10000000000 : ℝ)*X 0 1+(4474582109/10000000000 : ℝ)*X 0 2+(2173678877/5000000000 : ℝ)*X 1 0+(4223634279/10000000000 : ℝ)*X 1 1+(4474582109/10000000000 : ℝ)*X 1 2+(2173678877/5000000000 : ℝ)*X 2 0+(4223634279/10000000000 : ℝ)*X 2 1+(4474582109/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2108512217/10000000000 : ℝ)*X 0 0+(2633944543/5000000000 : ℝ)*X 0 1+(168449343/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328174411/2500000000 : ℝ)*X 1 0+(-2048121979/10000000000 : ℝ)*X 1 1+(215615159/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328174411/2500000000 : ℝ)*X 2 0+(168449343/312500000 : ℝ)*X 2 1+(-2048121979/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((434736713/1000000000 : ℝ)*X 0 0+(4473949033/10000000000 : ℝ)*X 0 1+(4224269641/10000000000 : ℝ)*X 0 2+(434736713/1000000000 : ℝ)*X 1 0+(4473949033/10000000000 : ℝ)*X 1 1+(4224269641/10000000000 : ℝ)*X 1 2+(434736713/1000000000 : ℝ)*X 2 0+(4473949033/10000000000 : ℝ)*X 2 1+(4224269641/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2706871241226558047/625000000000000000000000 : ℝ) := by norm_num
    linear_combination (412106303/50000000000000 : ℝ)*(base19) + (372935959/50000000000000 : ℝ)*(base23) + (16059637/50000000000000 : ℝ)*(lower2) + (3407641/3125000000000 : ℝ)*(upper3) + (2279897/4000000000000 : ℝ)*(upper5) + (1513454414894551/25000000000000 : ℝ)*(major0) + (1513454414894551/25000000000000 : ℝ)*(major1) + (1513454414894551/25000000000000 : ℝ)*(major2) + (406134903395563/5000000000000 : ℝ)*(sp0) + (2030679866378349/25000000000000 : ℝ)*(sp1) + (8122719543854083/100000000000000 : ℝ)*(sp2) + (1992451380963217/50000000000000 : ℝ)*(sp3) + (22221814741/100000000000000 : ℝ)*(sp4) + (969851/8000000000 : ℝ)*(sp7) + (1992457442531967/50000000000000 : ℝ)*(f.failure) + (8122720289726001/100000000000000 : ℝ)*(f.sum) + (144981084779/45000000000000000000000000 : ℝ)*base66 + (727082110510897/2250000000000000000000000000000 : ℝ)*base67 + (10338457376989103/2250000000000000000000000000000 : ℝ)*base70 + (33967317097510897/2250000000000000000000000000000 : ℝ)*base71 + (22455047407/22500000000000000000000000 : ℝ)*base74 + (54451252514989103/2250000000000000000000000000000 : ℝ)*base76 + (3073995146989103/2250000000000000000000000000000 : ℝ)*base78 + (7960609054510897/2250000000000000000000000000000 : ℝ)*base79 + (80068457249/45000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (452183/156250000000000000000 : ℝ)*base89 + (452183/156250000000000000000 : ℝ)*base91 + (452183/156250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1902614518574862719613029/300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1131916613/100000000000000 : ℝ)*(base19) + (76851153/6250000000000 : ℝ)*(base23) + (393591709/100000000000000 : ℝ)*(lower1) + (127362563/100000000000000 : ℝ)*(upper3) + (44432179/100000000000000 : ℝ)*(lower4) + (1041383/800000000000 : ℝ)*(upper5) + (1216902609887107/20000000000000 : ℝ)*(major0) + (1216902609887107/20000000000000 : ℝ)*(major1) + (1216902609887107/20000000000000 : ℝ)*(major2) + (118763703/5000000000000 : ℝ)*(sp2) + (408195290786219/5000000000000 : ℝ)*(sp4) + (4081952341903883/50000000000000 : ℝ)*(sp5) + (8163902210831871/100000000000000 : ℝ)*(sp6) + (4005120071745067/100000000000000 : ℝ)*(sp7) + (4005120071745067/100000000000000 : ℝ)*(f.failure) + (408195290786219/5000000000000 : ℝ)*(f.sum) + (21174521417/9000000000000000000000000 : ℝ)*base66 + (57391830047586971/1800000000000000000000000000000 : ℝ)*base68 + (243163867613029/1800000000000000000000000000000 : ℝ)*base69 + (8503585468986971/1800000000000000000000000000000 : ℝ)*base72 + (499917223/112500000000000000000000 : ℝ)*base74 + (24317290921613029/1800000000000000000000000000000 : ℝ)*base75 + (3983188480986971/1800000000000000000000000000000 : ℝ)*base78 + (24344863708386971/1800000000000000000000000000000 : ℝ)*base80 + (7271813071/9000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (290917/312500000000000000000 : ℝ)*base90 + (290917/312500000000000000000 : ℝ)*base92 + (290917/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1267_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4747449/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7059/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2877/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11509/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14117/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1267_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1267_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4747449/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14141/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5743/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11509/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14117/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1267_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1267_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1267_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4747449/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14141/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5743/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11509/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14117/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1267_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

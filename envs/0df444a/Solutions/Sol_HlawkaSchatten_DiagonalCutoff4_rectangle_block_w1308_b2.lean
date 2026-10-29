-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1308_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:38:41.592312+00:00
-- url     : https://prove2.me/submissions/2762a3ac-adcf-4a26-be33-6662e03b2538

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
theorem support_rectangle_w1308_s6_0 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-82948207/400000000 : ℝ)*x 0 + (5414489797/10000000000 : ℝ)*x 1 + (1310869453/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82948207/400000000 : ℝ)^1067 ≤ (6310177801269/50000000000000 : ℝ)^811 := by
    have hnat : (82948207 : ℕ)^1067*50000000000000^811 ≤ 6310177801269^811*400000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82948207 400000000 6310177801269 50000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414489797/10000000000 : ℝ)^1067 ≤ (44612072371907/100000000000000 : ℝ)^811 := by
    have hnat : (5414489797 : ℕ)^1067*100000000000000^811 ≤ 44612072371907^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414489797 10000000000 44612072371907 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310869453/2500000000 : ℝ)^1067 ≤ (5345946500351/12500000000000 : ℝ)^811 := by
    have hnat : (1310869453 : ℕ)^1067*12500000000000^811 ≤ 5345946500351^811*2500000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310869453 2500000000 5345946500351 12500000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-82948207/400000000 : ℝ), (5414489797/10000000000 : ℝ), (1310869453/2500000000 : ℝ)] ![(6310177801269/50000000000000 : ℝ), (44612072371907/100000000000000 : ℝ), (5345946500351/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-82948207/400000000 : ℝ)|^1067 ≤ (6310177801269/50000000000000 : ℝ)^811
        have hw : |(-82948207/400000000 : ℝ)|=(82948207/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414489797/10000000000 : ℝ)|^1067 ≤ (44612072371907/100000000000000 : ℝ)^811
        have hw : |(5414489797/10000000000 : ℝ)|=(5414489797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310869453/2500000000 : ℝ)|^1067 ≤ (5345946500351/12500000000000 : ℝ)^811
        have hw : |(1310869453/2500000000 : ℝ)|=(1310869453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1308_s6_1 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5349563973/10000000000 : ℝ)*x 0 + (-432173149/2000000000 : ℝ)*x 1 + (5243477537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349563973/10000000000 : ℝ)^1067 ≤ (21954798644837/50000000000000 : ℝ)^811 := by
    have hnat : (5349563973 : ℕ)^1067*50000000000000^811 ≤ 21954798644837^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349563973 10000000000 21954798644837 50000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (432173149/2000000000 : ℝ)^1067 ≤ (13322833635697/100000000000000 : ℝ)^811 := by
    have hnat : (432173149 : ℕ)^1067*100000000000000^811 ≤ 13322833635697^811*2000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432173149 2000000000 13322833635697 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243477537/10000000000 : ℝ)^1067 ≤ (42767569051793/100000000000000 : ℝ)^811 := by
    have hnat : (5243477537 : ℕ)^1067*100000000000000^811 ≤ 42767569051793^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243477537 10000000000 42767569051793 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349563973/10000000000 : ℝ), (-432173149/2000000000 : ℝ), (5243477537/10000000000 : ℝ)] ![(21954798644837/50000000000000 : ℝ), (13322833635697/100000000000000 : ℝ), (42767569051793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349563973/10000000000 : ℝ)|^1067 ≤ (21954798644837/50000000000000 : ℝ)^811
        have hw : |(5349563973/10000000000 : ℝ)|=(5349563973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-432173149/2000000000 : ℝ)|^1067 ≤ (13322833635697/100000000000000 : ℝ)^811
        have hw : |(-432173149/2000000000 : ℝ)|=(432173149/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243477537/10000000000 : ℝ)|^1067 ≤ (42767569051793/100000000000000 : ℝ)^811
        have hw : |(5243477537/10000000000 : ℝ)|=(5243477537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1308_s6_2 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5349563407/10000000000 : ℝ)*x 0 + (2621738883/5000000000 : ℝ)*x 1 + (-432173239/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349563407/10000000000 : ℝ)^1067 ≤ (2744349448589/6250000000000 : ℝ)^811 := by
    have hnat : (5349563407 : ℕ)^1067*6250000000000^811 ≤ 2744349448589^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349563407 10000000000 2744349448589 6250000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621738883/5000000000 : ℝ)^1067 ≤ (42767571509183/100000000000000 : ℝ)^811 := by
    have hnat : (2621738883 : ℕ)^1067*100000000000000^811 ≤ 42767571509183^811*5000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621738883 5000000000 42767571509183 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (432173239/2000000000 : ℝ)^1067 ≤ (6661418642983/50000000000000 : ℝ)^811 := by
    have hnat : (432173239 : ℕ)^1067*50000000000000^811 ≤ 6661418642983^811*2000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432173239 2000000000 6661418642983 50000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349563407/10000000000 : ℝ), (2621738883/5000000000 : ℝ), (-432173239/2000000000 : ℝ)] ![(2744349448589/6250000000000 : ℝ), (42767571509183/100000000000000 : ℝ), (6661418642983/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349563407/10000000000 : ℝ)|^1067 ≤ (2744349448589/6250000000000 : ℝ)^811
        have hw : |(5349563407/10000000000 : ℝ)|=(5349563407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621738883/5000000000 : ℝ)|^1067 ≤ (42767571509183/100000000000000 : ℝ)^811
        have hw : |(2621738883/5000000000 : ℝ)|=(2621738883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-432173239/2000000000 : ℝ)|^1067 ≤ (6661418642983/50000000000000 : ℝ)^811
        have hw : |(-432173239/2000000000 : ℝ)|=(432173239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1308_s6_3 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2167792513/5000000000 : ℝ)*x 0 + (520274563/1250000000 : ℝ)*x 1 + (1128954297/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2167792513/5000000000 : ℝ)^1067 ≤ (33302612451633/100000000000000 : ℝ)^811 := by
    have hnat : (2167792513 : ℕ)^1067*100000000000000^811 ≤ 33302612451633^811*5000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2167792513 5000000000 33302612451633 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (520274563/1250000000 : ℝ)^1067 ≤ (631230628417/2000000000000 : ℝ)^811 := by
    have hnat : (520274563 : ℕ)^1067*2000000000000^811 ≤ 631230628417^811*1250000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520274563 1250000000 631230628417 2000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1128954297/2500000000 : ℝ)^1067 ≤ (3513585610867/10000000000000 : ℝ)^811 := by
    have hnat : (1128954297 : ℕ)^1067*10000000000000^811 ≤ 3513585610867^811*2500000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128954297 2500000000 3513585610867 10000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2167792513/5000000000 : ℝ), (520274563/1250000000 : ℝ), (1128954297/2500000000 : ℝ)] ![(33302612451633/100000000000000 : ℝ), (631230628417/2000000000000 : ℝ), (3513585610867/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2167792513/5000000000 : ℝ)|^1067 ≤ (33302612451633/100000000000000 : ℝ)^811
        have hw : |(2167792513/5000000000 : ℝ)|=(2167792513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(520274563/1250000000 : ℝ)|^1067 ≤ (631230628417/2000000000000 : ℝ)^811
        have hw : |(520274563/1250000000 : ℝ)|=(520274563/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1128954297/2500000000 : ℝ)|^1067 ≤ (3513585610867/10000000000000 : ℝ)^811
        have hw : |(1128954297/2500000000 : ℝ)|=(1128954297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1308_s6_4 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1036859071/5000000000 : ℝ)*x 0 + (5244088503/10000000000 : ℝ)*x 1 + (2706937831/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1036859071/5000000000 : ℝ)^1067 ≤ (12620459429007/100000000000000 : ℝ)^811 := by
    have hnat : (1036859071 : ℕ)^1067*100000000000000^811 ≤ 12620459429007^811*5000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036859071 5000000000 12620459429007 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244088503/10000000000 : ℝ)^1067 ≤ (42774125426221/100000000000000 : ℝ)^811 := by
    have hnat : (5244088503 : ℕ)^1067*100000000000000^811 ≤ 42774125426221^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244088503 10000000000 42774125426221 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706937831/5000000000 : ℝ)^1067 ≤ (1115135378189/2500000000000 : ℝ)^811 := by
    have hnat : (2706937831 : ℕ)^1067*2500000000000^811 ≤ 1115135378189^811*5000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706937831 5000000000 1115135378189 2500000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1036859071/5000000000 : ℝ), (5244088503/10000000000 : ℝ), (2706937831/5000000000 : ℝ)] ![(12620459429007/100000000000000 : ℝ), (42774125426221/100000000000000 : ℝ), (1115135378189/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1036859071/5000000000 : ℝ)|^1067 ≤ (12620459429007/100000000000000 : ℝ)^811
        have hw : |(-1036859071/5000000000 : ℝ)|=(1036859071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244088503/10000000000 : ℝ)|^1067 ≤ (42774125426221/100000000000000 : ℝ)^811
        have hw : |(5244088503/10000000000 : ℝ)|=(5244088503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706937831/5000000000 : ℝ)|^1067 ≤ (1115135378189/2500000000000 : ℝ)^811
        have hw : |(2706937831/5000000000 : ℝ)|=(2706937831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1308_s6_5 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305692907/10000000000 : ℝ)*x 0 + (-995233969/5000000000 : ℝ)*x 1 + (5413875553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305692907/10000000000 : ℝ)^1067 ≤ (43436446820633/100000000000000 : ℝ)^811 := by
    have hnat : (5305692907 : ℕ)^1067*100000000000000^811 ≤ 43436446820633^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305692907 10000000000 43436446820633 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (995233969/5000000000 : ℝ)^1067 ≤ (5979069611059/50000000000000 : ℝ)^811 := by
    have hnat : (995233969 : ℕ)^1067*50000000000000^811 ≤ 5979069611059^811*5000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      995233969 5000000000 5979069611059 50000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413875553/10000000000 : ℝ)^1067 ≤ (44605413946017/100000000000000 : ℝ)^811 := by
    have hnat : (5413875553 : ℕ)^1067*100000000000000^811 ≤ 44605413946017^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413875553 10000000000 44605413946017 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305692907/10000000000 : ℝ), (-995233969/5000000000 : ℝ), (5413875553/10000000000 : ℝ)] ![(43436446820633/100000000000000 : ℝ), (5979069611059/50000000000000 : ℝ), (44605413946017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305692907/10000000000 : ℝ)|^1067 ≤ (43436446820633/100000000000000 : ℝ)^811
        have hw : |(5305692907/10000000000 : ℝ)|=(5305692907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-995233969/5000000000 : ℝ)|^1067 ≤ (5979069611059/50000000000000 : ℝ)^811
        have hw : |(-995233969/5000000000 : ℝ)|=(995233969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413875553/10000000000 : ℝ)|^1067 ≤ (44605413946017/100000000000000 : ℝ)^811
        have hw : |(5413875553/10000000000 : ℝ)|=(5413875553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1308_s6_6 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305692091/10000000000 : ℝ)*x 0 + (338367257/625000000 : ℝ)*x 1 + (-497617071/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305692091/10000000000 : ℝ)^1067 ≤ (43436438031503/100000000000000 : ℝ)^811 := by
    have hnat : (5305692091 : ℕ)^1067*100000000000000^811 ≤ 43436438031503^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305692091 10000000000 43436438031503 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338367257/625000000 : ℝ)^1067 ≤ (2787838750343/6250000000000 : ℝ)^811 := by
    have hnat : (338367257 : ℕ)^1067*6250000000000^811 ≤ 2787838750343^811*625000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338367257 625000000 2787838750343 6250000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (497617071/2500000000 : ℝ)^1067 ≤ (5979070978467/50000000000000 : ℝ)^811 := by
    have hnat : (497617071 : ℕ)^1067*50000000000000^811 ≤ 5979070978467^811*2500000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497617071 2500000000 5979070978467 50000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305692091/10000000000 : ℝ), (338367257/625000000 : ℝ), (-497617071/2500000000 : ℝ)] ![(43436438031503/100000000000000 : ℝ), (2787838750343/6250000000000 : ℝ), (5979070978467/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305692091/10000000000 : ℝ)|^1067 ≤ (43436438031503/100000000000000 : ℝ)^811
        have hw : |(5305692091/10000000000 : ℝ)|=(5305692091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338367257/625000000 : ℝ)|^1067 ≤ (2787838750343/6250000000000 : ℝ)^811
        have hw : |(338367257/625000000 : ℝ)|=(338367257/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-497617071/2500000000 : ℝ)|^1067 ≤ (5979070978467/50000000000000 : ℝ)^811
        have hw : |(-497617071/2500000000 : ℝ)|=(497617071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1308_s6_7 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (867122263/2000000000 : ℝ)*x 0 + (1128638499/2500000000 : ℝ)*x 1 + (832693177/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (867122263/2000000000 : ℝ)^1067 ≤ (33302878125381/100000000000000 : ℝ)^811 := by
    have hnat : (867122263 : ℕ)^1067*100000000000000^811 ≤ 33302878125381^811*2000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      867122263 2000000000 33302878125381 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1128638499/2500000000 : ℝ)^1067 ≤ (8780731457059/25000000000000 : ℝ)^811 := by
    have hnat : (1128638499 : ℕ)^1067*25000000000000^811 ≤ 8780731457059^811*2500000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128638499 2500000000 8780731457059 25000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (832693177/2000000000 : ℝ)^1067 ≤ (15787098017301/50000000000000 : ℝ)^811 := by
    have hnat : (832693177 : ℕ)^1067*50000000000000^811 ≤ 15787098017301^811*2000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      832693177 2000000000 15787098017301 50000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(867122263/2000000000 : ℝ), (1128638499/2500000000 : ℝ), (832693177/2000000000 : ℝ)] ![(33302878125381/100000000000000 : ℝ), (8780731457059/25000000000000 : ℝ), (15787098017301/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(867122263/2000000000 : ℝ)|^1067 ≤ (33302878125381/100000000000000 : ℝ)^811
        have hw : |(867122263/2000000000 : ℝ)|=(867122263/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1128638499/2500000000 : ℝ)|^1067 ≤ (8780731457059/25000000000000 : ℝ)^811
        have hw : |(1128638499/2500000000 : ℝ)|=(1128638499/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(832693177/2000000000 : ℝ)|^1067 ≤ (15787098017301/50000000000000 : ℝ)^811
        have hw : |(832693177/2000000000 : ℝ)|=(832693177/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1308_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153390473/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1837/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (691/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (5533/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7343/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1837/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (691/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1837/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (691/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1837/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (691/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1837/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (691/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1837/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (691/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1837/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (691/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (691/6250 : ℝ) ^ (4267/1024 : ℝ) ≤ (10343808294833637/100000000000000000000 : ℝ) := by
    have hpowers : (691/6250 : ℝ)^4267 ≤ (10343808294833637/100000000000000000000 : ℝ)^1024 := by
      have hnat : (691 : ℕ)^4267*100000000000000000000^1024 ≤ 10343808294833637^1024*6250^4267 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        691 6250 10343808294833637 100000000000000000000 4267 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (691/6250 : ℝ)) (X := (10343808294833637/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4267 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1837/12500 : ℝ) ^ (4267/1024 : ℝ) ≤ (1058218520389731/3125000000000000000 : ℝ) := by
    have hpowers : (1837/12500 : ℝ)^4267 ≤ (1058218520389731/3125000000000000000 : ℝ)^1024 := by
      have hnat : (1837 : ℕ)^4267*3125000000000000000^1024 ≤ 1058218520389731^1024*12500^4267 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1837 12500 1058218520389731 3125000000000000000 4267 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1837/12500 : ℝ)) (X := (1058218520389731/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4267 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010343808294833637/50000000000000000000 : ℝ) ≤ (5000248212493589/5000000000000000 : ℝ) ^ (4267/1024 : ℝ) := by
    have hpowers : (50010343808294833637/50000000000000000000 : ℝ)^1024 ≤ (5000248212493589/5000000000000000 : ℝ)^4267 := by
      have hnat : (50010343808294833637 : ℕ)^1024*5000000000000000^4267 ≤ 5000248212493589^4267*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010343808294833637 50000000000000000000 5000248212493589 5000000000000000 1024 4267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000248212493589/5000000000000000 : ℝ)) (X := (50010343808294833637/50000000000000000000 : ℝ)) (by norm_num) 4267 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044206800947305029/100000000000000000000 : ℝ) ≤ (1000106070217039/1000000000000000 : ℝ) ^ (4267/1024 : ℝ) := by
    have hpowers : (100044206800947305029/100000000000000000000 : ℝ)^1024 ≤ (1000106070217039/1000000000000000 : ℝ)^4267 := by
      have hnat : (100044206800947305029 : ℕ)^1024*1000000000000000^4267 ≤ 1000106070217039^4267*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044206800947305029 100000000000000000000 1000106070217039 1000000000000000 1024 4267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000106070217039/1000000000000000 : ℝ)) (X := (100044206800947305029/100000000000000000000 : ℝ)) (by norm_num) 4267 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1563558218520389731/1562500000000000000 : ℝ) ≤ (5000812489676801/5000000000000000 : ℝ) ^ (4267/1024 : ℝ) := by
    have hpowers : (1563558218520389731/1562500000000000000 : ℝ)^1024 ≤ (5000812489676801/5000000000000000 : ℝ)^4267 := by
      have hnat : (1563558218520389731 : ℕ)^1024*5000000000000000^4267 ≤ 5000812489676801^4267*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563558218520389731 1562500000000000000 5000812489676801 5000000000000000 1024 4267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000812489676801/5000000000000000 : ℝ)) (X := (1563558218520389731/1562500000000000000 : ℝ)) (by norm_num) 4267 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10343808294833637/100000000000000000000 : ℝ) ≤ ((2274333105617384011/2275000000000000000 : ℝ)+2*(141069295803/91000000000000 : ℝ)*(691/6250 : ℝ))^(4267/1024 : ℝ) := by
    rw [show (2274333105617384011/2275000000000000000 : ℝ)+2*(141069295803/91000000000000 : ℝ)*(691/6250 : ℝ)=(5000248212493589/5000000000000000 : ℝ) by norm_num, show 1+2*(10343808294833637/100000000000000000000 : ℝ)=(50010343808294833637/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1058218520389731/3125000000000000000 : ℝ)+(10343808294833637/100000000000000000000 : ℝ) ≤ ((2274333105617384011/2275000000000000000 : ℝ)+(141069295803/91000000000000 : ℝ)*((1837/12500 : ℝ)+(691/6250 : ℝ)))^(4267/1024 : ℝ) := by
    rw [show (2274333105617384011/2275000000000000000 : ℝ)+(141069295803/91000000000000 : ℝ)*((1837/12500 : ℝ)+(691/6250 : ℝ))=(1000106070217039/1000000000000000 : ℝ) by norm_num, show 1+(1058218520389731/3125000000000000000 : ℝ)+(10343808294833637/100000000000000000000 : ℝ)=(100044206800947305029/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1058218520389731/3125000000000000000 : ℝ) ≤ ((2274333105617384011/2275000000000000000 : ℝ)+2*(141069295803/91000000000000 : ℝ)*(1837/12500 : ℝ))^(4267/1024 : ℝ) := by
    rw [show (2274333105617384011/2275000000000000000 : ℝ)+2*(141069295803/91000000000000 : ℝ)*(1837/12500 : ℝ)=(5000812489676801/5000000000000000 : ℝ) by norm_num, show 1+2*(1058218520389731/3125000000000000000 : ℝ)=(1563558218520389731/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2274333105617384011/2275000000000000000 : ℝ)*(X 1 0+X 2 0)+(141069295803/91000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4267/1024 : ℝ)) (lo := (691/6250 : ℝ)) (hi := (1837/12500 : ℝ)) (c := (2274333105617384011/2275000000000000000 : ℝ)) (alpha := (141069295803/91000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2274333105617384011/2275000000000000000 : ℝ)*(X 0 1+X 2 1)+(141069295803/91000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4267/1024 : ℝ)) (lo := (691/6250 : ℝ)) (hi := (1837/12500 : ℝ)) (c := (2274333105617384011/2275000000000000000 : ℝ)) (alpha := (141069295803/91000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2274333105617384011/2275000000000000000 : ℝ)*(X 0 2+X 1 2)+(141069295803/91000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4267/1024 : ℝ)) (lo := (691/6250 : ℝ)) (hi := (1837/12500 : ℝ)) (c := (2274333105617384011/2275000000000000000 : ℝ)) (alpha := (141069295803/91000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-82948207/400000000 : ℝ)*X 0 0+(5414489797/10000000000 : ℝ)*X 0 1+(1310869453/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349563973/10000000000 : ℝ)*X 1 0+(-432173149/2000000000 : ℝ)*X 1 1+(5243477537/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349563407/10000000000 : ℝ)*X 2 0+(2621738883/5000000000 : ℝ)*X 2 1+(-432173239/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2167792513/5000000000 : ℝ)*X 0 0+(520274563/1250000000 : ℝ)*X 0 1+(1128954297/2500000000 : ℝ)*X 0 2+(2167792513/5000000000 : ℝ)*X 1 0+(520274563/1250000000 : ℝ)*X 1 1+(1128954297/2500000000 : ℝ)*X 1 2+(2167792513/5000000000 : ℝ)*X 2 0+(520274563/1250000000 : ℝ)*X 2 1+(1128954297/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1036859071/5000000000 : ℝ)*X 0 0+(5244088503/10000000000 : ℝ)*X 0 1+(2706937831/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305692907/10000000000 : ℝ)*X 1 0+(-995233969/5000000000 : ℝ)*X 1 1+(5413875553/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305692091/10000000000 : ℝ)*X 2 0+(338367257/625000000 : ℝ)*X 2 1+(-497617071/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((867122263/2000000000 : ℝ)*X 0 0+(1128638499/2500000000 : ℝ)*X 0 1+(832693177/2000000000 : ℝ)*X 0 2+(867122263/2000000000 : ℝ)*X 1 0+(1128638499/2500000000 : ℝ)*X 1 1+(832693177/2000000000 : ℝ)*X 1 2+(867122263/2000000000 : ℝ)*X 2 0+(1128638499/2500000000 : ℝ)*X 2 1+(832693177/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (404028880960590142128380361/56875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (600690869/50000000000000 : ℝ)*(base19) + (360455749/50000000000000 : ℝ)*(base23) + (21659537/100000000000000 : ℝ)*(upper3) + (16609701/12500000000000 : ℝ)*(lower4) + (2168879373272617/50000000000000 : ℝ)*(major0) + (2168879373272617/50000000000000 : ℝ)*(major1) + (2168879373272617/50000000000000 : ℝ)*(major2) + (5847575157590003/100000000000000 : ℝ)*(sp0) + (5847596783458767/100000000000000 : ℝ)*(sp1) + (2923791915248797/50000000000000 : ℝ)*(sp2) + (565581134574199/20000000000000 : ℝ)*(sp3) + (22827250501/100000000000000 : ℝ)*(sp4) + (6716715707/50000000000000 : ℝ)*(sp6) + (543943419/4000000000000 : ℝ)*(sp7) + (2827919271456471/100000000000000 : ℝ)*(f.failure) + (1169519596968101/20000000000000 : ℝ)*(f.sum) + (7121504417751/2275000000000000000000000000 : ℝ)*base65 + (172026189348701787/113750000000000000000000000000000 : ℝ)*base67 + (183082284512451787/113750000000000000000000000000000 : ℝ)*base69 + (592052218016298213/113750000000000000000000000000000 : ℝ)*base72 + (2459544744019/568750000000000000000000000 : ℝ)*base73 + (506867974326298213/113750000000000000000000000000000 : ℝ)*base76 + (1210907744055048213/113750000000000000000000000000000 : ℝ)*base78 + (1597092068148798213/113750000000000000000000000000000 : ℝ)*base80 + (1733591752619/568750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base87 + (85600783/10000000000000000000000 : ℝ)*base89 + (85600783/10000000000000000000000 : ℝ)*base91 + (85600783/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (368391032964603458196723/31250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2334014879/100000000000000 : ℝ)*(base19) + (683882931/50000000000000 : ℝ)*(base23) + (5460303/1562500000000 : ℝ)*(upper3) + (8263081/50000000000000 : ℝ)*(lower4) + (191906083/100000000000000 : ℝ)*(upper5) + (218450001217721/5000000000000 : ℝ)*(major0) + (218450001217721/5000000000000 : ℝ)*(major1) + (218450001217721/5000000000000 : ℝ)*(major2) + (2408885901/6250000000000 : ℝ)*(sp1) + (27466898349/100000000000000 : ℝ)*(sp2) + (5889713227725527/100000000000000 : ℝ)*(sp4) + (736209043942029/12500000000000 : ℝ)*(sp5) + (5889684393061317/100000000000000 : ℝ)*(sp6) + (712071607008217/25000000000000 : ℝ)*(sp7) + (712071607008217/25000000000000 : ℝ)*(f.failure) + (5889713227725527/100000000000000 : ℝ)*(f.sum) + (2134068109/312500000000000000000000 : ℝ)*base66 + (1417876915692759/125000000000000000000000000000 : ℝ)*base68 + (1143211346317759/125000000000000000000000000000 : ℝ)*base70 + (685210166067759/125000000000000000000000000000 : ℝ)*base72 + (15825895887/2500000000000000000000000 : ℝ)*base74 + (1155637926932241/125000000000000000000000000000 : ℝ)*base75 + (1046739878317759/125000000000000000000000000000 : ℝ)*base78 + (2622983385317759/125000000000000000000000000000 : ℝ)*base80 + (12191267299/5000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (20516641/2500000000000000000000 : ℝ)*base89 + (20516641/2500000000000000000000 : ℝ)*base91 + (20516641/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1308_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153390473/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1837/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (691/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5533/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7343/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1308_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1308_s7_0 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2073714081/10000000000 : ℝ)*x 0 + (1353600597/2500000000 : ℝ)*x 1 + (1048711893/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2073714081/10000000000 : ℝ)^1067 ≤ (3155106728163/25000000000000 : ℝ)^811 := by
    have hnat : (2073714081 : ℕ)^1067*25000000000000^811 ≤ 3155106728163^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073714081 10000000000 3155106728163 25000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353600597/2500000000 : ℝ)^1067 ≤ (44611124840817/100000000000000 : ℝ)^811 := by
    have hnat : (1353600597 : ℕ)^1067*100000000000000^811 ≤ 44611124840817^811*2500000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353600597 2500000000 44611124840817 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048711893/2000000000 : ℝ)^1067 ≤ (2138422411017/5000000000000 : ℝ)^811 := by
    have hnat : (1048711893 : ℕ)^1067*5000000000000^811 ≤ 2138422411017^811*2000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048711893 2000000000 2138422411017 5000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2073714081/10000000000 : ℝ), (1353600597/2500000000 : ℝ), (1048711893/2000000000 : ℝ)] ![(3155106728163/25000000000000 : ℝ), (44611124840817/100000000000000 : ℝ), (2138422411017/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2073714081/10000000000 : ℝ)|^1067 ≤ (3155106728163/25000000000000 : ℝ)^811
        have hw : |(-2073714081/10000000000 : ℝ)|=(2073714081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353600597/2500000000 : ℝ)|^1067 ≤ (44611124840817/100000000000000 : ℝ)^811
        have hw : |(1353600597/2500000000 : ℝ)|=(1353600597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048711893/2000000000 : ℝ)|^1067 ≤ (2138422411017/5000000000000 : ℝ)^811
        have hw : |(1048711893/2000000000 : ℝ)|=(1048711893/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1308_s7_1 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5349541771/10000000000 : ℝ)*x 0 + (-1080393477/5000000000 : ℝ)*x 1 + (5243559439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349541771/10000000000 : ℝ)^1067 ≤ (43909357529829/100000000000000 : ℝ)^811 := by
    have hnat : (5349541771 : ℕ)^1067*100000000000000^811 ≤ 43909357529829^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349541771 10000000000 43909357529829 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1080393477/5000000000 : ℝ)^1067 ≤ (6661097254839/50000000000000 : ℝ)^811 := by
    have hnat : (1080393477 : ℕ)^1067*50000000000000^811 ≤ 6661097254839^811*5000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080393477 5000000000 6661097254839 50000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243559439/10000000000 : ℝ)^1067 ≤ (21384223970667/50000000000000 : ℝ)^811 := by
    have hnat : (5243559439 : ℕ)^1067*50000000000000^811 ≤ 21384223970667^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243559439 10000000000 21384223970667 50000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349541771/10000000000 : ℝ), (-1080393477/5000000000 : ℝ), (5243559439/10000000000 : ℝ)] ![(43909357529829/100000000000000 : ℝ), (6661097254839/50000000000000 : ℝ), (21384223970667/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349541771/10000000000 : ℝ)|^1067 ≤ (43909357529829/100000000000000 : ℝ)^811
        have hw : |(5349541771/10000000000 : ℝ)|=(5349541771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1080393477/5000000000 : ℝ)|^1067 ≤ (6661097254839/50000000000000 : ℝ)^811
        have hw : |(-1080393477/5000000000 : ℝ)|=(1080393477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243559439/10000000000 : ℝ)|^1067 ≤ (21384223970667/50000000000000 : ℝ)^811
        have hw : |(5243559439/10000000000 : ℝ)|=(5243559439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1308_s7_2 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5349541793/10000000000 : ℝ)*x 0 + (5243559503/10000000000 : ℝ)*x 1 + (-54019671/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349541793/10000000000 : ℝ)^1067 ≤ (2744334860463/6250000000000 : ℝ)^811 := by
    have hnat : (5349541793 : ℕ)^1067*6250000000000^811 ≤ 2744334860463^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349541793 10000000000 2744334860463 6250000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243559503/10000000000 : ℝ)^1067 ≤ (42768448628119/100000000000000 : ℝ)^811 := by
    have hnat : (5243559503 : ℕ)^1067*100000000000000^811 ≤ 42768448628119^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243559503 10000000000 42768448628119 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54019671/250000000 : ℝ)^1067 ≤ (6661096792477/50000000000000 : ℝ)^811 := by
    have hnat : (54019671 : ℕ)^1067*50000000000000^811 ≤ 6661096792477^811*250000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54019671 250000000 6661096792477 50000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349541793/10000000000 : ℝ), (5243559503/10000000000 : ℝ), (-54019671/250000000 : ℝ)] ![(2744334860463/6250000000000 : ℝ), (42768448628119/100000000000000 : ℝ), (6661096792477/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349541793/10000000000 : ℝ)|^1067 ≤ (2744334860463/6250000000000 : ℝ)^811
        have hw : |(5349541793/10000000000 : ℝ)|=(5349541793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243559503/10000000000 : ℝ)|^1067 ≤ (42768448628119/100000000000000 : ℝ)^811
        have hw : |(5243559503/10000000000 : ℝ)|=(5243559503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-54019671/250000000 : ℝ)|^1067 ≤ (6661096792477/50000000000000 : ℝ)^811
        have hw : |(-54019671/250000000 : ℝ)|=(54019671/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1308_s7_3 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (433559129/1000000000 : ℝ)*x 0 + (2081185143/5000000000 : ℝ)*x 1 + (1128910409/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (433559129/1000000000 : ℝ)^1067 ≤ (33302675754883/100000000000000 : ℝ)^811 := by
    have hnat : (433559129 : ℕ)^1067*100000000000000^811 ≤ 33302675754883^811*1000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433559129 1000000000 33302675754883 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2081185143/5000000000 : ℝ)^1067 ≤ (1262530606871/4000000000000 : ℝ)^811 := by
    have hnat : (2081185143 : ℕ)^1067*4000000000000^811 ≤ 1262530606871^811*5000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081185143 5000000000 1262530606871 4000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1128910409/2500000000 : ℝ)^1067 ≤ (35134059055737/100000000000000 : ℝ)^811 := by
    have hnat : (1128910409 : ℕ)^1067*100000000000000^811 ≤ 35134059055737^811*2500000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128910409 2500000000 35134059055737 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(433559129/1000000000 : ℝ), (2081185143/5000000000 : ℝ), (1128910409/2500000000 : ℝ)] ![(33302675754883/100000000000000 : ℝ), (1262530606871/4000000000000 : ℝ), (35134059055737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(433559129/1000000000 : ℝ)|^1067 ≤ (33302675754883/100000000000000 : ℝ)^811
        have hw : |(433559129/1000000000 : ℝ)|=(433559129/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2081185143/5000000000 : ℝ)|^1067 ≤ (1262530606871/4000000000000 : ℝ)^811
        have hw : |(2081185143/5000000000 : ℝ)|=(2081185143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1128910409/2500000000 : ℝ)|^1067 ≤ (35134059055737/100000000000000 : ℝ)^811
        have hw : |(1128910409/2500000000 : ℝ)|=(1128910409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1308_s7_4 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2073726533/10000000000 : ℝ)*x 0 + (2622084493/5000000000 : ℝ)*x 1 + (5413789787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2073726533/10000000000 : ℝ)^1067 ≤ (12620526615659/100000000000000 : ℝ)^811 := by
    have hnat : (2073726533 : ℕ)^1067*100000000000000^811 ≤ 12620526615659^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073726533 10000000000 12620526615659 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622084493/5000000000 : ℝ)^1067 ≤ (8554997824043/20000000000000 : ℝ)^811 := by
    have hnat : (2622084493 : ℕ)^1067*20000000000000^811 ≤ 8554997824043^811*5000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622084493 5000000000 8554997824043 20000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413789787/10000000000 : ℝ)^1067 ≤ (44604484258627/100000000000000 : ℝ)^811 := by
    have hnat : (5413789787 : ℕ)^1067*100000000000000^811 ≤ 44604484258627^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413789787 10000000000 44604484258627 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2073726533/10000000000 : ℝ), (2622084493/5000000000 : ℝ), (5413789787/10000000000 : ℝ)] ![(12620526615659/100000000000000 : ℝ), (8554997824043/20000000000000 : ℝ), (44604484258627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2073726533/10000000000 : ℝ)|^1067 ≤ (12620526615659/100000000000000 : ℝ)^811
        have hw : |(-2073726533/10000000000 : ℝ)|=(2073726533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622084493/5000000000 : ℝ)|^1067 ≤ (8554997824043/20000000000000 : ℝ)^811
        have hw : |(2622084493/5000000000 : ℝ)|=(2622084493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413789787/10000000000 : ℝ)|^1067 ≤ (44604484258627/100000000000000 : ℝ)^811
        have hw : |(5413789787/10000000000 : ℝ)|=(5413789787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1308_s7_5 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2652857123/5000000000 : ℝ)*x 0 + (-1990556491/10000000000 : ℝ)*x 1 + (5413789779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652857123/5000000000 : ℝ)^1067 ≤ (43436676663001/100000000000000 : ℝ)^811 := by
    have hnat : (2652857123 : ℕ)^1067*100000000000000^811 ≤ 43436676663001^811*5000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652857123 5000000000 43436676663001 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1990556491/10000000000 : ℝ)^1067 ≤ (11958839158087/100000000000000 : ℝ)^811 := by
    have hnat : (1990556491 : ℕ)^1067*100000000000000^811 ≤ 11958839158087^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1990556491 10000000000 11958839158087 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413789779/10000000000 : ℝ)^1067 ≤ (44604484171909/100000000000000 : ℝ)^811 := by
    have hnat : (5413789779 : ℕ)^1067*100000000000000^811 ≤ 44604484171909^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413789779 10000000000 44604484171909 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652857123/5000000000 : ℝ), (-1990556491/10000000000 : ℝ), (5413789779/10000000000 : ℝ)] ![(43436676663001/100000000000000 : ℝ), (11958839158087/100000000000000 : ℝ), (44604484171909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652857123/5000000000 : ℝ)|^1067 ≤ (43436676663001/100000000000000 : ℝ)^811
        have hw : |(2652857123/5000000000 : ℝ)|=(2652857123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1990556491/10000000000 : ℝ)|^1067 ≤ (11958839158087/100000000000000 : ℝ)^811
        have hw : |(-1990556491/10000000000 : ℝ)|=(1990556491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413789779/10000000000 : ℝ)|^1067 ≤ (44604484171909/100000000000000 : ℝ)^811
        have hw : |(5413789779/10000000000 : ℝ)|=(5413789779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1308_s7_6 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (21222857/40000000 : ℝ)*x 0 + (270689489/500000000 : ℝ)*x 1 + (-1990556483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21222857/40000000 : ℝ)^1067 ≤ (8687335341217/20000000000000 : ℝ)^811 := by
    have hnat : (21222857 : ℕ)^1067*20000000000000^811 ≤ 8687335341217^811*40000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21222857 40000000 8687335341217 20000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270689489/500000000 : ℝ)^1067 ≤ (44604484182749/100000000000000 : ℝ)^811 := by
    have hnat : (270689489 : ℕ)^1067*100000000000000^811 ≤ 44604484182749^811*500000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270689489 500000000 44604484182749 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1990556483/10000000000 : ℝ)^1067 ≤ (5979419547427/50000000000000 : ℝ)^811 := by
    have hnat : (1990556483 : ℕ)^1067*50000000000000^811 ≤ 5979419547427^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1990556483 10000000000 5979419547427 50000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21222857/40000000 : ℝ), (270689489/500000000 : ℝ), (-1990556483/10000000000 : ℝ)] ![(8687335341217/20000000000000 : ℝ), (44604484182749/100000000000000 : ℝ), (5979419547427/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21222857/40000000 : ℝ)|^1067 ≤ (8687335341217/20000000000000 : ℝ)^811
        have hw : |(21222857/40000000 : ℝ)|=(21222857/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270689489/500000000 : ℝ)|^1067 ≤ (44604484182749/100000000000000 : ℝ)^811
        have hw : |(270689489/500000000 : ℝ)|=(270689489/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1990556483/10000000000 : ℝ)|^1067 ≤ (5979419547427/50000000000000 : ℝ)^811
        have hw : |(-1990556483/10000000000 : ℝ)|=(1990556483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1308_s7_7 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2167808621/5000000000 : ℝ)*x 0 + (4514380913/10000000000 : ℝ)*x 1 + (2081818721/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2167808621/5000000000 : ℝ)^1067 ≤ (16651469011531/50000000000000 : ℝ)^811 := by
    have hnat : (2167808621 : ℕ)^1067*50000000000000^811 ≤ 16651469011531^811*5000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2167808621 5000000000 16651469011531 50000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4514380913/10000000000 : ℝ)^1067 ≤ (35121154205741/100000000000000 : ℝ)^811 := by
    have hnat : (4514380913 : ℕ)^1067*100000000000000^811 ≤ 35121154205741^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4514380913 10000000000 35121154205741 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2081818721/5000000000 : ℝ)^1067 ≤ (3157590775223/10000000000000 : ℝ)^811 := by
    have hnat : (2081818721 : ℕ)^1067*10000000000000^811 ≤ 3157590775223^811*5000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081818721 5000000000 3157590775223 10000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2167808621/5000000000 : ℝ), (4514380913/10000000000 : ℝ), (2081818721/5000000000 : ℝ)] ![(16651469011531/50000000000000 : ℝ), (35121154205741/100000000000000 : ℝ), (3157590775223/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2167808621/5000000000 : ℝ)|^1067 ≤ (16651469011531/50000000000000 : ℝ)^811
        have hw : |(2167808621/5000000000 : ℝ)|=(2167808621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4514380913/10000000000 : ℝ)|^1067 ≤ (35121154205741/100000000000000 : ℝ)^811
        have hw : |(4514380913/10000000000 : ℝ)|=(4514380913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2081818721/5000000000 : ℝ)|^1067 ≤ (3157590775223/10000000000000 : ℝ)^811
        have hw : |(2081818721/5000000000 : ℝ)|=(2081818721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1308_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153390473/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7343/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5533/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2767/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3671/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7343/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5533/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7343/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5533/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7343/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5533/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7343/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5533/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7343/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5533/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7343/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5533/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5533/50000 : ℝ) ^ (4267/1024 : ℝ) ≤ (2595712462268909/25000000000000000000 : ℝ) := by
    have hpowers : (5533/50000 : ℝ)^4267 ≤ (2595712462268909/25000000000000000000 : ℝ)^1024 := by
      have hnat : (5533 : ℕ)^4267*25000000000000000000^1024 ≤ 2595712462268909^1024*50000^4267 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5533 50000 2595712462268909 25000000000000000000 4267 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5533/50000 : ℝ)) (X := (2595712462268909/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4267 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7343/50000 : ℝ) ^ (4267/1024 : ℝ) ≤ (33767078895164053/100000000000000000000 : ℝ) := by
    have hpowers : (7343/50000 : ℝ)^4267 ≤ (33767078895164053/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7343 : ℕ)^4267*100000000000000000000^1024 ≤ 33767078895164053^1024*50000^4267 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7343 50000 33767078895164053 100000000000000000000 4267 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7343/50000 : ℝ)) (X := (33767078895164053/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4267 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502595712462268909/12500000000000000000 : ℝ) ≤ (500024914927013/500000000000000 : ℝ) ^ (4267/1024 : ℝ) := by
    have hpowers : (12502595712462268909/12500000000000000000 : ℝ)^1024 ≤ (500024914927013/500000000000000 : ℝ)^4267 := by
      have hnat : (12502595712462268909 : ℕ)^1024*500000000000000^4267 ≤ 500024914927013^4267*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502595712462268909 12500000000000000000 500024914927013 500000000000000 1024 4267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500024914927013/500000000000000 : ℝ)) (X := (12502595712462268909/12500000000000000000 : ℝ)) (by norm_num) 4267 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044149928744239689/100000000000000000000 : ℝ) ≤ (400042373512089/400000000000000 : ℝ) ^ (4267/1024 : ℝ) := by
    have hpowers : (100044149928744239689/100000000000000000000 : ℝ)^1024 ≤ (400042373512089/400000000000000 : ℝ)^4267 := by
      have hnat : (100044149928744239689 : ℕ)^1024*400000000000000^4267 ≤ 400042373512089^4267*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044149928744239689 100000000000000000000 400042373512089 400000000000000 1024 4267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400042373512089/400000000000000 : ℝ)) (X := (100044149928744239689/100000000000000000000 : ℝ)) (by norm_num) 4267 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033767078895164053/50000000000000000000 : ℝ) ≤ (1000162037706419/1000000000000000 : ℝ) ^ (4267/1024 : ℝ) := by
    have hpowers : (50033767078895164053/50000000000000000000 : ℝ)^1024 ≤ (1000162037706419/1000000000000000 : ℝ)^4267 := by
      have hnat : (50033767078895164053 : ℕ)^1024*1000000000000000^4267 ≤ 1000162037706419^4267*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033767078895164053 50000000000000000000 1000162037706419 1000000000000000 1024 4267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000162037706419/1000000000000000 : ℝ)) (X := (50033767078895164053/50000000000000000000 : ℝ)) (by norm_num) 4267 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2595712462268909/25000000000000000000 : ℝ) ≤ ((1809469345988496591/1810000000000000000 : ℝ)+2*(112207852393/72400000000000 : ℝ)*(5533/50000 : ℝ))^(4267/1024 : ℝ) := by
    rw [show (1809469345988496591/1810000000000000000 : ℝ)+2*(112207852393/72400000000000 : ℝ)*(5533/50000 : ℝ)=(500024914927013/500000000000000 : ℝ) by norm_num, show 1+2*(2595712462268909/25000000000000000000 : ℝ)=(12502595712462268909/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33767078895164053/100000000000000000000 : ℝ)+(2595712462268909/25000000000000000000 : ℝ) ≤ ((1809469345988496591/1810000000000000000 : ℝ)+(112207852393/72400000000000 : ℝ)*((7343/50000 : ℝ)+(5533/50000 : ℝ)))^(4267/1024 : ℝ) := by
    rw [show (1809469345988496591/1810000000000000000 : ℝ)+(112207852393/72400000000000 : ℝ)*((7343/50000 : ℝ)+(5533/50000 : ℝ))=(400042373512089/400000000000000 : ℝ) by norm_num, show 1+(33767078895164053/100000000000000000000 : ℝ)+(2595712462268909/25000000000000000000 : ℝ)=(100044149928744239689/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33767078895164053/100000000000000000000 : ℝ) ≤ ((1809469345988496591/1810000000000000000 : ℝ)+2*(112207852393/72400000000000 : ℝ)*(7343/50000 : ℝ))^(4267/1024 : ℝ) := by
    rw [show (1809469345988496591/1810000000000000000 : ℝ)+2*(112207852393/72400000000000 : ℝ)*(7343/50000 : ℝ)=(1000162037706419/1000000000000000 : ℝ) by norm_num, show 1+2*(33767078895164053/100000000000000000000 : ℝ)=(50033767078895164053/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1809469345988496591/1810000000000000000 : ℝ)*(X 1 0+X 2 0)+(112207852393/72400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4267/1024 : ℝ)) (lo := (5533/50000 : ℝ)) (hi := (7343/50000 : ℝ)) (c := (1809469345988496591/1810000000000000000 : ℝ)) (alpha := (112207852393/72400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1809469345988496591/1810000000000000000 : ℝ)*(X 0 1+X 2 1)+(112207852393/72400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4267/1024 : ℝ)) (lo := (5533/50000 : ℝ)) (hi := (7343/50000 : ℝ)) (c := (1809469345988496591/1810000000000000000 : ℝ)) (alpha := (112207852393/72400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1809469345988496591/1810000000000000000 : ℝ)*(X 0 2+X 1 2)+(112207852393/72400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4267/1024 : ℝ)) (lo := (5533/50000 : ℝ)) (hi := (7343/50000 : ℝ)) (c := (1809469345988496591/1810000000000000000 : ℝ)) (alpha := (112207852393/72400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2073714081/10000000000 : ℝ)*X 0 0+(1353600597/2500000000 : ℝ)*X 0 1+(1048711893/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349541771/10000000000 : ℝ)*X 1 0+(-1080393477/5000000000 : ℝ)*X 1 1+(5243559439/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349541793/10000000000 : ℝ)*X 2 0+(5243559503/10000000000 : ℝ)*X 2 1+(-54019671/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((433559129/1000000000 : ℝ)*X 0 0+(2081185143/5000000000 : ℝ)*X 0 1+(1128910409/2500000000 : ℝ)*X 0 2+(433559129/1000000000 : ℝ)*X 1 0+(2081185143/5000000000 : ℝ)*X 1 1+(1128910409/2500000000 : ℝ)*X 1 2+(433559129/1000000000 : ℝ)*X 2 0+(2081185143/5000000000 : ℝ)*X 2 1+(1128910409/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2073726533/10000000000 : ℝ)*X 0 0+(2622084493/5000000000 : ℝ)*X 0 1+(5413789787/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652857123/5000000000 : ℝ)*X 1 0+(-1990556491/10000000000 : ℝ)*X 1 1+(5413789779/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((21222857/40000000 : ℝ)*X 2 0+(270689489/500000000 : ℝ)*X 2 1+(-1990556483/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2167808621/5000000000 : ℝ)*X 0 0+(4514380913/10000000000 : ℝ)*X 0 1+(2081818721/5000000000 : ℝ)*X 0 2+(2167808621/5000000000 : ℝ)*X 1 0+(4514380913/10000000000 : ℝ)*X 1 1+(2081818721/5000000000 : ℝ)*X 1 2+(2167808621/5000000000 : ℝ)*X 2 0+(4514380913/10000000000 : ℝ)*X 2 1+(2081818721/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (379065525318935974792964697/90500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (320850723/50000000000000 : ℝ)*(base19) + (153075681/25000000000000 : ℝ)*(base23) + (1920143/4000000000000 : ℝ)*(upper3) + (5720869/20000000000000 : ℝ)*(upper4) + (37804031/25000000000000 : ℝ)*(upper5) + (4342028218708611/100000000000000 : ℝ)*(major0) + (4342028218708611/100000000000000 : ℝ)*(major1) + (4342028218708611/100000000000000 : ℝ)*(major2) + (5853339409222929/100000000000000 : ℝ)*(sp0) + (1463338245876833/25000000000000 : ℝ)*(sp1) + (2926676506453027/50000000000000 : ℝ)*(sp2) + (2830694538915999/100000000000000 : ℝ)*(sp3) + (14215985849/100000000000000 : ℝ)*(sp4) + (8133673459/100000000000000 : ℝ)*(sp7) + (1415351336294729/50000000000000 : ℝ)*(f.failure) + (5853353625208779/100000000000000 : ℝ)*(f.sum) + (17118342896483/3620000000000000000000000000 : ℝ)*base65 + (508068760991920101/181000000000000000000000000000000 : ℝ)*base67 + (1183875082791079899/181000000000000000000000000000000 : ℝ)*base70 + (1178951340238920101/181000000000000000000000000000000 : ℝ)*base71 + (6910902275737/3620000000000000000000000000 : ℝ)*base74 + (96046579608920101/181000000000000000000000000000000 : ℝ)*base75 + (203336582611079899/181000000000000000000000000000000 : ℝ)*base78 + (2253759896115920101/181000000000000000000000000000000 : ℝ)*base79 + (6992387856717/3620000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1283183/5000000000000000000000 : ℝ)*base90 + (1283183/5000000000000000000000 : ℝ)*base92 + (1283183/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (423667308430292800213729887/45250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1651528319/100000000000000 : ℝ)*(base19) + (1799616179/100000000000000 : ℝ)*(base23) + (283358899/50000000000000 : ℝ)*(lower1) + (11624463/6250000000000 : ℝ)*(upper3) + (1296061/2000000000000 : ℝ)*(lower4) + (24259019/12500000000000 : ℝ)*(upper5) + (2186634798194581/50000000000000 : ℝ)*(major0) + (2186634798194581/50000000000000 : ℝ)*(major1) + (2186634798194581/50000000000000 : ℝ)*(major2) + (1301688869/50000000000000 : ℝ)*(sp2) + (2947734493204703/50000000000000 : ℝ)*(sp4) + (92116677107517/1562500000000 : ℝ)*(sp5) + (589546458341549/10000000000000 : ℝ)*(sp6) + (2851069894275091/100000000000000 : ℝ)*(sp7) + (2851069894275091/100000000000000 : ℝ)*(f.failure) + (2947734493204703/50000000000000 : ℝ)*(f.sum) + (4126286337107/1810000000000000000000000000 : ℝ)*base66 + (1131558027221998371/90500000000000000000000000000000 : ℝ)*base67 + (443298889499498371/90500000000000000000000000000000 : ℝ)*base69 + (13912123843696498371/90500000000000000000000000000000 : ℝ)*base71 + (1126114051417/1810000000000000000000000000 : ℝ)*base74 + (22217110414715501629/90500000000000000000000000000000 : ℝ)*base76 + (333236227413498371/90500000000000000000000000000000 : ℝ)*base77 + (931874018647001629/90500000000000000000000000000000 : ℝ)*base80 + (2016278068413/1810000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (608043/10000000000000000000000 : ℝ)*base89 + (608043/10000000000000000000000 : ℝ)*base91 + (608043/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1308_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153390473/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7343/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5533/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2767/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3671/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1308_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1308_s8_0 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2674768381/5000000000 : ℝ)*x 0 + (2621788107/5000000000 : ℝ)*x 1 + (-2160771431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674768381/5000000000 : ℝ)^1067 ≤ (43909303437581/100000000000000 : ℝ)^811 := by
    have hnat : (2674768381 : ℕ)^1067*100000000000000^811 ≤ 43909303437581^811*5000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674768381 5000000000 43909303437581 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621788107/5000000000 : ℝ)^1067 ≤ (21384313977113/50000000000000 : ℝ)^811 := by
    have hnat : (2621788107 : ℕ)^1067*50000000000000^811 ≤ 21384313977113^811*5000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621788107 5000000000 21384313977113 50000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2160771431/10000000000 : ℝ)^1067 ≤ (2664413718641/20000000000000 : ℝ)^811 := by
    have hnat : (2160771431 : ℕ)^1067*20000000000000^811 ≤ 2664413718641^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160771431 10000000000 2664413718641 20000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674768381/5000000000 : ℝ), (2621788107/5000000000 : ℝ), (-2160771431/10000000000 : ℝ)] ![(43909303437581/100000000000000 : ℝ), (21384313977113/50000000000000 : ℝ), (2664413718641/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674768381/5000000000 : ℝ)|^1067 ≤ (43909303437581/100000000000000 : ℝ)^811
        have hw : |(2674768381/5000000000 : ℝ)|=(2674768381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621788107/5000000000 : ℝ)|^1067 ≤ (21384313977113/50000000000000 : ℝ)^811
        have hw : |(2621788107/5000000000 : ℝ)|=(2621788107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2160771431/10000000000 : ℝ)|^1067 ≤ (2664413718641/20000000000000 : ℝ)^811
        have hw : |(-2160771431/10000000000 : ℝ)|=(2160771431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1308_s8_1 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2073728243/10000000000 : ℝ)*x 0 + (1311046269/2500000000 : ℝ)*x 1 + (2706886297/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2073728243/10000000000 : ℝ)^1067 ≤ (12620540307623/100000000000000 : ℝ)^811 := by
    have hnat : (2073728243 : ℕ)^1067*100000000000000^811 ≤ 12620540307623^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073728243 10000000000 12620540307623 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311046269/2500000000 : ℝ)^1067 ≤ (2673447611793/6250000000000 : ℝ)^811 := by
    have hnat : (1311046269 : ℕ)^1067*6250000000000^811 ≤ 2673447611793^811*2500000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311046269 2500000000 2673447611793 6250000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706886297/5000000000 : ℝ)^1067 ≤ (11151074472571/25000000000000 : ℝ)^811 := by
    have hnat : (2706886297 : ℕ)^1067*25000000000000^811 ≤ 11151074472571^811*5000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706886297 5000000000 11151074472571 25000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2073728243/10000000000 : ℝ), (1311046269/2500000000 : ℝ), (2706886297/5000000000 : ℝ)] ![(12620540307623/100000000000000 : ℝ), (2673447611793/6250000000000 : ℝ), (11151074472571/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2073728243/10000000000 : ℝ)|^1067 ≤ (12620540307623/100000000000000 : ℝ)^811
        have hw : |(-2073728243/10000000000 : ℝ)|=(2073728243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311046269/2500000000 : ℝ)|^1067 ≤ (2673447611793/6250000000000 : ℝ)^811
        have hw : |(1311046269/2500000000 : ℝ)|=(1311046269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706886297/5000000000 : ℝ)|^1067 ≤ (11151074472571/25000000000000 : ℝ)^811
        have hw : |(2706886297/5000000000 : ℝ)|=(2706886297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1308_s8_2 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (265285927/500000000 : ℝ)*x 0 + (-497643531/2500000000 : ℝ)*x 1 + (5413772653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265285927/500000000 : ℝ)^1067 ≤ (4343672291371/10000000000000 : ℝ)^811 := by
    have hnat : (265285927 : ℕ)^1067*10000000000000^811 ≤ 4343672291371^811*500000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265285927 500000000 4343672291371 10000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (497643531/2500000000 : ℝ)^1067 ≤ (11958978533093/100000000000000 : ℝ)^811 := by
    have hnat : (497643531 : ℕ)^1067*100000000000000^811 ≤ 11958978533093^811*2500000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497643531 2500000000 11958978533093 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413772653/10000000000 : ℝ)^1067 ≤ (44604298529831/100000000000000 : ℝ)^811 := by
    have hnat : (5413772653 : ℕ)^1067*100000000000000^811 ≤ 44604298529831^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413772653 10000000000 44604298529831 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265285927/500000000 : ℝ), (-497643531/2500000000 : ℝ), (5413772653/10000000000 : ℝ)] ![(4343672291371/10000000000000 : ℝ), (11958978533093/100000000000000 : ℝ), (44604298529831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265285927/500000000 : ℝ)|^1067 ≤ (4343672291371/10000000000000 : ℝ)^811
        have hw : |(265285927/500000000 : ℝ)|=(265285927/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-497643531/2500000000 : ℝ)|^1067 ≤ (11958978533093/100000000000000 : ℝ)^811
        have hw : |(-497643531/2500000000 : ℝ)|=(497643531/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413772653/10000000000 : ℝ)|^1067 ≤ (44604298529831/100000000000000 : ℝ)^811
        have hw : |(5413772653/10000000000 : ℝ)|=(5413772653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1308_s8_3 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305718551/10000000000 : ℝ)*x 0 + (2706886311/5000000000 : ℝ)*x 1 + (-1990574153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305718551/10000000000 : ℝ)^1067 ≤ (43436723032191/100000000000000 : ℝ)^811 := by
    have hnat : (5305718551 : ℕ)^1067*100000000000000^811 ≤ 43436723032191^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305718551 10000000000 43436723032191 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706886311/5000000000 : ℝ)^1067 ≤ (44604298193797/100000000000000 : ℝ)^811 := by
    have hnat : (2706886311 : ℕ)^1067*100000000000000^811 ≤ 44604298193797^811*5000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706886311 5000000000 44604298193797 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1990574153/10000000000 : ℝ)^1067 ≤ (2989744690579/25000000000000 : ℝ)^811 := by
    have hnat : (1990574153 : ℕ)^1067*25000000000000^811 ≤ 2989744690579^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1990574153 10000000000 2989744690579 25000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305718551/10000000000 : ℝ), (2706886311/5000000000 : ℝ), (-1990574153/10000000000 : ℝ)] ![(43436723032191/100000000000000 : ℝ), (44604298193797/100000000000000 : ℝ), (2989744690579/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305718551/10000000000 : ℝ)|^1067 ≤ (43436723032191/100000000000000 : ℝ)^811
        have hw : |(5305718551/10000000000 : ℝ)|=(5305718551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706886311/5000000000 : ℝ)|^1067 ≤ (44604298193797/100000000000000 : ℝ)^811
        have hw : |(2706886311/5000000000 : ℝ)|=(2706886311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1990574153/10000000000 : ℝ)|^1067 ≤ (2989744690579/25000000000000 : ℝ)^811
        have hw : |(-1990574153/10000000000 : ℝ)|=(1990574153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1308_s8_4 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1083904617/2500000000 : ℝ)*x 0 + (1128586593/2500000000 : ℝ)*x 1 + (832734327/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083904617/2500000000 : ℝ)^1067 ≤ (16651475206451/50000000000000 : ℝ)^811 := by
    have hnat : (1083904617 : ℕ)^1067*50000000000000^811 ≤ 16651475206451^811*2500000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083904617 2500000000 16651475206451 50000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1128586593/2500000000 : ℝ)^1067 ≤ (280966405261/800000000000 : ℝ)^811 := by
    have hnat : (1128586593 : ℕ)^1067*800000000000^811 ≤ 280966405261^811*2500000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128586593 2500000000 280966405261 800000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (832734327/2000000000 : ℝ)^1067 ≤ (7894062229269/25000000000000 : ℝ)^811 := by
    have hnat : (832734327 : ℕ)^1067*25000000000000^811 ≤ 7894062229269^811*2000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      832734327 2000000000 7894062229269 25000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083904617/2500000000 : ℝ), (1128586593/2500000000 : ℝ), (832734327/2000000000 : ℝ)] ![(16651475206451/50000000000000 : ℝ), (280966405261/800000000000 : ℝ), (7894062229269/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083904617/2500000000 : ℝ)|^1067 ≤ (16651475206451/50000000000000 : ℝ)^811
        have hw : |(1083904617/2500000000 : ℝ)|=(1083904617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1128586593/2500000000 : ℝ)|^1067 ≤ (280966405261/800000000000 : ℝ)^811
        have hw : |(1128586593/2500000000 : ℝ)|=(1128586593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(832734327/2000000000 : ℝ)|^1067 ≤ (7894062229269/25000000000000 : ℝ)^811
        have hw : |(832734327/2000000000 : ℝ)|=(832734327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1308_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153390473/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3671/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2767/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2767/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14683/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3671/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2767/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3671/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2767/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3671/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2767/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3671/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2767/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3671/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2767/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3671/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2767/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2767/25000 : ℝ) ^ (4267/1024 : ℝ) ≤ (5195335790068101/50000000000000000000 : ℝ) := by
    have hpowers : (2767/25000 : ℝ)^4267 ≤ (5195335790068101/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2767 : ℕ)^4267*50000000000000000000^1024 ≤ 5195335790068101^1024*25000^4267 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2767 25000 5195335790068101 50000000000000000000 4267 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2767/25000 : ℝ)) (X := (5195335790068101/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4267 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3671/25000 : ℝ) ^ (4267/1024 : ℝ) ≤ (33747920946933543/100000000000000000000 : ℝ) := by
    have hpowers : (3671/25000 : ℝ)^4267 ≤ (33747920946933543/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3671 : ℕ)^4267*100000000000000000000^1024 ≤ 33747920946933543^1024*25000^4267 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3671 25000 33747920946933543 100000000000000000000 4267 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3671/25000 : ℝ)) (X := (33747920946933543/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4267 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005195335790068101/25000000000000000000 : ℝ) ≤ (5000249336947381/5000000000000000 : ℝ) ^ (4267/1024 : ℝ) := by
    have hpowers : (25005195335790068101/25000000000000000000 : ℝ)^1024 ≤ (5000249336947381/5000000000000000 : ℝ)^4267 := by
      have hnat : (25005195335790068101 : ℕ)^1024*5000000000000000^4267 ≤ 5000249336947381^4267*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005195335790068101 25000000000000000000 5000249336947381 5000000000000000 1024 4267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000249336947381/5000000000000000 : ℝ)) (X := (25005195335790068101/25000000000000000000 : ℝ)) (by norm_num) 4267 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008827718505413949/20000000000000000000 : ℝ) ≤ (39066636975959/39062500000000 : ℝ) ^ (4267/1024 : ℝ) := by
    have hpowers : (20008827718505413949/20000000000000000000 : ℝ)^1024 ≤ (39066636975959/39062500000000 : ℝ)^4267 := by
      have hnat : (20008827718505413949 : ℕ)^1024*39062500000000^4267 ≤ 39066636975959^4267*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008827718505413949 20000000000000000000 39066636975959 39062500000000 1024 4267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (39066636975959/39062500000000 : ℝ)) (X := (20008827718505413949/20000000000000000000 : ℝ)) (by norm_num) 4267 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033747920946933543/50000000000000000000 : ℝ) ≤ (5000809728898123/5000000000000000 : ℝ) ^ (4267/1024 : ℝ) := by
    have hpowers : (50033747920946933543/50000000000000000000 : ℝ)^1024 ≤ (5000809728898123/5000000000000000 : ℝ)^4267 := by
      have hnat : (50033747920946933543 : ℕ)^1024*5000000000000000^4267 ≤ 5000809728898123^4267*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033747920946933543 50000000000000000000 5000809728898123 5000000000000000 1024 4267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000809728898123/5000000000000000 : ℝ)) (X := (50033747920946933543/50000000000000000000 : ℝ)) (by norm_num) 4267 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5195335790068101/50000000000000000000 : ℝ) ≤ ((451867479607272931/452000000000000000 : ℝ)+2*(280195975371/180800000000000 : ℝ)*(2767/25000 : ℝ))^(4267/1024 : ℝ) := by
    rw [show (451867479607272931/452000000000000000 : ℝ)+2*(280195975371/180800000000000 : ℝ)*(2767/25000 : ℝ)=(5000249336947381/5000000000000000 : ℝ) by norm_num, show 1+2*(5195335790068101/50000000000000000000 : ℝ)=(25005195335790068101/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33747920946933543/100000000000000000000 : ℝ)+(5195335790068101/50000000000000000000 : ℝ) ≤ ((451867479607272931/452000000000000000 : ℝ)+(280195975371/180800000000000 : ℝ)*((3671/25000 : ℝ)+(2767/25000 : ℝ)))^(4267/1024 : ℝ) := by
    rw [show (451867479607272931/452000000000000000 : ℝ)+(280195975371/180800000000000 : ℝ)*((3671/25000 : ℝ)+(2767/25000 : ℝ))=(39066636975959/39062500000000 : ℝ) by norm_num, show 1+(33747920946933543/100000000000000000000 : ℝ)+(5195335790068101/50000000000000000000 : ℝ)=(20008827718505413949/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33747920946933543/100000000000000000000 : ℝ) ≤ ((451867479607272931/452000000000000000 : ℝ)+2*(280195975371/180800000000000 : ℝ)*(3671/25000 : ℝ))^(4267/1024 : ℝ) := by
    rw [show (451867479607272931/452000000000000000 : ℝ)+2*(280195975371/180800000000000 : ℝ)*(3671/25000 : ℝ)=(5000809728898123/5000000000000000 : ℝ) by norm_num, show 1+2*(33747920946933543/100000000000000000000 : ℝ)=(50033747920946933543/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (451867479607272931/452000000000000000 : ℝ)*(X 1 0+X 2 0)+(280195975371/180800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4267/1024 : ℝ)) (lo := (2767/25000 : ℝ)) (hi := (3671/25000 : ℝ)) (c := (451867479607272931/452000000000000000 : ℝ)) (alpha := (280195975371/180800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (451867479607272931/452000000000000000 : ℝ)*(X 0 1+X 2 1)+(280195975371/180800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4267/1024 : ℝ)) (lo := (2767/25000 : ℝ)) (hi := (3671/25000 : ℝ)) (c := (451867479607272931/452000000000000000 : ℝ)) (alpha := (280195975371/180800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (451867479607272931/452000000000000000 : ℝ)*(X 0 2+X 1 2)+(280195975371/180800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4267/1024 : ℝ)) (lo := (2767/25000 : ℝ)) (hi := (3671/25000 : ℝ)) (c := (451867479607272931/452000000000000000 : ℝ)) (alpha := (280195975371/180800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((2674768381/5000000000 : ℝ)*X 2 0+(2621788107/5000000000 : ℝ)*X 2 1+(-2160771431/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s8_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-2073728243/10000000000 : ℝ)*X 0 0+(1311046269/2500000000 : ℝ)*X 0 1+(2706886297/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s8_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((265285927/500000000 : ℝ)*X 1 0+(-497643531/2500000000 : ℝ)*X 1 1+(5413772653/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s8_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5305718551/10000000000 : ℝ)*X 2 0+(2706886311/5000000000 : ℝ)*X 2 1+(-1990574153/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s8_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((1083904617/2500000000 : ℝ)*X 0 0+(1128586593/2500000000 : ℝ)*X 0 1+(832734327/2000000000 : ℝ)*X 0 2+(1083904617/2500000000 : ℝ)*X 1 0+(1128586593/2500000000 : ℝ)*X 1 1+(832734327/2000000000 : ℝ)*X 1 2+(1083904617/2500000000 : ℝ)*X 2 0+(1128586593/2500000000 : ℝ)*X 2 1+(832734327/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s8_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13753152409633864147233/4520000000000000000000000000 : ℝ) := by norm_num
    linear_combination (572170141/100000000000000 : ℝ)*(base19) + (317451201/50000000000000 : ℝ)*(base23) + (21710357/10000000000000 : ℝ)*(lower1) + (80096879/100000000000000 : ℝ)*(upper3) + (6192967/25000000000000 : ℝ)*(lower4) + (65327267/100000000000000 : ℝ)*(upper5) + (2187071484046093/50000000000000 : ℝ)*(major0) + (2187071484046093/50000000000000 : ℝ)*(major1) + (2187071484046093/50000000000000 : ℝ)*(major2) + (231158497/50000000000000 : ℝ)*(sp0) + (2948323281211237/50000000000000 : ℝ)*(sp1) + (5896645990252333/100000000000000 : ℝ)*(sp2) + (2948322732601539/50000000000000 : ℝ)*(sp3) + (1425819636168729/50000000000000 : ℝ)*(sp4) + (1425819636168729/50000000000000 : ℝ)*(f.failure) + (2948323281211237/50000000000000 : ℝ)*(f.sum) + (29536046723263/4520000000000000000000000000 : ℝ)*base65 + (455439249466033917/22600000000000000000000000000000 : ℝ)*base68 + (183307240250366083/22600000000000000000000000000000 : ℝ)*base69 + (484121536932433917/22600000000000000000000000000000 : ℝ)*base72 + (4312955475823/4520000000000000000000000000 : ℝ)*base73 + (70895475468566083/22600000000000000000000000000000 : ℝ)*base75 + (226628584423966083/22600000000000000000000000000000 : ℝ)*base77 + (164807966833917/22600000000000000000000000000000 : ℝ)*base80 + (3512050356863/4520000000000000000000000000 : ℝ)*base81 + (50881183/5000000000000000000000 : ℝ)*base90 + (50881183/5000000000000000000000 : ℝ)*base92 + (50881183/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1308_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153390473/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3671/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2767/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2767/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14683/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1308_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1308_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153390473/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1837/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (691/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2767/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14683/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1308_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1308_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1308_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153390473/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1837/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (691/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2767/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14683/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1308_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

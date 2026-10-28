-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1145_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:33:29.307585+00:00
-- url     : https://prove2.me/submissions/80c52c8a-7f0d-47a2-82db-97abcd4ea009

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
theorem support_rectangle_w1145_s3_0 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2161680363/10000000000 : ℝ)*x 0 + (5428874739/10000000000 : ℝ)*x 1 + (5232362503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2161680363/10000000000 : ℝ)^4169 ≤ (525124295503/4000000000000 : ℝ)^3145 := by
    have hnat : (2161680363 : ℕ)^4169*4000000000000^3145 ≤ 525124295503^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161680363 10000000000 525124295503 4000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5428874739/10000000000 : ℝ)^4169 ≤ (8899433187667/20000000000000 : ℝ)^3145 := by
    have hnat : (5428874739 : ℕ)^4169*20000000000000^3145 ≤ 8899433187667^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428874739 10000000000 8899433187667 20000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5232362503/10000000000 : ℝ)^4169 ≤ (4237472665551/10000000000000 : ℝ)^3145 := by
    have hnat : (5232362503 : ℕ)^4169*10000000000000^3145 ≤ 4237472665551^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5232362503 10000000000 4237472665551 10000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2161680363/10000000000 : ℝ), (5428874739/10000000000 : ℝ), (5232362503/10000000000 : ℝ)] ![(525124295503/4000000000000 : ℝ), (8899433187667/20000000000000 : ℝ), (4237472665551/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2161680363/10000000000 : ℝ)|^4169 ≤ (525124295503/4000000000000 : ℝ)^3145
        have hw : |(-2161680363/10000000000 : ℝ)|=(2161680363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5428874739/10000000000 : ℝ)|^4169 ≤ (8899433187667/20000000000000 : ℝ)^3145
        have hw : |(5428874739/10000000000 : ℝ)|=(5428874739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5232362503/10000000000 : ℝ)|^4169 ≤ (4237472665551/10000000000000 : ℝ)^3145
        have hw : |(5232362503/10000000000 : ℝ)|=(5232362503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s3_1 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353724057/10000000000 : ℝ)*x 0 + (-1131062117/5000000000 : ℝ)*x 1 + (2616181167/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353724057/10000000000 : ℝ)^4169 ≤ (43682492023709/100000000000000 : ℝ)^3145 := by
    have hnat : (5353724057 : ℕ)^4169*100000000000000^3145 ≤ 43682492023709^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353724057 10000000000 43682492023709 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1131062117/5000000000 : ℝ)^4169 ≤ (871423945293/6250000000000 : ℝ)^3145 := by
    have hnat : (1131062117 : ℕ)^4169*6250000000000^3145 ≤ 871423945293^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131062117 5000000000 871423945293 6250000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2616181167/5000000000 : ℝ)^4169 ≤ (42374724841219/100000000000000 : ℝ)^3145 := by
    have hnat : (2616181167 : ℕ)^4169*100000000000000^3145 ≤ 42374724841219^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2616181167 5000000000 42374724841219 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353724057/10000000000 : ℝ), (-1131062117/5000000000 : ℝ), (2616181167/5000000000 : ℝ)] ![(43682492023709/100000000000000 : ℝ), (871423945293/6250000000000 : ℝ), (42374724841219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353724057/10000000000 : ℝ)|^4169 ≤ (43682492023709/100000000000000 : ℝ)^3145
        have hw : |(5353724057/10000000000 : ℝ)|=(5353724057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1131062117/5000000000 : ℝ)|^4169 ≤ (871423945293/6250000000000 : ℝ)^3145
        have hw : |(-1131062117/5000000000 : ℝ)|=(1131062117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2616181167/5000000000 : ℝ)|^4169 ≤ (42374724841219/100000000000000 : ℝ)^3145
        have hw : |(2616181167/5000000000 : ℝ)|=(2616181167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s3_2 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353724137/10000000000 : ℝ)*x 0 + (1046472481/2000000000 : ℝ)*x 1 + (-1131062017/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353724137/10000000000 : ℝ)^4169 ≤ (43682492888981/100000000000000 : ℝ)^3145 := by
    have hnat : (5353724137 : ℕ)^4169*100000000000000^3145 ≤ 43682492888981^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353724137 10000000000 43682492888981 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1046472481/2000000000 : ℝ)^4169 ≤ (10593681400859/25000000000000 : ℝ)^3145 := by
    have hnat : (1046472481 : ℕ)^4169*25000000000000^3145 ≤ 10593681400859^3145*2000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046472481 2000000000 10593681400859 25000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1131062017/5000000000 : ℝ)^4169 ≤ (3485695372651/25000000000000 : ℝ)^3145 := by
    have hnat : (1131062017 : ℕ)^4169*25000000000000^3145 ≤ 3485695372651^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131062017 5000000000 3485695372651 25000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353724137/10000000000 : ℝ), (1046472481/2000000000 : ℝ), (-1131062017/5000000000 : ℝ)] ![(43682492888981/100000000000000 : ℝ), (10593681400859/25000000000000 : ℝ), (3485695372651/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353724137/10000000000 : ℝ)|^4169 ≤ (43682492888981/100000000000000 : ℝ)^3145
        have hw : |(5353724137/10000000000 : ℝ)|=(5353724137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1046472481/2000000000 : ℝ)|^4169 ≤ (10593681400859/25000000000000 : ℝ)^3145
        have hw : |(1046472481/2000000000 : ℝ)|=(1046472481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1131062017/5000000000 : ℝ)|^4169 ≤ (3485695372651/25000000000000 : ℝ)^3145
        have hw : |(-1131062017/5000000000 : ℝ)|=(1131062017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s3_3 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4362011933/10000000000 : ℝ)*x 0 + (4170773643/10000000000 : ℝ)*x 1 + (1140489879/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362011933/10000000000 : ℝ)^4169 ≤ (6658865731709/20000000000000 : ℝ)^3145 := by
    have hnat : (4362011933 : ℕ)^4169*20000000000000^3145 ≤ 6658865731709^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362011933 10000000000 6658865731709 20000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4170773643/10000000000 : ℝ)^4169 ≤ (7843332200587/25000000000000 : ℝ)^3145 := by
    have hnat : (4170773643 : ℕ)^4169*25000000000000^3145 ≤ 7843332200587^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170773643 10000000000 7843332200587 25000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1140489879/2500000000 : ℝ)^4169 ≤ (706646850593/2000000000000 : ℝ)^3145 := by
    have hnat : (1140489879 : ℕ)^4169*2000000000000^3145 ≤ 706646850593^3145*2500000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1140489879 2500000000 706646850593 2000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362011933/10000000000 : ℝ), (4170773643/10000000000 : ℝ), (1140489879/2500000000 : ℝ)] ![(6658865731709/20000000000000 : ℝ), (7843332200587/25000000000000 : ℝ), (706646850593/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362011933/10000000000 : ℝ)|^4169 ≤ (6658865731709/20000000000000 : ℝ)^3145
        have hw : |(4362011933/10000000000 : ℝ)|=(4362011933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4170773643/10000000000 : ℝ)|^4169 ≤ (7843332200587/25000000000000 : ℝ)^3145
        have hw : |(4170773643/10000000000 : ℝ)|=(4170773643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1140489879/2500000000 : ℝ)|^4169 ≤ (706646850593/2000000000000 : ℝ)^3145
        have hw : |(1140489879/2500000000 : ℝ)|=(1140489879/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s3_4 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-21616983/100000000 : ℝ)*x 0 + (5233123569/10000000000 : ℝ)*x 1 + (542810943/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21616983/100000000 : ℝ)^4169 ≤ (3282062947317/25000000000000 : ℝ)^3145 := by
    have hnat : (21616983 : ℕ)^4169*25000000000000^3145 ≤ 3282062947317^3145*100000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21616983 100000000 3282062947317 25000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5233123569/10000000000 : ℝ)^4169 ≤ (42382897236411/100000000000000 : ℝ)^3145 := by
    have hnat : (5233123569 : ℕ)^4169*100000000000000^3145 ≤ 42382897236411^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5233123569 10000000000 42382897236411 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542810943/1000000000 : ℝ)^4169 ≤ (11122212742361/25000000000000 : ℝ)^3145 := by
    have hnat : (542810943 : ℕ)^4169*25000000000000^3145 ≤ 11122212742361^3145*1000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542810943 1000000000 11122212742361 25000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-21616983/100000000 : ℝ), (5233123569/10000000000 : ℝ), (542810943/1000000000 : ℝ)] ![(3282062947317/25000000000000 : ℝ), (42382897236411/100000000000000 : ℝ), (11122212742361/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-21616983/100000000 : ℝ)|^4169 ≤ (3282062947317/25000000000000 : ℝ)^3145
        have hw : |(-21616983/100000000 : ℝ)|=(21616983/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5233123569/10000000000 : ℝ)|^4169 ≤ (42382897236411/100000000000000 : ℝ)^3145
        have hw : |(5233123569/10000000000 : ℝ)|=(5233123569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(542810943/1000000000 : ℝ)|^4169 ≤ (11122212742361/25000000000000 : ℝ)^3145
        have hw : |(542810943/1000000000 : ℝ)|=(542810943/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s3_5 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5303927581/10000000000 : ℝ)*x 0 + (-1033188531/5000000000 : ℝ)*x 1 + (5428109541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303927581/10000000000 : ℝ)^4169 ≤ (43144715579079/100000000000000 : ℝ)^3145 := by
    have hnat : (5303927581 : ℕ)^4169*100000000000000^3145 ≤ 43144715579079^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303927581 10000000000 43144715579079 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1033188531/5000000000 : ℝ)^4169 ≤ (19322550361/156250000000 : ℝ)^3145 := by
    have hnat : (1033188531 : ℕ)^4169*156250000000^3145 ≤ 19322550361^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033188531 5000000000 19322550361 156250000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5428109541/10000000000 : ℝ)^4169 ≤ (8897770435083/20000000000000 : ℝ)^3145 := by
    have hnat : (5428109541 : ℕ)^4169*20000000000000^3145 ≤ 8897770435083^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428109541 10000000000 8897770435083 20000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303927581/10000000000 : ℝ), (-1033188531/5000000000 : ℝ), (5428109541/10000000000 : ℝ)] ![(43144715579079/100000000000000 : ℝ), (19322550361/156250000000 : ℝ), (8897770435083/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303927581/10000000000 : ℝ)|^4169 ≤ (43144715579079/100000000000000 : ℝ)^3145
        have hw : |(5303927581/10000000000 : ℝ)|=(5303927581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1033188531/5000000000 : ℝ)|^4169 ≤ (19322550361/156250000000 : ℝ)^3145
        have hw : |(-1033188531/5000000000 : ℝ)|=(1033188531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5428109541/10000000000 : ℝ)|^4169 ≤ (8897770435083/20000000000000 : ℝ)^3145
        have hw : |(5428109541/10000000000 : ℝ)|=(5428109541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s3_6 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5303927463/10000000000 : ℝ)*x 0 + (5428109733/10000000000 : ℝ)*x 1 + (-2066376959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303927463/10000000000 : ℝ)^4169 ≤ (1078617857667/2500000000000 : ℝ)^3145 := by
    have hnat : (5303927463 : ℕ)^4169*2500000000000^3145 ≤ 1078617857667^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303927463 10000000000 1078617857667 2500000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5428109733/10000000000 : ℝ)^4169 ≤ (44488854261419/100000000000000 : ℝ)^3145 := by
    have hnat : (5428109733 : ℕ)^4169*100000000000000^3145 ≤ 44488854261419^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428109733 10000000000 44488854261419 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2066376959/10000000000 : ℝ)^4169 ≤ (3091607853481/25000000000000 : ℝ)^3145 := by
    have hnat : (2066376959 : ℕ)^4169*25000000000000^3145 ≤ 3091607853481^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066376959 10000000000 3091607853481 25000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303927463/10000000000 : ℝ), (5428109733/10000000000 : ℝ), (-2066376959/10000000000 : ℝ)] ![(1078617857667/2500000000000 : ℝ), (44488854261419/100000000000000 : ℝ), (3091607853481/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303927463/10000000000 : ℝ)|^4169 ≤ (1078617857667/2500000000000 : ℝ)^3145
        have hw : |(5303927463/10000000000 : ℝ)|=(5303927463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5428109733/10000000000 : ℝ)|^4169 ≤ (44488854261419/100000000000000 : ℝ)^3145
        have hw : |(5428109733/10000000000 : ℝ)|=(5428109733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2066376959/10000000000 : ℝ)|^4169 ≤ (3091607853481/25000000000000 : ℝ)^3145
        have hw : |(-2066376959/10000000000 : ℝ)|=(2066376959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s3_7 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2181023823/5000000000 : ℝ)*x 0 + (2280222369/5000000000 : ℝ)*x 1 + (267027/640000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2181023823/5000000000 : ℝ)^4169 ≤ (33294690003147/100000000000000 : ℝ)^3145 := by
    have hnat : (2181023823 : ℕ)^4169*100000000000000^3145 ≤ 33294690003147^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181023823 5000000000 33294690003147 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2280222369/5000000000 : ℝ)^4169 ≤ (17658395774863/50000000000000 : ℝ)^3145 := by
    have hnat : (2280222369 : ℕ)^4169*50000000000000^3145 ≤ 17658395774863^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2280222369 5000000000 17658395774863 50000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (267027/640000 : ℝ)^4169 ≤ (7847129607251/25000000000000 : ℝ)^3145 := by
    have hnat : (267027 : ℕ)^4169*25000000000000^3145 ≤ 7847129607251^3145*640000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267027 640000 7847129607251 25000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2181023823/5000000000 : ℝ), (2280222369/5000000000 : ℝ), (267027/640000 : ℝ)] ![(33294690003147/100000000000000 : ℝ), (17658395774863/50000000000000 : ℝ), (7847129607251/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2181023823/5000000000 : ℝ)|^4169 ≤ (33294690003147/100000000000000 : ℝ)^3145
        have hw : |(2181023823/5000000000 : ℝ)|=(2181023823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2280222369/5000000000 : ℝ)|^4169 ≤ (17658395774863/50000000000000 : ℝ)^3145
        have hw : |(2280222369/5000000000 : ℝ)|=(2280222369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(267027/640000 : ℝ)|^4169 ≤ (7847129607251/25000000000000 : ℝ)^3145
        have hw : |(267027/640000 : ℝ)|=(267027/640000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1145_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29906449/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8247/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2271/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2661/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7401/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8247/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2271/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8247/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2271/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8247/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2271/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8247/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2271/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8247/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2271/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8247/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2271/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2271/25000 : ℝ) ^ (8337/2048 : ℝ) ≤ (5745842387731579/100000000000000000000 : ℝ) := by
    have hpowers : (2271/25000 : ℝ)^8337 ≤ (5745842387731579/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2271 : ℕ)^8337*100000000000000000000^2048 ≤ 5745842387731579^2048*25000^8337 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2271 25000 5745842387731579 100000000000000000000 8337 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2271/25000 : ℝ)) (X := (5745842387731579/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (8247/50000 : ℝ) ^ (8337/2048 : ℝ) ≤ (65146341201028967/100000000000000000000 : ℝ) := by
    have hpowers : (8247/50000 : ℝ)^8337 ≤ (65146341201028967/100000000000000000000 : ℝ)^2048 := by
      have hnat : (8247 : ℕ)^8337*100000000000000000000^2048 ≤ 65146341201028967^2048*50000^8337 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8247 50000 65146341201028967 100000000000000000000 8337 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8247/50000 : ℝ)) (X := (65146341201028967/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005745842387731579/50000000000000000000 : ℝ) ≤ (5000141141600079/5000000000000000 : ℝ) ^ (8337/2048 : ℝ) := by
    have hpowers : (50005745842387731579/50000000000000000000 : ℝ)^2048 ≤ (5000141141600079/5000000000000000 : ℝ)^8337 := by
      have hnat : (50005745842387731579 : ℕ)^2048*5000000000000000^8337 ≤ 5000141141600079^8337*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005745842387731579 50000000000000000000 5000141141600079 5000000000000000 2048 8337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000141141600079/5000000000000000 : ℝ)) (X := (50005745842387731579/50000000000000000000 : ℝ)) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50035446091794380273/50000000000000000000 : ℝ) ≤ (10001741014596623/10000000000000000 : ℝ) ^ (8337/2048 : ℝ) := by
    have hpowers : (50035446091794380273/50000000000000000000 : ℝ)^2048 ≤ (10001741014596623/10000000000000000 : ℝ)^8337 := by
      have hnat : (50035446091794380273 : ℕ)^2048*10000000000000000^8337 ≤ 10001741014596623^8337*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035446091794380273 50000000000000000000 10001741014596623 10000000000000000 2048 8337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001741014596623/10000000000000000 : ℝ)) (X := (50035446091794380273/50000000000000000000 : ℝ)) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50065146341201028967/50000000000000000000 : ℝ) ≤ (78149998015571/78125000000000 : ℝ) ^ (8337/2048 : ℝ) := by
    have hpowers : (50065146341201028967/50000000000000000000 : ℝ)^2048 ≤ (78149998015571/78125000000000 : ℝ)^8337 := by
      have hnat : (50065146341201028967 : ℕ)^2048*78125000000000^8337 ≤ 78149998015571^8337*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50065146341201028967 50000000000000000000 78149998015571 78125000000000 2048 8337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78149998015571/78125000000000 : ℝ)) (X := (50065146341201028967/50000000000000000000 : ℝ)) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5745842387731579/100000000000000000000 : ℝ) ≤ ((1234593158108369911/1235000000000000000 : ℝ)+2*(291746279293/148200000000000 : ℝ)*(2271/25000 : ℝ))^(8337/2048 : ℝ) := by
    rw [show (1234593158108369911/1235000000000000000 : ℝ)+2*(291746279293/148200000000000 : ℝ)*(2271/25000 : ℝ)=(5000141141600079/5000000000000000 : ℝ) by norm_num, show 1+2*(5745842387731579/100000000000000000000 : ℝ)=(50005745842387731579/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(65146341201028967/100000000000000000000 : ℝ)+(5745842387731579/100000000000000000000 : ℝ) ≤ ((1234593158108369911/1235000000000000000 : ℝ)+(291746279293/148200000000000 : ℝ)*((8247/50000 : ℝ)+(2271/25000 : ℝ)))^(8337/2048 : ℝ) := by
    rw [show (1234593158108369911/1235000000000000000 : ℝ)+(291746279293/148200000000000 : ℝ)*((8247/50000 : ℝ)+(2271/25000 : ℝ))=(10001741014596623/10000000000000000 : ℝ) by norm_num, show 1+(65146341201028967/100000000000000000000 : ℝ)+(5745842387731579/100000000000000000000 : ℝ)=(50035446091794380273/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(65146341201028967/100000000000000000000 : ℝ) ≤ ((1234593158108369911/1235000000000000000 : ℝ)+2*(291746279293/148200000000000 : ℝ)*(8247/50000 : ℝ))^(8337/2048 : ℝ) := by
    rw [show (1234593158108369911/1235000000000000000 : ℝ)+2*(291746279293/148200000000000 : ℝ)*(8247/50000 : ℝ)=(78149998015571/78125000000000 : ℝ) by norm_num, show 1+2*(65146341201028967/100000000000000000000 : ℝ)=(50065146341201028967/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1234593158108369911/1235000000000000000 : ℝ)*(X 1 0+X 2 0)+(291746279293/148200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8337/2048 : ℝ)) (lo := (2271/25000 : ℝ)) (hi := (8247/50000 : ℝ)) (c := (1234593158108369911/1235000000000000000 : ℝ)) (alpha := (291746279293/148200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1234593158108369911/1235000000000000000 : ℝ)*(X 0 1+X 2 1)+(291746279293/148200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8337/2048 : ℝ)) (lo := (2271/25000 : ℝ)) (hi := (8247/50000 : ℝ)) (c := (1234593158108369911/1235000000000000000 : ℝ)) (alpha := (291746279293/148200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1234593158108369911/1235000000000000000 : ℝ)*(X 0 2+X 1 2)+(291746279293/148200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8337/2048 : ℝ)) (lo := (2271/25000 : ℝ)) (hi := (8247/50000 : ℝ)) (c := (1234593158108369911/1235000000000000000 : ℝ)) (alpha := (291746279293/148200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2161680363/10000000000 : ℝ)*X 0 0+(5428874739/10000000000 : ℝ)*X 0 1+(5232362503/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353724057/10000000000 : ℝ)*X 1 0+(-1131062117/5000000000 : ℝ)*X 1 1+(2616181167/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353724137/10000000000 : ℝ)*X 2 0+(1046472481/2000000000 : ℝ)*X 2 1+(-1131062017/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4362011933/10000000000 : ℝ)*X 0 0+(4170773643/10000000000 : ℝ)*X 0 1+(1140489879/2500000000 : ℝ)*X 0 2+(4362011933/10000000000 : ℝ)*X 1 0+(4170773643/10000000000 : ℝ)*X 1 1+(1140489879/2500000000 : ℝ)*X 1 2+(4362011933/10000000000 : ℝ)*X 2 0+(4170773643/10000000000 : ℝ)*X 2 1+(1140489879/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-21616983/100000000 : ℝ)*X 0 0+(5233123569/10000000000 : ℝ)*X 0 1+(542810943/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5303927581/10000000000 : ℝ)*X 1 0+(-1033188531/5000000000 : ℝ)*X 1 1+(5428109541/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5303927463/10000000000 : ℝ)*X 2 0+(5428109733/10000000000 : ℝ)*X 2 1+(-2066376959/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2181023823/5000000000 : ℝ)*X 0 0+(2280222369/5000000000 : ℝ)*X 0 1+(267027/640000 : ℝ)*X 0 2+(2181023823/5000000000 : ℝ)*X 1 0+(2280222369/5000000000 : ℝ)*X 1 1+(267027/640000 : ℝ)*X 1 2+(2181023823/5000000000 : ℝ)*X 2 0+(2280222369/5000000000 : ℝ)*X 2 1+(267027/640000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (54457711997142908365802763/15437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1054619961/100000000000000 : ℝ)*(base19) + (1008694723/100000000000000 : ℝ)*(base23) + (13059461/20000000000000 : ℝ)*(lower2) + (20584131/100000000000000 : ℝ)*(upper3) + (154171007/100000000000000 : ℝ)*(upper5) + (1911280365682089/50000000000000 : ℝ)*(major0) + (1911280365682089/50000000000000 : ℝ)*(major1) + (1911280365682089/50000000000000 : ℝ)*(major2) + (5088755660363529/100000000000000 : ℝ)*(sp0) + (5088774847192467/100000000000000 : ℝ)*(sp1) + (1017754978623541/20000000000000 : ℝ)*(sp2) + (1278168999295117/50000000000000 : ℝ)*(sp3) + (202414489/1000000000000 : ℝ)*(sp4) + (7444738179/100000000000000 : ℝ)*(sp7) + (639086360832103/25000000000000 : ℝ)*(f.failure) + (5088775901812429/100000000000000 : ℝ)*(f.sum) + (987039049489/308750000000000000000000000 : ℝ)*base66 + (459852167056949079/61750000000000000000000000000000 : ℝ)*base67 + (364499986890199079/61750000000000000000000000000000 : ℝ)*base69 + (231639460458050921/61750000000000000000000000000000 : ℝ)*base72 + (2302522926149/1235000000000000000000000000 : ℝ)*base73 + (1195787262120949079/61750000000000000000000000000000 : ℝ)*base75 + (203483954391449079/61750000000000000000000000000000 : ℝ)*base77 + (618070333052449079/61750000000000000000000000000000 : ℝ)*base79 + (994381911703/617500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (4067753/500000000000000000000 : ℝ)*base90 + (4067753/500000000000000000000 : ℝ)*base92 + (4067753/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (76487807638116155637413979/15437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (966230913/100000000000000 : ℝ)*(base19) + (211670991/20000000000000 : ℝ)*(base23) + (28472521/20000000000000 : ℝ)*(upper3) + (77654567/100000000000000 : ℝ)*(lower4) + (5603163/6250000000000 : ℝ)*(upper5) + (1926227850980163/50000000000000 : ℝ)*(major0) + (1926227850980163/50000000000000 : ℝ)*(major1) + (1926227850980163/50000000000000 : ℝ)*(major2) + (18202801253/100000000000000 : ℝ)*(sp1) + (12286769103/50000000000000 : ℝ)*(sp2) + (5128573471642833/100000000000000 : ℝ)*(sp4) + (5128554302610667/100000000000000 : ℝ)*(sp5) + (641068479968709/12500000000000 : ℝ)*(sp6) + (80510555222561/3125000000000 : ℝ)*(sp7) + (80510555222561/3125000000000 : ℝ)*(f.failure) + (5128573471642833/100000000000000 : ℝ)*(f.sum) + (8427885860367/1235000000000000000000000000 : ℝ)*base66 + (326653664664349507/61750000000000000000000000000000 : ℝ)*base68 + (701006595249099507/61750000000000000000000000000000 : ℝ)*base70 + (923192959811599507/61750000000000000000000000000000 : ℝ)*base72 + (6806654341447/1235000000000000000000000000 : ℝ)*base74 + (258695245317349507/61750000000000000000000000000000 : ℝ)*base76 + (511812632629099507/61750000000000000000000000000000 : ℝ)*base78 + (90154387544900493/61750000000000000000000000000000 : ℝ)*base79 + (6824619303527/1235000000000000000000000000 : ℝ)*base82 + (445889/62500000000000000000 : ℝ)*base89 + (445889/62500000000000000000 : ℝ)*base91 + (445889/62500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1145_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29906449/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8247/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2271/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2661/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7401/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1145_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1145_s4_0 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1082330331/5000000000 : ℝ)*x 0 + (5401747599/10000000000 : ℝ)*x 1 + (1314384943/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082330331/5000000000 : ℝ)^4169 ≤ (657605280741/5000000000000 : ℝ)^3145 := by
    have hnat : (1082330331 : ℕ)^4169*5000000000000^3145 ≤ 657605280741^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082330331 5000000000 657605280741 5000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5401747599/10000000000 : ℝ)^4169 ≤ (884053336993/2000000000000 : ℝ)^3145 := by
    have hnat : (5401747599 : ℕ)^4169*2000000000000^3145 ≤ 884053336993^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401747599 10000000000 884053336993 2000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1314384943/2500000000 : ℝ)^4169 ≤ (5330653440061/12500000000000 : ℝ)^3145 := by
    have hnat : (1314384943 : ℕ)^4169*12500000000000^3145 ≤ 5330653440061^3145*2500000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314384943 2500000000 5330653440061 12500000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1082330331/5000000000 : ℝ), (5401747599/10000000000 : ℝ), (1314384943/2500000000 : ℝ)] ![(657605280741/5000000000000 : ℝ), (884053336993/2000000000000 : ℝ), (5330653440061/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1082330331/5000000000 : ℝ)|^4169 ≤ (657605280741/5000000000000 : ℝ)^3145
        have hw : |(-1082330331/5000000000 : ℝ)|=(1082330331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5401747599/10000000000 : ℝ)|^4169 ≤ (884053336993/2000000000000 : ℝ)^3145
        have hw : |(5401747599/10000000000 : ℝ)|=(5401747599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1314384943/2500000000 : ℝ)|^4169 ≤ (5330653440061/12500000000000 : ℝ)^3145
        have hw : |(1314384943/2500000000 : ℝ)|=(1314384943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s4_1 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346946613/10000000000 : ℝ)*x 0 + (-2237943631/10000000000 : ℝ)*x 1 + (657192557/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346946613/10000000000 : ℝ)^4169 ≤ (4360920297787/10000000000000 : ℝ)^3145 := by
    have hnat : (5346946613 : ℕ)^4169*10000000000000^3145 ≤ 4360920297787^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346946613 10000000000 4360920297787 10000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2237943631/10000000000 : ℝ)^4169 ≤ (343639053243/2500000000000 : ℝ)^3145 := by
    have hnat : (2237943631 : ℕ)^4169*2500000000000^3145 ≤ 343639053243^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237943631 10000000000 343639053243 2500000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (657192557/1250000000 : ℝ)^4169 ≤ (42645234875023/100000000000000 : ℝ)^3145 := by
    have hnat : (657192557 : ℕ)^4169*100000000000000^3145 ≤ 42645234875023^3145*1250000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657192557 1250000000 42645234875023 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346946613/10000000000 : ℝ), (-2237943631/10000000000 : ℝ), (657192557/1250000000 : ℝ)] ![(4360920297787/10000000000000 : ℝ), (343639053243/2500000000000 : ℝ), (42645234875023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346946613/10000000000 : ℝ)|^4169 ≤ (4360920297787/10000000000000 : ℝ)^3145
        have hw : |(5346946613/10000000000 : ℝ)|=(5346946613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2237943631/10000000000 : ℝ)|^4169 ≤ (343639053243/2500000000000 : ℝ)^3145
        have hw : |(-2237943631/10000000000 : ℝ)|=(2237943631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(657192557/1250000000 : ℝ)|^4169 ≤ (42645234875023/100000000000000 : ℝ)^3145
        have hw : |(657192557/1250000000 : ℝ)|=(657192557/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s4_2 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673473447/5000000000 : ℝ)*x 0 + (2628769817/5000000000 : ℝ)*x 1 + (-279743043/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673473447/5000000000 : ℝ)^4169 ≤ (10902301503971/25000000000000 : ℝ)^3145 := by
    have hnat : (2673473447 : ℕ)^4169*25000000000000^3145 ≤ 10902301503971^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673473447 5000000000 10902301503971 25000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2628769817/5000000000 : ℝ)^4169 ≤ (21322613018339/50000000000000 : ℝ)^3145 := by
    have hnat : (2628769817 : ℕ)^4169*50000000000000^3145 ≤ 21322613018339^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628769817 5000000000 21322613018339 50000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (279743043/1250000000 : ℝ)^4169 ≤ (13745567934879/100000000000000 : ℝ)^3145 := by
    have hnat : (279743043 : ℕ)^4169*100000000000000^3145 ≤ 13745567934879^3145*1250000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279743043 1250000000 13745567934879 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673473447/5000000000 : ℝ), (2628769817/5000000000 : ℝ), (-279743043/1250000000 : ℝ)] ![(10902301503971/25000000000000 : ℝ), (21322613018339/50000000000000 : ℝ), (13745567934879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673473447/5000000000 : ℝ)|^4169 ≤ (10902301503971/25000000000000 : ℝ)^3145
        have hw : |(2673473447/5000000000 : ℝ)|=(2673473447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2628769817/5000000000 : ℝ)|^4169 ≤ (21322613018339/50000000000000 : ℝ)^3145
        have hw : |(2628769817/5000000000 : ℝ)|=(2628769817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-279743043/1250000000 : ℝ)|^4169 ≤ (13745567934879/100000000000000 : ℝ)^3145
        have hw : |(-279743043/1250000000 : ℝ)|=(279743043/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s4_3 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1090947557/2500000000 : ℝ)*x 0 + (2111300811/5000000000 : ℝ)*x 1 + (4509670503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090947557/2500000000 : ℝ)^4169 ≤ (33312322640717/100000000000000 : ℝ)^3145 := by
    have hnat : (1090947557 : ℕ)^4169*100000000000000^3145 ≤ 33312322640717^3145*2500000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090947557 2500000000 33312322640717 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2111300811/5000000000 : ℝ)^4169 ≤ (31891167803011/100000000000000 : ℝ)^3145 := by
    have hnat : (2111300811 : ℕ)^4169*100000000000000^3145 ≤ 31891167803011^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111300811 5000000000 31891167803011 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4509670503/10000000000 : ℝ)^4169 ≤ (17398254770041/50000000000000 : ℝ)^3145 := by
    have hnat : (4509670503 : ℕ)^4169*50000000000000^3145 ≤ 17398254770041^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4509670503 10000000000 17398254770041 50000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1090947557/2500000000 : ℝ), (2111300811/5000000000 : ℝ), (4509670503/10000000000 : ℝ)] ![(33312322640717/100000000000000 : ℝ), (31891167803011/100000000000000 : ℝ), (17398254770041/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1090947557/2500000000 : ℝ)|^4169 ≤ (33312322640717/100000000000000 : ℝ)^3145
        have hw : |(1090947557/2500000000 : ℝ)|=(1090947557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2111300811/5000000000 : ℝ)|^4169 ≤ (31891167803011/100000000000000 : ℝ)^3145
        have hw : |(2111300811/5000000000 : ℝ)|=(2111300811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4509670503/10000000000 : ℝ)|^4169 ≤ (17398254770041/50000000000000 : ℝ)^3145
        have hw : |(4509670503/10000000000 : ℝ)|=(4509670503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s4_4 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-432933489/2000000000 : ℝ)*x 0 + (2628975239/5000000000 : ℝ)*x 1 + (5401335449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (432933489/2000000000 : ℝ)^4169 ≤ (13152160245769/100000000000000 : ℝ)^3145 := by
    have hnat : (432933489 : ℕ)^4169*100000000000000^3145 ≤ 13152160245769^3145*2000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432933489 2000000000 13152160245769 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2628975239/5000000000 : ℝ)^4169 ≤ (10662410896951/25000000000000 : ℝ)^3145 := by
    have hnat : (2628975239 : ℕ)^4169*25000000000000^3145 ≤ 10662410896951^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628975239 5000000000 10662410896951 25000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5401335449/10000000000 : ℝ)^4169 ≤ (5524774518949/12500000000000 : ℝ)^3145 := by
    have hnat : (5401335449 : ℕ)^4169*12500000000000^3145 ≤ 5524774518949^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401335449 10000000000 5524774518949 12500000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-432933489/2000000000 : ℝ), (2628975239/5000000000 : ℝ), (5401335449/10000000000 : ℝ)] ![(13152160245769/100000000000000 : ℝ), (10662410896951/25000000000000 : ℝ), (5524774518949/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-432933489/2000000000 : ℝ)|^4169 ≤ (13152160245769/100000000000000 : ℝ)^3145
        have hw : |(-432933489/2000000000 : ℝ)|=(432933489/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2628975239/5000000000 : ℝ)|^4169 ≤ (10662410896951/25000000000000 : ℝ)^3145
        have hw : |(2628975239/5000000000 : ℝ)|=(2628975239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5401335449/10000000000 : ℝ)|^4169 ≤ (5524774518949/12500000000000 : ℝ)^3145
        have hw : |(5401335449/10000000000 : ℝ)|=(5401335449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s4_5 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2655202671/5000000000 : ℝ)*x 0 + (-2094148203/10000000000 : ℝ)*x 1 + (5401335333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655202671/5000000000 : ℝ)^4169 ≤ (10803644856999/25000000000000 : ℝ)^3145 := by
    have hnat : (2655202671 : ℕ)^4169*25000000000000^3145 ≤ 10803644856999^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655202671 5000000000 10803644856999 25000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2094148203/10000000000 : ℝ)^4169 ≤ (2517445131361/20000000000000 : ℝ)^3145 := by
    have hnat : (2094148203 : ℕ)^4169*20000000000000^3145 ≤ 2517445131361^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2094148203 10000000000 2517445131361 20000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5401335333/10000000000 : ℝ)^4169 ≤ (22099097446663/50000000000000 : ℝ)^3145 := by
    have hnat : (5401335333 : ℕ)^4169*50000000000000^3145 ≤ 22099097446663^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401335333 10000000000 22099097446663 50000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655202671/5000000000 : ℝ), (-2094148203/10000000000 : ℝ), (5401335333/10000000000 : ℝ)] ![(10803644856999/25000000000000 : ℝ), (2517445131361/20000000000000 : ℝ), (22099097446663/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655202671/5000000000 : ℝ)|^4169 ≤ (10803644856999/25000000000000 : ℝ)^3145
        have hw : |(2655202671/5000000000 : ℝ)|=(2655202671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2094148203/10000000000 : ℝ)|^4169 ≤ (2517445131361/20000000000000 : ℝ)^3145
        have hw : |(-2094148203/10000000000 : ℝ)|=(2094148203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5401335333/10000000000 : ℝ)|^4169 ≤ (22099097446663/50000000000000 : ℝ)^3145
        have hw : |(5401335333/10000000000 : ℝ)|=(5401335333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s4_6 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5310405023/10000000000 : ℝ)*x 0 + (337583499/625000000 : ℝ)*x 1 + (-2094147749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310405023/10000000000 : ℝ)^4169 ≤ (43214575986839/100000000000000 : ℝ)^3145 := by
    have hnat : (5310405023 : ℕ)^4169*100000000000000^3145 ≤ 43214575986839^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310405023 10000000000 43214575986839 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337583499/625000000 : ℝ)^4169 ≤ (11049550488701/25000000000000 : ℝ)^3145 := by
    have hnat : (337583499 : ℕ)^4169*25000000000000^3145 ≤ 11049550488701^3145*625000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337583499 625000000 11049550488701 25000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2094147749/10000000000 : ℝ)^4169 ≤ (6293611019731/50000000000000 : ℝ)^3145 := by
    have hnat : (2094147749 : ℕ)^4169*50000000000000^3145 ≤ 6293611019731^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2094147749 10000000000 6293611019731 50000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310405023/10000000000 : ℝ), (337583499/625000000 : ℝ), (-2094147749/10000000000 : ℝ)] ![(43214575986839/100000000000000 : ℝ), (11049550488701/25000000000000 : ℝ), (6293611019731/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310405023/10000000000 : ℝ)|^4169 ≤ (43214575986839/100000000000000 : ℝ)^3145
        have hw : |(5310405023/10000000000 : ℝ)|=(5310405023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337583499/625000000 : ℝ)|^4169 ≤ (11049550488701/25000000000000 : ℝ)^3145
        have hw : |(337583499/625000000 : ℝ)|=(337583499/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2094147749/10000000000 : ℝ)|^4169 ≤ (6293611019731/50000000000000 : ℝ)^3145
        have hw : |(-2094147749/10000000000 : ℝ)|=(2094147749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s4_7 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4363803839/10000000000 : ℝ)*x 0 + (225442671/500000000 : ℝ)*x 1 + (4223422583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4363803839/10000000000 : ℝ)^4169 ≤ (33312460375157/100000000000000 : ℝ)^3145 := by
    have hnat : (4363803839 : ℕ)^4169*100000000000000^3145 ≤ 33312460375157^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363803839 10000000000 33312460375157 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (225442671/500000000 : ℝ)^4169 ≤ (1739407622119/5000000000000 : ℝ)^3145 := by
    have hnat : (225442671 : ℕ)^4169*5000000000000^3145 ≤ 1739407622119^3145*500000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225442671 500000000 1739407622119 5000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4223422583/10000000000 : ℝ)^4169 ≤ (31899387159733/100000000000000 : ℝ)^3145 := by
    have hnat : (4223422583 : ℕ)^4169*100000000000000^3145 ≤ 31899387159733^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4223422583 10000000000 31899387159733 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4363803839/10000000000 : ℝ), (225442671/500000000 : ℝ), (4223422583/10000000000 : ℝ)] ![(33312460375157/100000000000000 : ℝ), (1739407622119/5000000000000 : ℝ), (31899387159733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4363803839/10000000000 : ℝ)|^4169 ≤ (33312460375157/100000000000000 : ℝ)^3145
        have hw : |(4363803839/10000000000 : ℝ)|=(4363803839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(225442671/500000000 : ℝ)|^4169 ≤ (1739407622119/5000000000000 : ℝ)^3145
        have hw : |(225442671/500000000 : ℝ)|=(225442671/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4223422583/10000000000 : ℝ)|^4169 ≤ (31899387159733/100000000000000 : ℝ)^3145
        have hw : |(4223422583/10000000000 : ℝ)|=(4223422583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1145_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29906449/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7401/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2661/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11181/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7401/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2661/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7401/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2661/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7401/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2661/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7401/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2661/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7401/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2661/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7401/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2661/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2661/25000 : ℝ) ^ (8337/2048 : ℝ) ≤ (684569814339409/6250000000000000000 : ℝ) := by
    have hpowers : (2661/25000 : ℝ)^8337 ≤ (684569814339409/6250000000000000000 : ℝ)^2048 := by
      have hnat : (2661 : ℕ)^8337*6250000000000000000^2048 ≤ 684569814339409^2048*25000^8337 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2661 25000 684569814339409 6250000000000000000 8337 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2661/25000 : ℝ)) (X := (684569814339409/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7401/50000 : ℝ) ^ (8337/2048 : ℝ) ≤ (163794634138817/390625000000000000 : ℝ) := by
    have hpowers : (7401/50000 : ℝ)^8337 ≤ (163794634138817/390625000000000000 : ℝ)^2048 := by
      have hnat : (7401 : ℕ)^8337*390625000000000000^2048 ≤ 163794634138817^2048*50000^8337 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7401 50000 163794634138817 390625000000000000 8337 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7401/50000 : ℝ)) (X := (163794634138817/390625000000000000 : ℝ)) (by norm_num) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125684569814339409/3125000000000000000 : ℝ) ≤ (20001076172747/20000000000000 : ℝ) ^ (8337/2048 : ℝ) := by
    have hpowers : (3125684569814339409/3125000000000000000 : ℝ)^2048 ≤ (20001076172747/20000000000000 : ℝ)^8337 := by
      have hnat : (3125684569814339409 : ℕ)^2048*20000000000000^8337 ≤ 20001076172747^8337*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125684569814339409 3125000000000000000 20001076172747 20000000000000 2048 8337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (20001076172747/20000000000000 : ℝ)) (X := (3125684569814339409/3125000000000000000 : ℝ)) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (6253305283960560481/6250000000000000000 : ℝ) ≤ (5000649429937281/5000000000000000 : ℝ) ^ (8337/2048 : ℝ) := by
    have hpowers : (6253305283960560481/6250000000000000000 : ℝ)^2048 ≤ (5000649429937281/5000000000000000 : ℝ)^8337 := by
      have hnat : (6253305283960560481 : ℕ)^2048*5000000000000000^8337 ≤ 5000649429937281^8337*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253305283960560481 6250000000000000000 5000649429937281 5000000000000000 2048 8337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000649429937281/5000000000000000 : ℝ)) (X := (6253305283960560481/6250000000000000000 : ℝ)) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (195476294634138817/195312500000000000 : ℝ) ≤ (1250257454171953/1250000000000000 : ℝ) ^ (8337/2048 : ℝ) := by
    have hpowers : (195476294634138817/195312500000000000 : ℝ)^2048 ≤ (1250257454171953/1250000000000000 : ℝ)^8337 := by
      have hnat : (195476294634138817 : ℕ)^2048*1250000000000000^8337 ≤ 1250257454171953^8337*195312500000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        195476294634138817 195312500000000000 1250257454171953 1250000000000000 2048 8337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250257454171953/1250000000000000 : ℝ)) (X := (195476294634138817/195312500000000000 : ℝ)) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(684569814339409/6250000000000000000 : ℝ) ≤ ((1731918417368766881/1732500000000000000 : ℝ)+2*(380386750531/207900000000000 : ℝ)*(2661/25000 : ℝ))^(8337/2048 : ℝ) := by
    rw [show (1731918417368766881/1732500000000000000 : ℝ)+2*(380386750531/207900000000000 : ℝ)*(2661/25000 : ℝ)=(20001076172747/20000000000000 : ℝ) by norm_num, show 1+2*(684569814339409/6250000000000000000 : ℝ)=(3125684569814339409/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(163794634138817/390625000000000000 : ℝ)+(684569814339409/6250000000000000000 : ℝ) ≤ ((1731918417368766881/1732500000000000000 : ℝ)+(380386750531/207900000000000 : ℝ)*((7401/50000 : ℝ)+(2661/25000 : ℝ)))^(8337/2048 : ℝ) := by
    rw [show (1731918417368766881/1732500000000000000 : ℝ)+(380386750531/207900000000000 : ℝ)*((7401/50000 : ℝ)+(2661/25000 : ℝ))=(5000649429937281/5000000000000000 : ℝ) by norm_num, show 1+(163794634138817/390625000000000000 : ℝ)+(684569814339409/6250000000000000000 : ℝ)=(6253305283960560481/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(163794634138817/390625000000000000 : ℝ) ≤ ((1731918417368766881/1732500000000000000 : ℝ)+2*(380386750531/207900000000000 : ℝ)*(7401/50000 : ℝ))^(8337/2048 : ℝ) := by
    rw [show (1731918417368766881/1732500000000000000 : ℝ)+2*(380386750531/207900000000000 : ℝ)*(7401/50000 : ℝ)=(1250257454171953/1250000000000000 : ℝ) by norm_num, show 1+2*(163794634138817/390625000000000000 : ℝ)=(195476294634138817/195312500000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1731918417368766881/1732500000000000000 : ℝ)*(X 1 0+X 2 0)+(380386750531/207900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8337/2048 : ℝ)) (lo := (2661/25000 : ℝ)) (hi := (7401/50000 : ℝ)) (c := (1731918417368766881/1732500000000000000 : ℝ)) (alpha := (380386750531/207900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1731918417368766881/1732500000000000000 : ℝ)*(X 0 1+X 2 1)+(380386750531/207900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8337/2048 : ℝ)) (lo := (2661/25000 : ℝ)) (hi := (7401/50000 : ℝ)) (c := (1731918417368766881/1732500000000000000 : ℝ)) (alpha := (380386750531/207900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1731918417368766881/1732500000000000000 : ℝ)*(X 0 2+X 1 2)+(380386750531/207900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8337/2048 : ℝ)) (lo := (2661/25000 : ℝ)) (hi := (7401/50000 : ℝ)) (c := (1731918417368766881/1732500000000000000 : ℝ)) (alpha := (380386750531/207900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1082330331/5000000000 : ℝ)*X 0 0+(5401747599/10000000000 : ℝ)*X 0 1+(1314384943/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346946613/10000000000 : ℝ)*X 1 0+(-2237943631/10000000000 : ℝ)*X 1 1+(657192557/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673473447/5000000000 : ℝ)*X 2 0+(2628769817/5000000000 : ℝ)*X 2 1+(-279743043/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1090947557/2500000000 : ℝ)*X 0 0+(2111300811/5000000000 : ℝ)*X 0 1+(4509670503/10000000000 : ℝ)*X 0 2+(1090947557/2500000000 : ℝ)*X 1 0+(2111300811/5000000000 : ℝ)*X 1 1+(4509670503/10000000000 : ℝ)*X 1 2+(1090947557/2500000000 : ℝ)*X 2 0+(2111300811/5000000000 : ℝ)*X 2 1+(4509670503/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-432933489/2000000000 : ℝ)*X 0 0+(2628975239/5000000000 : ℝ)*X 0 1+(5401335449/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655202671/5000000000 : ℝ)*X 1 0+(-2094148203/10000000000 : ℝ)*X 1 1+(5401335333/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310405023/10000000000 : ℝ)*X 2 0+(337583499/625000000 : ℝ)*X 2 1+(-2094147749/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4363803839/10000000000 : ℝ)*X 0 0+(225442671/500000000 : ℝ)*X 0 1+(4223422583/10000000000 : ℝ)*X 0 2+(4363803839/10000000000 : ℝ)*X 1 0+(225442671/500000000 : ℝ)*X 1 1+(4223422583/10000000000 : ℝ)*X 1 2+(4363803839/10000000000 : ℝ)*X 2 0+(225442671/500000000 : ℝ)*X 2 1+(4223422583/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (254010839172437360912488577/21656250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (41100963/12500000000000 : ℝ)*(base23) + (164283157/100000000000000 : ℝ)*(lower2) + (118579147/25000000000000 : ℝ)*(upper3) + (207661259/100000000000000 : ℝ)*(lower4) + (32787663/50000000000000 : ℝ)*(upper5) + (1302246809725789/25000000000000 : ℝ)*(major0) + (1302246809725789/25000000000000 : ℝ)*(major1) + (1302246809725789/25000000000000 : ℝ)*(major2) + (433403314476403/6250000000000 : ℝ)*(sp0) + (433403314476403/6250000000000 : ℝ)*(sp1) + (3467217809903651/50000000000000 : ℝ)*(sp2) + (3483498650415841/100000000000000 : ℝ)*(sp3) + (17083007443/100000000000000 : ℝ)*(sp6) + (1400299633/6250000000000 : ℝ)*(sp7) + (217720065950623/6250000000000 : ℝ)*(f.failure) + (433403314476403/6250000000000 : ℝ)*(f.sum) + (11589634056059/649687500000000000000000000 : ℝ)*base66 + (331992871558267673/129937500000000000000000000000000 : ℝ)*base68 + (36572470764794827/129937500000000000000000000000000 : ℝ)*base69 + (8800034500961392673/129937500000000000000000000000000 : ℝ)*base72 + (3684233258947/5197500000000000000000000000 : ℝ)*base74 + (864306254256794827/129937500000000000000000000000000 : ℝ)*base75 + (1176944093004330173/129937500000000000000000000000000 : ℝ)*base78 + (2016610993071517673/129937500000000000000000000000000 : ℝ)*base80 + (10627850687449/2598750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1732273/125000000000000000000 : ℝ)*base90 + (1732273/125000000000000000000 : ℝ)*base92 + (1732273/125000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7941325273226682333457/693000000000000000000000000 : ℝ) := by norm_num
    linear_combination (83826873/20000000000000 : ℝ)*(base19) + (13901307/20000000000000 : ℝ)*(base23) + (226838033/100000000000000 : ℝ)*(lower2) + (111844823/100000000000000 : ℝ)*(upper3) + (11422367/6250000000000 : ℝ)*(lower4) + (1047772674077869/20000000000000 : ℝ)*(major0) + (1047772674077869/20000000000000 : ℝ)*(major1) + (1047772674077869/20000000000000 : ℝ)*(major2) + (885465393/4000000000000 : ℝ)*(sp2) + (5930791117/50000000000000 : ℝ)*(sp3) + (6974225578491033/100000000000000 : ℝ)*(sp4) + (1743556289839167/25000000000000 : ℝ)*(sp5) + (871775421543709/12500000000000 : ℝ)*(sp6) + (437936114840911/12500000000000 : ℝ)*(sp7) + (3503500780309521/100000000000000 : ℝ)*(f.failure) + (6974225578491033/100000000000000 : ℝ)*(f.sum) + (198745368091/1039500000000000000000000000 : ℝ)*base66 + (194706816346155233/103950000000000000000000000000000 : ℝ)*base68 + (570162986246894767/103950000000000000000000000000000 : ℝ)*base69 + (883273295970255233/103950000000000000000000000000000 : ℝ)*base72 + (4630529340977/2079000000000000000000000000 : ℝ)*base74 + (783674038120244767/103950000000000000000000000000000 : ℝ)*base75 + (635525679892755233/103950000000000000000000000000000 : ℝ)*base78 + (1224700545534044767/103950000000000000000000000000000 : ℝ)*base79 + (10584258824677/2079000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (5999071/2000000000000000000000 : ℝ)*base90 + (5999071/2000000000000000000000 : ℝ)*base92 + (5999071/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1145_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29906449/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7401/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2661/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11181/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1145_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1145_s5_0 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-270661441/1250000000 : ℝ)*x 0 + (1078967181/2000000000 : ℝ)*x 1 + (5264037291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270661441/1250000000 : ℝ)^4169 ≤ (1315718691011/10000000000000 : ℝ)^3145 := by
    have hnat : (270661441 : ℕ)^4169*10000000000000^3145 ≤ 1315718691011^3145*1250000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270661441 1250000000 1315718691011 10000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078967181/2000000000 : ℝ)^4169 ≤ (22063854300479/50000000000000 : ℝ)^3145 := by
    have hnat : (1078967181 : ℕ)^4169*50000000000000^3145 ≤ 22063854300479^3145*2000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078967181 2000000000 22063854300479 50000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264037291/10000000000 : ℝ)^4169 ≤ (42715104482757/100000000000000 : ℝ)^3145 := by
    have hnat : (5264037291 : ℕ)^4169*100000000000000^3145 ≤ 42715104482757^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264037291 10000000000 42715104482757 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-270661441/1250000000 : ℝ), (1078967181/2000000000 : ℝ), (5264037291/10000000000 : ℝ)] ![(1315718691011/10000000000000 : ℝ), (22063854300479/50000000000000 : ℝ), (42715104482757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-270661441/1250000000 : ℝ)|^4169 ≤ (1315718691011/10000000000000 : ℝ)^3145
        have hw : |(-270661441/1250000000 : ℝ)|=(270661441/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078967181/2000000000 : ℝ)|^4169 ≤ (22063854300479/50000000000000 : ℝ)^3145
        have hw : |(1078967181/2000000000 : ℝ)|=(1078967181/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264037291/10000000000 : ℝ)|^4169 ≤ (42715104482757/100000000000000 : ℝ)^3145
        have hw : |(5264037291/10000000000 : ℝ)|=(5264037291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s5_1 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345213353/10000000000 : ℝ)*x 0 + (-278957577/1250000000 : ℝ)*x 1 + (2632018673/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345213353/10000000000 : ℝ)^4169 ≤ (43590464930163/100000000000000 : ℝ)^3145 := by
    have hnat : (5345213353 : ℕ)^4169*100000000000000^3145 ≤ 43590464930163^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345213353 10000000000 43590464930163 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (278957577/1250000000 : ℝ)^4169 ≤ (684721499091/5000000000000 : ℝ)^3145 := by
    have hnat : (278957577 : ℕ)^4169*5000000000000^3145 ≤ 684721499091^3145*1250000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278957577 1250000000 684721499091 5000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632018673/5000000000 : ℝ)^4169 ≤ (42715105074369/100000000000000 : ℝ)^3145 := by
    have hnat : (2632018673 : ℕ)^4169*100000000000000^3145 ≤ 42715105074369^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632018673 5000000000 42715105074369 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345213353/10000000000 : ℝ), (-278957577/1250000000 : ℝ), (2632018673/5000000000 : ℝ)] ![(43590464930163/100000000000000 : ℝ), (684721499091/5000000000000 : ℝ), (42715105074369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345213353/10000000000 : ℝ)|^4169 ≤ (43590464930163/100000000000000 : ℝ)^3145
        have hw : |(5345213353/10000000000 : ℝ)|=(5345213353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-278957577/1250000000 : ℝ)|^4169 ≤ (684721499091/5000000000000 : ℝ)^3145
        have hw : |(-278957577/1250000000 : ℝ)|=(278957577/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632018673/5000000000 : ℝ)|^4169 ≤ (42715105074369/100000000000000 : ℝ)^3145
        have hw : |(2632018673/5000000000 : ℝ)|=(2632018673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s5_2 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345213233/10000000000 : ℝ)*x 0 + (2632018747/5000000000 : ℝ)*x 1 + (-2231660581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345213233/10000000000 : ℝ)^4169 ≤ (43590463632927/100000000000000 : ℝ)^3145 := by
    have hnat : (5345213233 : ℕ)^4169*100000000000000^3145 ≤ 43590463632927^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345213233 10000000000 43590463632927 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632018747/5000000000 : ℝ)^4169 ≤ (42715106666341/100000000000000 : ℝ)^3145 := by
    have hnat : (2632018747 : ℕ)^4169*100000000000000^3145 ≤ 42715106666341^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632018747 5000000000 42715106666341 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2231660581/10000000000 : ℝ)^4169 ≤ (2738885939423/20000000000000 : ℝ)^3145 := by
    have hnat : (2231660581 : ℕ)^4169*20000000000000^3145 ≤ 2738885939423^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2231660581 10000000000 2738885939423 20000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345213233/10000000000 : ℝ), (2632018747/5000000000 : ℝ), (-2231660581/10000000000 : ℝ)] ![(43590463632927/100000000000000 : ℝ), (42715106666341/100000000000000 : ℝ), (2738885939423/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345213233/10000000000 : ℝ)|^4169 ≤ (43590463632927/100000000000000 : ℝ)^3145
        have hw : |(5345213233/10000000000 : ℝ)|=(5345213233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632018747/5000000000 : ℝ)|^4169 ≤ (42715106666341/100000000000000 : ℝ)^3145
        have hw : |(2632018747/5000000000 : ℝ)|=(2632018747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2231660581/10000000000 : ℝ)|^4169 ≤ (2738885939423/20000000000000 : ℝ)^3145
        have hw : |(-2231660581/10000000000 : ℝ)|=(2231660581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s5_3 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (21820789/50000000 : ℝ)*x 0 + (529487751/1250000000 : ℝ)*x 1 + (2248137553/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21820789/50000000 : ℝ)^4169 ≤ (2082252642417/6250000000000 : ℝ)^3145 := by
    have hnat : (21820789 : ℕ)^4169*6250000000000^3145 ≤ 2082252642417^3145*50000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21820789 50000000 2082252642417 6250000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (529487751/1250000000 : ℝ)^4169 ≤ (1000762299619/3125000000000 : ℝ)^3145 := by
    have hnat : (529487751 : ℕ)^4169*3125000000000^3145 ≤ 1000762299619^3145*1250000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529487751 1250000000 1000762299619 3125000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2248137553/5000000000 : ℝ)^4169 ≤ (17329782061737/50000000000000 : ℝ)^3145 := by
    have hnat : (2248137553 : ℕ)^4169*50000000000000^3145 ≤ 17329782061737^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248137553 5000000000 17329782061737 50000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21820789/50000000 : ℝ), (529487751/1250000000 : ℝ), (2248137553/5000000000 : ℝ)] ![(2082252642417/6250000000000 : ℝ), (1000762299619/3125000000000 : ℝ), (17329782061737/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21820789/50000000 : ℝ)|^4169 ≤ (2082252642417/6250000000000 : ℝ)^3145
        have hw : |(21820789/50000000 : ℝ)|=(21820789/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(529487751/1250000000 : ℝ)|^4169 ≤ (1000762299619/3125000000000 : ℝ)^3145
        have hw : |(529487751/1250000000 : ℝ)|=(529487751/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2248137553/5000000000 : ℝ)|^4169 ≤ (17329782061737/50000000000000 : ℝ)^3145
        have hw : |(2248137553/5000000000 : ℝ)|=(2248137553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s5_4 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1082648273/5000000000 : ℝ)*x 0 + (1316093943/2500000000 : ℝ)*x 1 + (5394496383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082648273/5000000000 : ℝ)^4169 ≤ (2631445465881/20000000000000 : ℝ)^3145 := by
    have hnat : (1082648273 : ℕ)^4169*20000000000000^3145 ≤ 2631445465881^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082648273 5000000000 2631445465881 20000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316093943/2500000000 : ℝ)^4169 ≤ (42718745415049/100000000000000 : ℝ)^3145 := by
    have hnat : (1316093943 : ℕ)^4169*100000000000000^3145 ≤ 42718745415049^3145*2500000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316093943 2500000000 42718745415049 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394496383/10000000000 : ℝ)^4169 ≤ (44124027244651/100000000000000 : ℝ)^3145 := by
    have hnat : (5394496383 : ℕ)^4169*100000000000000^3145 ≤ 44124027244651^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394496383 10000000000 44124027244651 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1082648273/5000000000 : ℝ), (1316093943/2500000000 : ℝ), (5394496383/10000000000 : ℝ)] ![(2631445465881/20000000000000 : ℝ), (42718745415049/100000000000000 : ℝ), (44124027244651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1082648273/5000000000 : ℝ)|^4169 ≤ (2631445465881/20000000000000 : ℝ)^3145
        have hw : |(-1082648273/5000000000 : ℝ)|=(1082648273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316093943/2500000000 : ℝ)|^4169 ≤ (42718745415049/100000000000000 : ℝ)^3145
        have hw : |(1316093943/2500000000 : ℝ)|=(1316093943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394496383/10000000000 : ℝ)|^4169 ≤ (44124027244651/100000000000000 : ℝ)^3145
        have hw : |(5394496383/10000000000 : ℝ)|=(5394496383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s5_5 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656034277/5000000000 : ℝ)*x 0 + (-210120079/1000000000 : ℝ)*x 1 + (2697248253/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656034277/5000000000 : ℝ)^4169 ≤ (43232521955293/100000000000000 : ℝ)^3145 := by
    have hnat : (2656034277 : ℕ)^4169*100000000000000^3145 ≤ 43232521955293^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656034277 5000000000 43232521955293 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210120079/1000000000 : ℝ)^4169 ≤ (12643449452981/100000000000000 : ℝ)^3145 := by
    have hnat : (210120079 : ℕ)^4169*100000000000000^3145 ≤ 12643449452981^3145*1000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210120079 1000000000 12643449452981 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697248253/5000000000 : ℝ)^4169 ≤ (44124028578297/100000000000000 : ℝ)^3145 := by
    have hnat : (2697248253 : ℕ)^4169*100000000000000^3145 ≤ 44124028578297^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697248253 5000000000 44124028578297 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656034277/5000000000 : ℝ), (-210120079/1000000000 : ℝ), (2697248253/5000000000 : ℝ)] ![(43232521955293/100000000000000 : ℝ), (12643449452981/100000000000000 : ℝ), (44124028578297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656034277/5000000000 : ℝ)|^4169 ≤ (43232521955293/100000000000000 : ℝ)^3145
        have hw : |(2656034277/5000000000 : ℝ)|=(2656034277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-210120079/1000000000 : ℝ)|^4169 ≤ (12643449452981/100000000000000 : ℝ)^3145
        have hw : |(-210120079/1000000000 : ℝ)|=(210120079/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697248253/5000000000 : ℝ)|^4169 ≤ (44124028578297/100000000000000 : ℝ)^3145
        have hw : |(2697248253/5000000000 : ℝ)|=(2697248253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s5_6 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656033989/5000000000 : ℝ)*x 0 + (674312111/1250000000 : ℝ)*x 1 + (-42024021/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656033989/5000000000 : ℝ)^4169 ≤ (43232515741159/100000000000000 : ℝ)^3145 := by
    have hnat : (2656033989 : ℕ)^4169*100000000000000^3145 ≤ 43232515741159^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656033989 5000000000 43232515741159 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674312111/1250000000 : ℝ)^4169 ≤ (44124032720189/100000000000000 : ℝ)^3145 := by
    have hnat : (674312111 : ℕ)^4169*100000000000000^3145 ≤ 44124032720189^3145*1250000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674312111 1250000000 44124032720189 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42024021/200000000 : ℝ)^4169 ≤ (12643451526857/100000000000000 : ℝ)^3145 := by
    have hnat : (42024021 : ℕ)^4169*100000000000000^3145 ≤ 12643451526857^3145*200000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42024021 200000000 12643451526857 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656033989/5000000000 : ℝ), (674312111/1250000000 : ℝ), (-42024021/200000000 : ℝ)] ![(43232515741159/100000000000000 : ℝ), (44124032720189/100000000000000 : ℝ), (12643451526857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656033989/5000000000 : ℝ)|^4169 ≤ (43232515741159/100000000000000 : ℝ)^3145
        have hw : |(2656033989/5000000000 : ℝ)|=(2656033989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674312111/1250000000 : ℝ)|^4169 ≤ (44124032720189/100000000000000 : ℝ)^3145
        have hw : |(674312111/1250000000 : ℝ)|=(674312111/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-42024021/200000000 : ℝ)|^4169 ≤ (12643451526857/100000000000000 : ℝ)^3145
        have hw : |(-42024021/200000000 : ℝ)|=(42024021/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s5_7 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1091042159/2500000000 : ℝ)*x 0 + (1123900523/2500000000 : ℝ)*x 1 + (847315449/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1091042159/2500000000 : ℝ)^4169 ≤ (33316151934919/100000000000000 : ℝ)^3145 := by
    have hnat : (1091042159 : ℕ)^4169*100000000000000^3145 ≤ 33316151934919^3145*2500000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091042159 2500000000 33316151934919 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1123900523/2500000000 : ℝ)^4169 ≤ (34652687187493/100000000000000 : ℝ)^3145 := by
    have hnat : (1123900523 : ℕ)^4169*100000000000000^3145 ≤ 34652687187493^3145*2500000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123900523 2500000000 34652687187493 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (847315449/2000000000 : ℝ)^4169 ≤ (16015580430873/50000000000000 : ℝ)^3145 := by
    have hnat : (847315449 : ℕ)^4169*50000000000000^3145 ≤ 16015580430873^3145*2000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847315449 2000000000 16015580430873 50000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1091042159/2500000000 : ℝ), (1123900523/2500000000 : ℝ), (847315449/2000000000 : ℝ)] ![(33316151934919/100000000000000 : ℝ), (34652687187493/100000000000000 : ℝ), (16015580430873/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1091042159/2500000000 : ℝ)|^4169 ≤ (33316151934919/100000000000000 : ℝ)^3145
        have hw : |(1091042159/2500000000 : ℝ)|=(1091042159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1123900523/2500000000 : ℝ)|^4169 ≤ (34652687187493/100000000000000 : ℝ)^3145
        have hw : |(1123900523/2500000000 : ℝ)|=(1123900523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(847315449/2000000000 : ℝ)|^4169 ≤ (16015580430873/50000000000000 : ℝ)^3145
        have hw : |(847315449/2000000000 : ℝ)|=(847315449/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1145_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29906449/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11181/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (283/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1409/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11181/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11181/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11181/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11181/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11181/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11181/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11181/100000 : ℝ) ^ (8337/2048 : ℝ) ≤ (13383024603095111/100000000000000000000 : ℝ) := by
    have hpowers : (11181/100000 : ℝ)^8337 ≤ (13383024603095111/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11181 : ℕ)^8337*100000000000000000000^2048 ≤ 13383024603095111^2048*100000^8337 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11181 100000 13383024603095111 100000000000000000000 8337 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11181/100000 : ℝ)) (X := (13383024603095111/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (8337/2048 : ℝ) ≤ (17883681958157837/50000000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^8337 ≤ (17883681958157837/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2847 : ℕ)^8337*50000000000000000000^2048 ≤ 17883681958157837^2048*20000^8337 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 17883681958157837 50000000000000000000 8337 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (17883681958157837/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013383024603095111/50000000000000000000 : ℝ) ≤ (500032872337547/500000000000000 : ℝ) ^ (8337/2048 : ℝ) := by
    have hpowers : (50013383024603095111/50000000000000000000 : ℝ)^2048 ≤ (500032872337547/500000000000000 : ℝ)^8337 := by
      have hnat : (50013383024603095111 : ℕ)^2048*500000000000000^8337 ≤ 500032872337547^8337*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013383024603095111 50000000000000000000 500032872337547 500000000000000 2048 8337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500032872337547/500000000000000 : ℝ)) (X := (50013383024603095111/50000000000000000000 : ℝ)) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009830077703882157/20000000000000000000 : ℝ) ≤ (5000603582466397/5000000000000000 : ℝ) ^ (8337/2048 : ℝ) := by
    have hpowers : (20009830077703882157/20000000000000000000 : ℝ)^2048 ≤ (5000603582466397/5000000000000000 : ℝ)^8337 := by
      have hnat : (20009830077703882157 : ℕ)^2048*5000000000000000^8337 ≤ 5000603582466397^8337*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009830077703882157 20000000000000000000 5000603582466397 5000000000000000 2048 8337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000603582466397/5000000000000000 : ℝ)) (X := (20009830077703882157/20000000000000000000 : ℝ)) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017883681958157837/25000000000000000000 : ℝ) ≤ (1250219610389331/1250000000000000 : ℝ) ^ (8337/2048 : ℝ) := by
    have hpowers : (25017883681958157837/25000000000000000000 : ℝ)^2048 ≤ (1250219610389331/1250000000000000 : ℝ)^8337 := by
      have hnat : (25017883681958157837 : ℕ)^2048*1250000000000000^8337 ≤ 1250219610389331^8337*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017883681958157837 25000000000000000000 1250219610389331 1250000000000000 2048 8337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250219610389331/1250000000000000 : ℝ)) (X := (25017883681958157837/25000000000000000000 : ℝ)) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13383024603095111/100000000000000000000 : ℝ) ≤ ((2544142920366229301/2545000000000000000 : ℝ)+2*(274859090927/152700000000000 : ℝ)*(11181/100000 : ℝ))^(8337/2048 : ℝ) := by
    rw [show (2544142920366229301/2545000000000000000 : ℝ)+2*(274859090927/152700000000000 : ℝ)*(11181/100000 : ℝ)=(500032872337547/500000000000000 : ℝ) by norm_num, show 1+2*(13383024603095111/100000000000000000000 : ℝ)=(50013383024603095111/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17883681958157837/50000000000000000000 : ℝ)+(13383024603095111/100000000000000000000 : ℝ) ≤ ((2544142920366229301/2545000000000000000 : ℝ)+(274859090927/152700000000000 : ℝ)*((2847/20000 : ℝ)+(11181/100000 : ℝ)))^(8337/2048 : ℝ) := by
    rw [show (2544142920366229301/2545000000000000000 : ℝ)+(274859090927/152700000000000 : ℝ)*((2847/20000 : ℝ)+(11181/100000 : ℝ))=(5000603582466397/5000000000000000 : ℝ) by norm_num, show 1+(17883681958157837/50000000000000000000 : ℝ)+(13383024603095111/100000000000000000000 : ℝ)=(20009830077703882157/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17883681958157837/50000000000000000000 : ℝ) ≤ ((2544142920366229301/2545000000000000000 : ℝ)+2*(274859090927/152700000000000 : ℝ)*(2847/20000 : ℝ))^(8337/2048 : ℝ) := by
    rw [show (2544142920366229301/2545000000000000000 : ℝ)+2*(274859090927/152700000000000 : ℝ)*(2847/20000 : ℝ)=(1250219610389331/1250000000000000 : ℝ) by norm_num, show 1+2*(17883681958157837/50000000000000000000 : ℝ)=(25017883681958157837/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2544142920366229301/2545000000000000000 : ℝ)*(X 1 0+X 2 0)+(274859090927/152700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8337/2048 : ℝ)) (lo := (11181/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (2544142920366229301/2545000000000000000 : ℝ)) (alpha := (274859090927/152700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2544142920366229301/2545000000000000000 : ℝ)*(X 0 1+X 2 1)+(274859090927/152700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8337/2048 : ℝ)) (lo := (11181/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (2544142920366229301/2545000000000000000 : ℝ)) (alpha := (274859090927/152700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2544142920366229301/2545000000000000000 : ℝ)*(X 0 2+X 1 2)+(274859090927/152700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8337/2048 : ℝ)) (lo := (11181/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (2544142920366229301/2545000000000000000 : ℝ)) (alpha := (274859090927/152700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-270661441/1250000000 : ℝ)*X 0 0+(1078967181/2000000000 : ℝ)*X 0 1+(5264037291/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345213353/10000000000 : ℝ)*X 1 0+(-278957577/1250000000 : ℝ)*X 1 1+(2632018673/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345213233/10000000000 : ℝ)*X 2 0+(2632018747/5000000000 : ℝ)*X 2 1+(-2231660581/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((21820789/50000000 : ℝ)*X 0 0+(529487751/1250000000 : ℝ)*X 0 1+(2248137553/5000000000 : ℝ)*X 0 2+(21820789/50000000 : ℝ)*X 1 0+(529487751/1250000000 : ℝ)*X 1 1+(2248137553/5000000000 : ℝ)*X 1 2+(21820789/50000000 : ℝ)*X 2 0+(529487751/1250000000 : ℝ)*X 2 1+(2248137553/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1082648273/5000000000 : ℝ)*X 0 0+(1316093943/2500000000 : ℝ)*X 0 1+(5394496383/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656034277/5000000000 : ℝ)*X 1 0+(-210120079/1000000000 : ℝ)*X 1 1+(2697248253/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656033989/5000000000 : ℝ)*X 2 0+(674312111/1250000000 : ℝ)*X 2 1+(-42024021/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1091042159/2500000000 : ℝ)*X 0 0+(1123900523/2500000000 : ℝ)*X 0 1+(847315449/2000000000 : ℝ)*X 0 2+(1091042159/2500000000 : ℝ)*X 1 0+(1123900523/2500000000 : ℝ)*X 1 1+(847315449/2000000000 : ℝ)*X 1 2+(1091042159/2500000000 : ℝ)*X 2 0+(1123900523/2500000000 : ℝ)*X 2 1+(847315449/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (147422122749141715409420891/63625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (175144563/25000000000000 : ℝ)*(base19) + (219976721/50000000000000 : ℝ)*(base23) + (53405381/50000000000000 : ℝ)*(upper3) + (47564919/100000000000000 : ℝ)*(upper4) + (66103991/100000000000000 : ℝ)*(upper5) + (2871510285914399/50000000000000 : ℝ)*(major0) + (2871510285914399/50000000000000 : ℝ)*(major1) + (2871510285914399/50000000000000 : ℝ)*(major2) + (7645363640075563/100000000000000 : ℝ)*(sp0) + (1911345851997439/25000000000000 : ℝ)*(sp1) + (3822691834307283/50000000000000 : ℝ)*(sp2) + (960162389484323/25000000000000 : ℝ)*(sp3) + (10234246223/50000000000000 : ℝ)*(sp4) + (7399917383/100000000000000 : ℝ)*(sp7) + (1920328478927337/50000000000000 : ℝ)*(f.failure) + (955673013571001/12500000000000 : ℝ)*(f.sum) + (3203133462167/3817500000000000000000000000 : ℝ)*base66 + (5509158934199784703/381750000000000000000000000000000 : ℝ)*base68 + (4139550656588034703/381750000000000000000000000000000 : ℝ)*base70 + (7647773457759534703/381750000000000000000000000000000 : ℝ)*base72 + (22418619166243/3817500000000000000000000000 : ℝ)*base73 + (3860791051706784703/381750000000000000000000000000000 : ℝ)*base76 + (1654810006577034703/381750000000000000000000000000000 : ℝ)*base78 + (1762523101569534703/381750000000000000000000000000000 : ℝ)*base80 + (28730430733789/7635000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1303687/1000000000000000000000 : ℝ)*base90 + (1303687/1000000000000000000000 : ℝ)*base92 + (1303687/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9577452075751856625079/2545000000000000000000000000 : ℝ) := by norm_num
    linear_combination (473774157/25000000000000 : ℝ)*(base19) + (159844069/10000000000000 : ℝ)*(base23) + (59846959/50000000000000 : ℝ)*(upper3) + (18094463/6250000000000 : ℝ)*(lower4) + (2886447736366471/50000000000000 : ℝ)*(major0) + (2886447736366471/50000000000000 : ℝ)*(major1) + (2886447736366471/50000000000000 : ℝ)*(major2) + (64972126177/100000000000000 : ℝ)*(sp1) + (63634013957/100000000000000 : ℝ)*(sp2) + (358666211/10000000000000 : ℝ)*(sp3) + (7685154960024529/100000000000000 : ℝ)*(sp4) + (307403523712069/4000000000000 : ℝ)*(sp5) + (7685089727569883/100000000000000 : ℝ)*(sp6) + (3860632273337813/100000000000000 : ℝ)*(sp7) + (1930317929999961/50000000000000 : ℝ)*(f.failure) + (7685154960024529/100000000000000 : ℝ)*(f.sum) + (7752177864839/1908750000000000000000000000 : ℝ)*base66 + (1220509543111350313/381750000000000000000000000000000 : ℝ)*base67 + (6673982222992350313/381750000000000000000000000000000 : ℝ)*base69 + (2080389229674899687/381750000000000000000000000000000 : ℝ)*base72 + (504972994321/119296875000000000000000000 : ℝ)*base73 + (2004607937156399687/381750000000000000000000000000000 : ℝ)*base76 + (5602748519963100313/381750000000000000000000000000000 : ℝ)*base77 + (1077631745838149687/381750000000000000000000000000000 : ℝ)*base80 + (343787842807/59648437500000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (16351511/1000000000000000000000 : ℝ)*base90 + (16351511/1000000000000000000000 : ℝ)*base92 + (16351511/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1145_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29906449/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11181/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (283/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1145_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1145_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29906449/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8247/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2271/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (283/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1145_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1145_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1145_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29906449/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8247/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2271/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (283/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1145_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

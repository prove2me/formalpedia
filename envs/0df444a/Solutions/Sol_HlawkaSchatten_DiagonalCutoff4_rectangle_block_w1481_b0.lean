-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1481_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:13:19.971845+00:00
-- url     : https://prove2.me/submissions/d56d5194-3799-4969-a753-e49936e0149d

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
theorem support_rectangle_w1481_s0_0 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1719212799/10000000000 : ℝ)*x 0 + (2968549703/5000000000 : ℝ)*x 1 + (2420917649/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1719212799/10000000000 : ℝ)^4459 ≤ (10171277445453/100000000000000 : ℝ)^3435 := by
    have hnat : (1719212799 : ℕ)^4459*100000000000000^3435 ≤ 10171277445453^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1719212799 10000000000 10171277445453 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2968549703/5000000000 : ℝ)^4459 ≤ (5082472981339/10000000000000 : ℝ)^3435 := by
    have hnat : (2968549703 : ℕ)^4459*10000000000000^3435 ≤ 5082472981339^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2968549703 5000000000 5082472981339 10000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2420917649/5000000000 : ℝ)^4459 ≤ (39003992727461/100000000000000 : ℝ)^3435 := by
    have hnat : (2420917649 : ℕ)^4459*100000000000000^3435 ≤ 39003992727461^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2420917649 5000000000 39003992727461 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1719212799/10000000000 : ℝ), (2968549703/5000000000 : ℝ), (2420917649/5000000000 : ℝ)] ![(10171277445453/100000000000000 : ℝ), (5082472981339/10000000000000 : ℝ), (39003992727461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1719212799/10000000000 : ℝ)|^4459 ≤ (10171277445453/100000000000000 : ℝ)^3435
        have hw : |(-1719212799/10000000000 : ℝ)|=(1719212799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2968549703/5000000000 : ℝ)|^4459 ≤ (5082472981339/10000000000000 : ℝ)^3435
        have hw : |(2968549703/5000000000 : ℝ)|=(2968549703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2420917649/5000000000 : ℝ)|^4459 ≤ (39003992727461/100000000000000 : ℝ)^3435
        have hw : |(2420917649/5000000000 : ℝ)|=(2420917649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s0_1 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5484756181/10000000000 : ℝ)*x 0 + (-1167814517/5000000000 : ℝ)*x 1 + (4841835331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5484756181/10000000000 : ℝ)^4459 ≤ (2866012829897/6250000000000 : ℝ)^3435 := by
    have hnat : (5484756181 : ℕ)^4459*6250000000000^3435 ≤ 2866012829897^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5484756181 10000000000 2866012829897 6250000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1167814517/5000000000 : ℝ)^4459 ≤ (1513980163419/10000000000000 : ℝ)^3435 := by
    have hnat : (1167814517 : ℕ)^4459*10000000000000^3435 ≤ 1513980163419^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1167814517 5000000000 1513980163419 10000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4841835331/10000000000 : ℝ)^4459 ≤ (7800798614509/20000000000000 : ℝ)^3435 := by
    have hnat : (4841835331 : ℕ)^4459*20000000000000^3435 ≤ 7800798614509^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4841835331 10000000000 7800798614509 20000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5484756181/10000000000 : ℝ), (-1167814517/5000000000 : ℝ), (4841835331/10000000000 : ℝ)] ![(2866012829897/6250000000000 : ℝ), (1513980163419/10000000000000 : ℝ), (7800798614509/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5484756181/10000000000 : ℝ)|^4459 ≤ (2866012829897/6250000000000 : ℝ)^3435
        have hw : |(5484756181/10000000000 : ℝ)|=(5484756181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1167814517/5000000000 : ℝ)|^4459 ≤ (1513980163419/10000000000000 : ℝ)^3435
        have hw : |(-1167814517/5000000000 : ℝ)|=(1167814517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4841835331/10000000000 : ℝ)|^4459 ≤ (7800798614509/20000000000000 : ℝ)^3435
        have hw : |(4841835331/10000000000 : ℝ)|=(4841835331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s0_2 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2742378047/5000000000 : ℝ)*x 0 + (38734683/80000000 : ℝ)*x 1 + (-2335629091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2742378047/5000000000 : ℝ)^4459 ≤ (45856204334137/100000000000000 : ℝ)^3435 := by
    have hnat : (2742378047 : ℕ)^4459*100000000000000^3435 ≤ 45856204334137^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2742378047 5000000000 45856204334137 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (38734683/80000000 : ℝ)^4459 ≤ (7800798706531/20000000000000 : ℝ)^3435 := by
    have hnat : (38734683 : ℕ)^4459*20000000000000^3435 ≤ 7800798706531^3435*80000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38734683 80000000 7800798706531 20000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2335629091/10000000000 : ℝ)^4459 ≤ (3027960422763/20000000000000 : ℝ)^3435 := by
    have hnat : (2335629091 : ℕ)^4459*20000000000000^3435 ≤ 3027960422763^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2335629091 10000000000 3027960422763 20000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2742378047/5000000000 : ℝ), (38734683/80000000 : ℝ), (-2335629091/10000000000 : ℝ)] ![(45856204334137/100000000000000 : ℝ), (7800798706531/20000000000000 : ℝ), (3027960422763/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2742378047/5000000000 : ℝ)|^4459 ≤ (45856204334137/100000000000000 : ℝ)^3435
        have hw : |(2742378047/5000000000 : ℝ)|=(2742378047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(38734683/80000000 : ℝ)|^4459 ≤ (7800798706531/20000000000000 : ℝ)^3435
        have hw : |(38734683/80000000 : ℝ)|=(38734683/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2335629091/10000000000 : ℝ)|^4459 ≤ (3027960422763/20000000000000 : ℝ)^3435
        have hw : |(-2335629091/10000000000 : ℝ)|=(2335629091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s0_3 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4153610271/10000000000 : ℝ)*x 0 + (309145847/1000000000 : ℝ)*x 1 + (2760454383/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4153610271/10000000000 : ℝ)^4459 ≤ (15982529687407/50000000000000 : ℝ)^3435 := by
    have hnat : (4153610271 : ℕ)^4459*50000000000000^3435 ≤ 15982529687407^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4153610271 10000000000 15982529687407 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (309145847/1000000000 : ℝ)^4459 ≤ (10892992440887/50000000000000 : ℝ)^3435 := by
    have hnat : (309145847 : ℕ)^4459*50000000000000^3435 ≤ 10892992440887^3435*1000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      309145847 1000000000 10892992440887 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2760454383/5000000000 : ℝ)^4459 ≤ (4624895573223/10000000000000 : ℝ)^3435 := by
    have hnat : (2760454383 : ℕ)^4459*10000000000000^3435 ≤ 4624895573223^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2760454383 5000000000 4624895573223 10000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4153610271/10000000000 : ℝ), (309145847/1000000000 : ℝ), (2760454383/5000000000 : ℝ)] ![(15982529687407/50000000000000 : ℝ), (10892992440887/50000000000000 : ℝ), (4624895573223/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4153610271/10000000000 : ℝ)|^4459 ≤ (15982529687407/50000000000000 : ℝ)^3435
        have hw : |(4153610271/10000000000 : ℝ)|=(4153610271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(309145847/1000000000 : ℝ)|^4459 ≤ (10892992440887/50000000000000 : ℝ)^3435
        have hw : |(309145847/1000000000 : ℝ)|=(309145847/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2760454383/5000000000 : ℝ)|^4459 ≤ (4624895573223/10000000000000 : ℝ)^3435
        have hw : |(2760454383/5000000000 : ℝ)|=(2760454383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s0_4 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1723007089/10000000000 : ℝ)*x 0 + (4869928957/10000000000 : ℝ)*x 1 + (5907995501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1723007089/10000000000 : ℝ)^4459 ≤ (255010671583/2500000000000 : ℝ)^3435 := by
    have hnat : (1723007089 : ℕ)^4459*2500000000000^3435 ≤ 255010671583^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1723007089 10000000000 255010671583 2500000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4869928957/10000000000 : ℝ)^4459 ≤ (7859604732079/20000000000000 : ℝ)^3435 := by
    have hnat : (4869928957 : ℕ)^4459*20000000000000^3435 ≤ 7859604732079^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4869928957 10000000000 7859604732079 20000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5907995501/10000000000 : ℝ)^4459 ≤ (50501549463277/100000000000000 : ℝ)^3435 := by
    have hnat : (5907995501 : ℕ)^4459*100000000000000^3435 ≤ 50501549463277^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5907995501 10000000000 50501549463277 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1723007089/10000000000 : ℝ), (4869928957/10000000000 : ℝ), (5907995501/10000000000 : ℝ)] ![(255010671583/2500000000000 : ℝ), (7859604732079/20000000000000 : ℝ), (50501549463277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1723007089/10000000000 : ℝ)|^4459 ≤ (255010671583/2500000000000 : ℝ)^3435
        have hw : |(-1723007089/10000000000 : ℝ)|=(1723007089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4869928957/10000000000 : ℝ)|^4459 ≤ (7859604732079/20000000000000 : ℝ)^3435
        have hw : |(4869928957/10000000000 : ℝ)|=(4869928957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5907995501/10000000000 : ℝ)|^4459 ≤ (50501549463277/100000000000000 : ℝ)^3435
        have hw : |(5907995501/10000000000 : ℝ)|=(5907995501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s0_5 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (32410577/62500000 : ℝ)*x 0 + (-1269468649/10000000000 : ℝ)*x 1 + (1181599099/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (32410577/62500000 : ℝ)^4459 ≤ (4263717637659/10000000000000 : ℝ)^3435 := by
    have hnat : (32410577 : ℕ)^4459*10000000000000^3435 ≤ 4263717637659^3435*62500000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32410577 62500000 4263717637659 10000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1269468649/10000000000 : ℝ)^4459 ≤ (686127422053/10000000000000 : ℝ)^3435 := by
    have hnat : (1269468649 : ℕ)^4459*10000000000000^3435 ≤ 686127422053^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1269468649 10000000000 686127422053 10000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1181599099/2000000000 : ℝ)^4459 ≤ (505015493967/1000000000000 : ℝ)^3435 := by
    have hnat : (1181599099 : ℕ)^4459*1000000000000^3435 ≤ 505015493967^3435*2000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1181599099 2000000000 505015493967 1000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(32410577/62500000 : ℝ), (-1269468649/10000000000 : ℝ), (1181599099/2000000000 : ℝ)] ![(4263717637659/10000000000000 : ℝ), (686127422053/10000000000000 : ℝ), (505015493967/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(32410577/62500000 : ℝ)|^4459 ≤ (4263717637659/10000000000000 : ℝ)^3435
        have hw : |(32410577/62500000 : ℝ)|=(32410577/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1269468649/10000000000 : ℝ)|^4459 ≤ (686127422053/10000000000000 : ℝ)^3435
        have hw : |(-1269468649/10000000000 : ℝ)|=(1269468649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1181599099/2000000000 : ℝ)|^4459 ≤ (505015493967/1000000000000 : ℝ)^3435
        have hw : |(1181599099/2000000000 : ℝ)|=(1181599099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s0_6 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1037138441/2000000000 : ℝ)*x 0 + (2953997739/5000000000 : ℝ)*x 1 + (-25389377/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1037138441/2000000000 : ℝ)^4459 ≤ (42637175149179/100000000000000 : ℝ)^3435 := by
    have hnat : (1037138441 : ℕ)^4459*100000000000000^3435 ≤ 42637175149179^3435*2000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037138441 2000000000 42637175149179 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2953997739/5000000000 : ℝ)^4459 ≤ (98635838297/195312500000 : ℝ)^3435 := by
    have hnat : (2953997739 : ℕ)^4459*195312500000^3435 ≤ 98635838297^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2953997739 5000000000 98635838297 195312500000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (25389377/200000000 : ℝ)^4459 ≤ (6861275630759/100000000000000 : ℝ)^3435 := by
    have hnat : (25389377 : ℕ)^4459*100000000000000^3435 ≤ 6861275630759^3435*200000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25389377 200000000 6861275630759 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1037138441/2000000000 : ℝ), (2953997739/5000000000 : ℝ), (-25389377/200000000 : ℝ)] ![(42637175149179/100000000000000 : ℝ), (98635838297/195312500000 : ℝ), (6861275630759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1037138441/2000000000 : ℝ)|^4459 ≤ (42637175149179/100000000000000 : ℝ)^3435
        have hw : |(1037138441/2000000000 : ℝ)|=(1037138441/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2953997739/5000000000 : ℝ)|^4459 ≤ (98635838297/195312500000 : ℝ)^3435
        have hw : |(2953997739/5000000000 : ℝ)|=(2953997739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-25389377/200000000 : ℝ)|^4459 ≤ (6861275630759/100000000000000 : ℝ)^3435
        have hw : |(-25389377/200000000 : ℝ)|=(25389377/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s0_7 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (520253381/1250000000 : ℝ)*x 0 + (5458592859/10000000000 : ℝ)*x 1 + (789003799/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (520253381/1250000000 : ℝ)^4459 ≤ (6409833479167/20000000000000 : ℝ)^3435 := by
    have hnat : (520253381 : ℕ)^4459*20000000000000^3435 ≤ 6409833479167^3435*1250000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520253381 1250000000 6409833479167 20000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5458592859/10000000000 : ℝ)^4459 ≤ (22786227871669/50000000000000 : ℝ)^3435 := by
    have hnat : (5458592859 : ℕ)^4459*50000000000000^3435 ≤ 22786227871669^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5458592859 10000000000 22786227871669 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (789003799/2500000000 : ℝ)^4459 ≤ (22378376851097/100000000000000 : ℝ)^3435 := by
    have hnat : (789003799 : ℕ)^4459*100000000000000^3435 ≤ 22378376851097^3435*2500000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      789003799 2500000000 22378376851097 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(520253381/1250000000 : ℝ), (5458592859/10000000000 : ℝ), (789003799/2500000000 : ℝ)] ![(6409833479167/20000000000000 : ℝ), (22786227871669/50000000000000 : ℝ), (22378376851097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(520253381/1250000000 : ℝ)|^4459 ≤ (6409833479167/20000000000000 : ℝ)^3435
        have hw : |(520253381/1250000000 : ℝ)|=(520253381/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5458592859/10000000000 : ℝ)|^4459 ≤ (22786227871669/50000000000000 : ℝ)^3435
        have hw : |(5458592859/10000000000 : ℝ)|=(5458592859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(789003799/2500000000 : ℝ)|^4459 ≤ (22378376851097/100000000000000 : ℝ)^3435
        have hw : |(789003799/2500000000 : ℝ)|=(789003799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1481_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160907049/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2419/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6473/25000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4457/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4457 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4457*1^1024 ≤ 0^1024*1^4457 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4457 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4457 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4457/1024 : ℝ) ≤ (1853320662701423943/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4457 ≤ (1853320662701423943/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4457*100000000000000000000^1024 ≤ 1853320662701423943^1024*5^4457 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1853320662701423943 100000000000000000000 4457 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1853320662701423943/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4457 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4457/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4457 := by
      have hnat : (1 : ℕ)^1024*1^4457 ≤ 1^4457*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4457 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101853320662701423943/100000000000000000000 : ℝ) ≤ (2510569895085553/2500000000000000 : ℝ) ^ (4457/1024 : ℝ) := by
    have hpowers : (101853320662701423943/100000000000000000000 : ℝ)^1024 ≤ (2510569895085553/2500000000000000 : ℝ)^4457 := by
      have hnat : (101853320662701423943 : ℕ)^1024*2500000000000000^4457 ≤ 2510569895085553^4457*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101853320662701423943 100000000000000000000 2510569895085553 2500000000000000 1024 4457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2510569895085553/2500000000000000 : ℝ)) (X := (101853320662701423943/100000000000000000000 : ℝ)) (by norm_num) 4457 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51853320662701423943/50000000000000000000 : ℝ) ≤ (1260569895085553/1250000000000000 : ℝ) ^ (4457/1024 : ℝ) := by
    have hpowers : (51853320662701423943/50000000000000000000 : ℝ)^1024 ≤ (1260569895085553/1250000000000000 : ℝ)^4457 := by
      have hnat : (51853320662701423943 : ℕ)^1024*1250000000000000^4457 ≤ 1260569895085553^4457*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51853320662701423943 50000000000000000000 1260569895085553 1250000000000000 1024 4457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1260569895085553/1250000000000000 : ℝ)) (X := (51853320662701423943/50000000000000000000 : ℝ)) (by norm_num) 4457 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(10569895085553/1000000000000000 : ℝ)*(0 : ℝ))^(4457/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(10569895085553/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1853320662701423943/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(10569895085553/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4457/1024 : ℝ) := by
    rw [show (1 : ℝ)+(10569895085553/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2510569895085553/2500000000000000 : ℝ) by norm_num, show 1+(1853320662701423943/100000000000000000000 : ℝ)+(0 : ℝ)=(101853320662701423943/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1853320662701423943/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(10569895085553/1000000000000000 : ℝ)*(2/5 : ℝ))^(4457/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(10569895085553/1000000000000000 : ℝ)*(2/5 : ℝ)=(1260569895085553/1250000000000000 : ℝ) by norm_num, show 1+2*(1853320662701423943/100000000000000000000 : ℝ)=(51853320662701423943/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(10569895085553/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4457/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (10569895085553/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(10569895085553/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4457/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (10569895085553/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(10569895085553/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4457/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (10569895085553/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1719212799/10000000000 : ℝ)*X 0 0+(2968549703/5000000000 : ℝ)*X 0 1+(2420917649/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5484756181/10000000000 : ℝ)*X 1 0+(-1167814517/5000000000 : ℝ)*X 1 1+(4841835331/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2742378047/5000000000 : ℝ)*X 2 0+(38734683/80000000 : ℝ)*X 2 1+(-2335629091/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4153610271/10000000000 : ℝ)*X 0 0+(309145847/1000000000 : ℝ)*X 0 1+(2760454383/5000000000 : ℝ)*X 0 2+(4153610271/10000000000 : ℝ)*X 1 0+(309145847/1000000000 : ℝ)*X 1 1+(2760454383/5000000000 : ℝ)*X 1 2+(4153610271/10000000000 : ℝ)*X 2 0+(309145847/1000000000 : ℝ)*X 2 1+(2760454383/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1723007089/10000000000 : ℝ)*X 0 0+(4869928957/10000000000 : ℝ)*X 0 1+(5907995501/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((32410577/62500000 : ℝ)*X 1 0+(-1269468649/10000000000 : ℝ)*X 1 1+(1181599099/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1037138441/2000000000 : ℝ)*X 2 0+(2953997739/5000000000 : ℝ)*X 2 1+(-25389377/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((520253381/1250000000 : ℝ)*X 0 0+(5458592859/10000000000 : ℝ)*X 0 1+(789003799/2500000000 : ℝ)*X 0 2+(520253381/1250000000 : ℝ)*X 1 0+(5458592859/10000000000 : ℝ)*X 1 1+(789003799/2500000000 : ℝ)*X 1 2+(520253381/1250000000 : ℝ)*X 2 0+(5458592859/10000000000 : ℝ)*X 2 1+(789003799/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (82718880885410971786353/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (49475263/100000000000000 : ℝ)*(base1) + (294606051/20000000000000 : ℝ)*(base19) + (291709527/20000000000000 : ℝ)*(base23) + (3916967/2000000000000 : ℝ)*(upper3) + (175781823/100000000000000 : ℝ)*(upper5) + (662326209095367/100000000000000 : ℝ)*(major0) + (662326209095367/100000000000000 : ℝ)*(major1) + (662326209095367/100000000000000 : ℝ)*(major2) + (913026772237411/100000000000000 : ℝ)*(sp0) + (456515171494527/50000000000000 : ℝ)*(sp1) + (456515178735837/50000000000000 : ℝ)*(sp2) + (205808977085369/50000000000000 : ℝ)*(sp3) + (5093257161/100000000000000 : ℝ)*(sp4) + (2377941737/100000000000000 : ℝ)*(sp7) + (411620381587737/100000000000000 : ℝ)*(f.failure) + (913031816019309/100000000000000 : ℝ)*(f.sum) + (93942531867049/50000000000000000000000000000 : ℝ)*base66 + (777966387667049/100000000000000000000000000000 : ℝ)*base68 + (381605888967049/100000000000000000000000000000 : ℝ)*base70 + (586496313867049/100000000000000000000000000000 : ℝ)*base72 + (14452454417049/50000000000000000000000000000 : ℝ)*base74 + (797955962467049/100000000000000000000000000000 : ℝ)*base76 + (432700172067049/100000000000000000000000000000 : ℝ)*base78 + (1057274268367049/100000000000000000000000000000 : ℝ)*base80 + (75510379632951/50000000000000000000000000000 : ℝ)*base81 + (4741887/10000000000000000000000 : ℝ)*base90 + (4741887/10000000000000000000000 : ℝ)*base92 + (4741887/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (219671095035910199098281/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (125265163/6250000000000 : ℝ)*(base19) + (248863219/12500000000000 : ℝ)*(base23) + (75744887/50000000000000 : ℝ)*(base32) + (145990273/50000000000000 : ℝ)*(upper3) + (195602103/100000000000000 : ℝ)*(upper5) + (698812297534341/100000000000000 : ℝ)*(major0) + (698812297534341/100000000000000 : ℝ)*(major1) + (698812297534341/100000000000000 : ℝ)*(major2) + (1237099389/25000000000000 : ℝ)*(sp1) + (5087570483/100000000000000 : ℝ)*(sp2) + (192665732524931/20000000000000 : ℝ)*(sp4) + (96332170998449/10000000000000 : ℝ)*(sp5) + (963321584148419/100000000000000 : ℝ)*(sp6) + (86859097611891/20000000000000 : ℝ)*(sp7) + (434295639549229/100000000000000 : ℝ)*(f.failure) + (192665732524931/20000000000000 : ℝ)*(f.sum) + (90207173225573/50000000000000000000000000000 : ℝ)*base65 + (551951517524427/100000000000000000000000000000 : ℝ)*base68 + (80560383024427/100000000000000000000000000000 : ℝ)*base70 + (114700222875573/100000000000000000000000000000 : ℝ)*base71 + (114791696074427/50000000000000000000000000000 : ℝ)*base74 + (587134973875573/100000000000000000000000000000 : ℝ)*base75 + (131526536775573/100000000000000000000000000000 : ℝ)*base77 + (215903425275573/100000000000000000000000000000 : ℝ)*base79 + (120429696625573/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (28615221/10000000000000000000000 : ℝ)*base89 + (28615221/10000000000000000000000 : ℝ)*base91 + (28615221/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1481_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160907049/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2419/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6473/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1481_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1481_s1_0 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-235167687/1250000000 : ℝ)*x 0 + (1398005627/2500000000 : ℝ)*x 1 + (1270710661/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (235167687/1250000000 : ℝ)^4459 ≤ (11433543259633/100000000000000 : ℝ)^3435 := by
    have hnat : (235167687 : ℕ)^4459*100000000000000^3435 ≤ 11433543259633^3435*1250000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235167687 1250000000 11433543259633 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1398005627/2500000000 : ℝ)^4459 ≤ (47023749549031/100000000000000 : ℝ)^3435 := by
    have hnat : (1398005627 : ℕ)^4459*100000000000000^3435 ≤ 47023749549031^3435*2500000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1398005627 2500000000 47023749549031 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1270710661/2500000000 : ℝ)^4459 ≤ (649104799653/1562500000000 : ℝ)^3435 := by
    have hnat : (1270710661 : ℕ)^4459*1562500000000^3435 ≤ 649104799653^3435*2500000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1270710661 2500000000 649104799653 1562500000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-235167687/1250000000 : ℝ), (1398005627/2500000000 : ℝ), (1270710661/2500000000 : ℝ)] ![(11433543259633/100000000000000 : ℝ), (47023749549031/100000000000000 : ℝ), (649104799653/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-235167687/1250000000 : ℝ)|^4459 ≤ (11433543259633/100000000000000 : ℝ)^3435
        have hw : |(-235167687/1250000000 : ℝ)|=(235167687/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1398005627/2500000000 : ℝ)|^4459 ≤ (47023749549031/100000000000000 : ℝ)^3435
        have hw : |(1398005627/2500000000 : ℝ)|=(1398005627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1270710661/2500000000 : ℝ)|^4459 ≤ (649104799653/1562500000000 : ℝ)^3435
        have hw : |(1270710661/2500000000 : ℝ)|=(1270710661/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s1_1 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2696188327/5000000000 : ℝ)*x 0 + (-430108777/2000000000 : ℝ)*x 1 + (2541421501/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2696188327/5000000000 : ℝ)^4459 ≤ (22428066668459/50000000000000 : ℝ)^3435 := by
    have hnat : (2696188327 : ℕ)^4459*50000000000000^3435 ≤ 22428066668459^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696188327 5000000000 22428066668459 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (430108777/2000000000 : ℝ)^4459 ≤ (6800577834077/50000000000000 : ℝ)^3435 := by
    have hnat : (430108777 : ℕ)^4459*50000000000000^3435 ≤ 6800577834077^3435*2000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430108777 2000000000 6800577834077 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2541421501/5000000000 : ℝ)^4459 ≤ (10385677744007/25000000000000 : ℝ)^3435 := by
    have hnat : (2541421501 : ℕ)^4459*25000000000000^3435 ≤ 10385677744007^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2541421501 5000000000 10385677744007 25000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2696188327/5000000000 : ℝ), (-430108777/2000000000 : ℝ), (2541421501/5000000000 : ℝ)] ![(22428066668459/50000000000000 : ℝ), (6800577834077/50000000000000 : ℝ), (10385677744007/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2696188327/5000000000 : ℝ)|^4459 ≤ (22428066668459/50000000000000 : ℝ)^3435
        have hw : |(2696188327/5000000000 : ℝ)|=(2696188327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-430108777/2000000000 : ℝ)|^4459 ≤ (6800577834077/50000000000000 : ℝ)^3435
        have hw : |(-430108777/2000000000 : ℝ)|=(430108777/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2541421501/5000000000 : ℝ)|^4459 ≤ (10385677744007/25000000000000 : ℝ)^3435
        have hw : |(2541421501/5000000000 : ℝ)|=(2541421501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s1_2 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5392377091/10000000000 : ℝ)*x 0 + (1016568549/2000000000 : ℝ)*x 1 + (-2150543643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5392377091/10000000000 : ℝ)^4459 ≤ (22428069027871/50000000000000 : ℝ)^3435 := by
    have hnat : (5392377091 : ℕ)^4459*50000000000000^3435 ≤ 22428069027871^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392377091 10000000000 22428069027871 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1016568549/2000000000 : ℝ)^4459 ≤ (20771354124681/50000000000000 : ℝ)^3435 := by
    have hnat : (1016568549 : ℕ)^4459*50000000000000^3435 ≤ 20771354124681^3435*2000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016568549 2000000000 20771354124681 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2150543643/10000000000 : ℝ)^4459 ≤ (13601153681357/100000000000000 : ℝ)^3435 := by
    have hnat : (2150543643 : ℕ)^4459*100000000000000^3435 ≤ 13601153681357^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150543643 10000000000 13601153681357 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5392377091/10000000000 : ℝ), (1016568549/2000000000 : ℝ), (-2150543643/10000000000 : ℝ)] ![(22428069027871/50000000000000 : ℝ), (20771354124681/50000000000000 : ℝ), (13601153681357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5392377091/10000000000 : ℝ)|^4459 ≤ (22428069027871/50000000000000 : ℝ)^3435
        have hw : |(5392377091/10000000000 : ℝ)|=(5392377091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1016568549/2000000000 : ℝ)|^4459 ≤ (20771354124681/50000000000000 : ℝ)^3435
        have hw : |(1016568549/2000000000 : ℝ)|=(1016568549/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2150543643/10000000000 : ℝ)|^4459 ≤ (13601153681357/100000000000000 : ℝ)^3435
        have hw : |(-2150543643/10000000000 : ℝ)|=(2150543643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s1_3 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4260900451/10000000000 : ℝ)*x 0 + (3728596859/10000000000 : ℝ)*x 1 + (4858029381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4260900451/10000000000 : ℝ)^4459 ≤ (16520488975213/50000000000000 : ℝ)^3435 := by
    have hnat : (4260900451 : ℕ)^4459*50000000000000^3435 ≤ 16520488975213^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4260900451 10000000000 16520488975213 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3728596859/10000000000 : ℝ)^4459 ≤ (434150037131/1562500000000 : ℝ)^3435 := by
    have hnat : (3728596859 : ℕ)^4459*1562500000000^3435 ≤ 434150037131^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3728596859 10000000000 434150037131 1562500000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4858029381/10000000000 : ℝ)^4459 ≤ (3917341965347/10000000000000 : ℝ)^3435 := by
    have hnat : (4858029381 : ℕ)^4459*10000000000000^3435 ≤ 3917341965347^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4858029381 10000000000 3917341965347 10000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4260900451/10000000000 : ℝ), (3728596859/10000000000 : ℝ), (4858029381/10000000000 : ℝ)] ![(16520488975213/50000000000000 : ℝ), (434150037131/1562500000000 : ℝ), (3917341965347/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4260900451/10000000000 : ℝ)|^4459 ≤ (16520488975213/50000000000000 : ℝ)^3435
        have hw : |(4260900451/10000000000 : ℝ)|=(4260900451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3728596859/10000000000 : ℝ)|^4459 ≤ (434150037131/1562500000000 : ℝ)^3435
        have hw : |(3728596859/10000000000 : ℝ)|=(3728596859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4858029381/10000000000 : ℝ)|^4459 ≤ (3917341965347/10000000000000 : ℝ)^3435
        have hw : |(4858029381/10000000000 : ℝ)|=(4858029381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s1_4 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-376341701/2000000000 : ℝ)*x 0 + (2544396147/5000000000 : ℝ)*x 1 + (5585972567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (376341701/2000000000 : ℝ)^4459 ≤ (1429554836377/12500000000000 : ℝ)^3435 := by
    have hnat : (376341701 : ℕ)^4459*12500000000000^3435 ≤ 1429554836377^3435*2000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      376341701 2000000000 1429554836377 12500000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2544396147/5000000000 : ℝ)^4459 ≤ (1040146039323/2500000000000 : ℝ)^3435 := by
    have hnat : (2544396147 : ℕ)^4459*2500000000000^3435 ≤ 1040146039323^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2544396147 5000000000 1040146039323 2500000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5585972567/10000000000 : ℝ)^4459 ≤ (9391543944459/20000000000000 : ℝ)^3435 := by
    have hnat : (5585972567 : ℕ)^4459*20000000000000^3435 ≤ 9391543944459^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5585972567 10000000000 9391543944459 20000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-376341701/2000000000 : ℝ), (2544396147/5000000000 : ℝ), (5585972567/10000000000 : ℝ)] ![(1429554836377/12500000000000 : ℝ), (1040146039323/2500000000000 : ℝ), (9391543944459/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-376341701/2000000000 : ℝ)|^4459 ≤ (1429554836377/12500000000000 : ℝ)^3435
        have hw : |(-376341701/2000000000 : ℝ)|=(376341701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2544396147/5000000000 : ℝ)|^4459 ≤ (1040146039323/2500000000000 : ℝ)^3435
        have hw : |(2544396147/5000000000 : ℝ)|=(2544396147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5585972567/10000000000 : ℝ)|^4459 ≤ (9391543944459/20000000000000 : ℝ)^3435
        have hw : |(5585972567/10000000000 : ℝ)|=(5585972567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s1_5 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5258785589/10000000000 : ℝ)*x 0 + (-823706971/5000000000 : ℝ)*x 1 + (5585972609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5258785589/10000000000 : ℝ)^4459 ≤ (43418945101589/100000000000000 : ℝ)^3435 := by
    have hnat : (5258785589 : ℕ)^4459*100000000000000^3435 ≤ 43418945101589^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258785589 10000000000 43418945101589 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (823706971/5000000000 : ℝ)^4459 ≤ (9623334700737/100000000000000 : ℝ)^3435 := by
    have hnat : (823706971 : ℕ)^4459*100000000000000^3435 ≤ 9623334700737^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      823706971 5000000000 9623334700737 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5585972609/10000000000 : ℝ)^4459 ≤ (9391544036123/20000000000000 : ℝ)^3435 := by
    have hnat : (5585972609 : ℕ)^4459*20000000000000^3435 ≤ 9391544036123^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5585972609 10000000000 9391544036123 20000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5258785589/10000000000 : ℝ), (-823706971/5000000000 : ℝ), (5585972609/10000000000 : ℝ)] ![(43418945101589/100000000000000 : ℝ), (9623334700737/100000000000000 : ℝ), (9391544036123/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5258785589/10000000000 : ℝ)|^4459 ≤ (43418945101589/100000000000000 : ℝ)^3435
        have hw : |(5258785589/10000000000 : ℝ)|=(5258785589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-823706971/5000000000 : ℝ)|^4459 ≤ (9623334700737/100000000000000 : ℝ)^3435
        have hw : |(-823706971/5000000000 : ℝ)|=(823706971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5585972609/10000000000 : ℝ)|^4459 ≤ (9391544036123/20000000000000 : ℝ)^3435
        have hw : |(5585972609/10000000000 : ℝ)|=(5585972609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s1_6 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2629392803/5000000000 : ℝ)*x 0 + (5585972581/10000000000 : ℝ)*x 1 + (-1647413959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2629392803/5000000000 : ℝ)^4459 ≤ (43418945283791/100000000000000 : ℝ)^3435 := by
    have hnat : (2629392803 : ℕ)^4459*100000000000000^3435 ≤ 43418945283791^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629392803 5000000000 43418945283791 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5585972581/10000000000 : ℝ)^4459 ≤ (46957719875069/100000000000000 : ℝ)^3435 := by
    have hnat : (5585972581 : ℕ)^4459*100000000000000^3435 ≤ 46957719875069^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5585972581 10000000000 46957719875069 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1647413959/10000000000 : ℝ)^4459 ≤ (1924666965929/20000000000000 : ℝ)^3435 := by
    have hnat : (1647413959 : ℕ)^4459*20000000000000^3435 ≤ 1924666965929^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1647413959 10000000000 1924666965929 20000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2629392803/5000000000 : ℝ), (5585972581/10000000000 : ℝ), (-1647413959/10000000000 : ℝ)] ![(43418945283791/100000000000000 : ℝ), (46957719875069/100000000000000 : ℝ), (1924666965929/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2629392803/5000000000 : ℝ)|^4459 ≤ (43418945283791/100000000000000 : ℝ)^3435
        have hw : |(2629392803/5000000000 : ℝ)|=(2629392803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5585972581/10000000000 : ℝ)|^4459 ≤ (46957719875069/100000000000000 : ℝ)^3435
        have hw : |(5585972581/10000000000 : ℝ)|=(5585972581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1647413959/10000000000 : ℝ)|^4459 ≤ (1924666965929/20000000000000 : ℝ)^3435
        have hw : |(-1647413959/10000000000 : ℝ)|=(1647413959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s1_7 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4261714649/10000000000 : ℝ)*x 0 + (968966553/2000000000 : ℝ)*x 1 + (3742016331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4261714649/10000000000 : ℝ)^4459 ≤ (3304917400113/10000000000000 : ℝ)^3435 := by
    have hnat : (4261714649 : ℕ)^4459*10000000000000^3435 ≤ 3304917400113^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4261714649 10000000000 3304917400113 10000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (968966553/2000000000 : ℝ)^4459 ≤ (4879417540633/12500000000000 : ℝ)^3435 := by
    have hnat : (968966553 : ℕ)^4459*12500000000000^3435 ≤ 4879417540633^3435*2000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      968966553 2000000000 4879417540633 12500000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3742016331/10000000000 : ℝ)^4459 ≤ (13957742831211/50000000000000 : ℝ)^3435 := by
    have hnat : (3742016331 : ℕ)^4459*50000000000000^3435 ≤ 13957742831211^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3742016331 10000000000 13957742831211 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4261714649/10000000000 : ℝ), (968966553/2000000000 : ℝ), (3742016331/10000000000 : ℝ)] ![(3304917400113/10000000000000 : ℝ), (4879417540633/12500000000000 : ℝ), (13957742831211/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4261714649/10000000000 : ℝ)|^4459 ≤ (3304917400113/10000000000000 : ℝ)^3435
        have hw : |(4261714649/10000000000 : ℝ)|=(4261714649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(968966553/2000000000 : ℝ)|^4459 ≤ (4879417540633/12500000000000 : ℝ)^3435
        have hw : |(968966553/2000000000 : ℝ)|=(968966553/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3742016331/10000000000 : ℝ)|^4459 ≤ (13957742831211/50000000000000 : ℝ)^3435
        have hw : |(3742016331/10000000000 : ℝ)|=(3742016331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1481_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160907049/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6473/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2419/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (99/1250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3737/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6473/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2419/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6473/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2419/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6473/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2419/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6473/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2419/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6473/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2419/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6473/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2419/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2419/100000 : ℝ) ^ (4457/1024 : ℝ) ≤ (9219597847081/100000000000000000000 : ℝ) := by
    have hpowers : (2419/100000 : ℝ)^4457 ≤ (9219597847081/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2419 : ℕ)^4457*100000000000000000000^1024 ≤ 9219597847081^1024*100000^4457 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2419 100000 9219597847081 100000000000000000000 4457 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2419/100000 : ℝ)) (X := (9219597847081/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4457 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (6473/25000 : ℝ) ^ (4457/1024 : ℝ) ≤ (279113179225254393/100000000000000000000 : ℝ) := by
    have hpowers : (6473/25000 : ℝ)^4457 ≤ (279113179225254393/100000000000000000000 : ℝ)^1024 := by
      have hnat : (6473 : ℕ)^4457*100000000000000000000^1024 ≤ 279113179225254393^1024*25000^4457 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6473 25000 279113179225254393 100000000000000000000 4457 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6473/25000 : ℝ)) (X := (279113179225254393/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4457 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000009219597847081/50000000000000000000 : ℝ) ≤ (40000001694569/40000000000000 : ℝ) ^ (4457/1024 : ℝ) := by
    have hpowers : (50000009219597847081/50000000000000000000 : ℝ)^1024 ≤ (40000001694569/40000000000000 : ℝ)^4457 := by
      have hnat : (50000009219597847081 : ℕ)^1024*40000000000000^4457 ≤ 40000001694569^4457*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000009219597847081 50000000000000000000 40000001694569 40000000000000 1024 4457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (40000001694569/40000000000000 : ℝ)) (X := (50000009219597847081/50000000000000000000 : ℝ)) (by norm_num) 4457 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50139561199411550737/50000000000000000000 : ℝ) ≤ (10006405981432649/10000000000000000 : ℝ) ^ (4457/1024 : ℝ) := by
    have hpowers : (50139561199411550737/50000000000000000000 : ℝ)^1024 ≤ (10006405981432649/10000000000000000 : ℝ)^4457 := by
      have hnat : (50139561199411550737 : ℕ)^1024*10000000000000000^4457 ≤ 10006405981432649^4457*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50139561199411550737 50000000000000000000 10006405981432649 10000000000000000 1024 4457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006405981432649/10000000000000000 : ℝ)) (X := (50139561199411550737/50000000000000000000 : ℝ)) (by norm_num) 4457 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50279113179225254393/50000000000000000000 : ℝ) ≤ (1251601442402881/1250000000000000 : ℝ) ^ (4457/1024 : ℝ) := by
    have hpowers : (50279113179225254393/50000000000000000000 : ℝ)^1024 ≤ (1251601442402881/1250000000000000 : ℝ)^4457 := by
      have hnat : (50279113179225254393 : ℕ)^1024*1250000000000000^4457 ≤ 1251601442402881^4457*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50279113179225254393 50000000000000000000 1251601442402881 1250000000000000 1024 4457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1251601442402881/1250000000000000 : ℝ)) (X := (50279113179225254393/50000000000000000000 : ℝ)) (by norm_num) 4457 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9219597847081/100000000000000000000 : ℝ) ≤ ((14668688740972786493/14670625000000000000 : ℝ)+2*(6405557790399/2347300000000000 : ℝ)*(2419/100000 : ℝ))^(4457/1024 : ℝ) := by
    rw [show (14668688740972786493/14670625000000000000 : ℝ)+2*(6405557790399/2347300000000000 : ℝ)*(2419/100000 : ℝ)=(40000001694569/40000000000000 : ℝ) by norm_num, show 1+2*(9219597847081/100000000000000000000 : ℝ)=(50000009219597847081/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(279113179225254393/100000000000000000000 : ℝ)+(9219597847081/100000000000000000000 : ℝ) ≤ ((14668688740972786493/14670625000000000000 : ℝ)+(6405557790399/2347300000000000 : ℝ)*((6473/25000 : ℝ)+(2419/100000 : ℝ)))^(4457/1024 : ℝ) := by
    rw [show (14668688740972786493/14670625000000000000 : ℝ)+(6405557790399/2347300000000000 : ℝ)*((6473/25000 : ℝ)+(2419/100000 : ℝ))=(10006405981432649/10000000000000000 : ℝ) by norm_num, show 1+(279113179225254393/100000000000000000000 : ℝ)+(9219597847081/100000000000000000000 : ℝ)=(50139561199411550737/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(279113179225254393/100000000000000000000 : ℝ) ≤ ((14668688740972786493/14670625000000000000 : ℝ)+2*(6405557790399/2347300000000000 : ℝ)*(6473/25000 : ℝ))^(4457/1024 : ℝ) := by
    rw [show (14668688740972786493/14670625000000000000 : ℝ)+2*(6405557790399/2347300000000000 : ℝ)*(6473/25000 : ℝ)=(1251601442402881/1250000000000000 : ℝ) by norm_num, show 1+2*(279113179225254393/100000000000000000000 : ℝ)=(50279113179225254393/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14668688740972786493/14670625000000000000 : ℝ)*(X 1 0+X 2 0)+(6405557790399/2347300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4457/1024 : ℝ)) (lo := (2419/100000 : ℝ)) (hi := (6473/25000 : ℝ)) (c := (14668688740972786493/14670625000000000000 : ℝ)) (alpha := (6405557790399/2347300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14668688740972786493/14670625000000000000 : ℝ)*(X 0 1+X 2 1)+(6405557790399/2347300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4457/1024 : ℝ)) (lo := (2419/100000 : ℝ)) (hi := (6473/25000 : ℝ)) (c := (14668688740972786493/14670625000000000000 : ℝ)) (alpha := (6405557790399/2347300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14668688740972786493/14670625000000000000 : ℝ)*(X 0 2+X 1 2)+(6405557790399/2347300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4457/1024 : ℝ)) (lo := (2419/100000 : ℝ)) (hi := (6473/25000 : ℝ)) (c := (14668688740972786493/14670625000000000000 : ℝ)) (alpha := (6405557790399/2347300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-235167687/1250000000 : ℝ)*X 0 0+(1398005627/2500000000 : ℝ)*X 0 1+(1270710661/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2696188327/5000000000 : ℝ)*X 1 0+(-430108777/2000000000 : ℝ)*X 1 1+(2541421501/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5392377091/10000000000 : ℝ)*X 2 0+(1016568549/2000000000 : ℝ)*X 2 1+(-2150543643/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4260900451/10000000000 : ℝ)*X 0 0+(3728596859/10000000000 : ℝ)*X 0 1+(4858029381/10000000000 : ℝ)*X 0 2+(4260900451/10000000000 : ℝ)*X 1 0+(3728596859/10000000000 : ℝ)*X 1 1+(4858029381/10000000000 : ℝ)*X 1 2+(4260900451/10000000000 : ℝ)*X 2 0+(3728596859/10000000000 : ℝ)*X 2 1+(4858029381/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-376341701/2000000000 : ℝ)*X 0 0+(2544396147/5000000000 : ℝ)*X 0 1+(5585972567/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5258785589/10000000000 : ℝ)*X 1 0+(-823706971/5000000000 : ℝ)*X 1 1+(5585972609/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2629392803/5000000000 : ℝ)*X 2 0+(5585972581/10000000000 : ℝ)*X 2 1+(-1647413959/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4261714649/10000000000 : ℝ)*X 0 0+(968966553/2000000000 : ℝ)*X 0 1+(3742016331/10000000000 : ℝ)*X 0 2+(4261714649/10000000000 : ℝ)*X 1 0+(968966553/2000000000 : ℝ)*X 1 1+(3742016331/10000000000 : ℝ)*X 1 2+(4261714649/10000000000 : ℝ)*X 2 0+(968966553/2000000000 : ℝ)*X 2 1+(3742016331/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (183786891304358213678943/23473000000000000000000000000 : ℝ) := by norm_num
    linear_combination (48656609/100000000000000 : ℝ)*(base1) + (296980869/20000000000000 : ℝ)*(base19) + (1644064639/100000000000000 : ℝ)*(base23) + (127519193/100000000000000 : ℝ)*(upper3) + (137667803/50000000000000 : ℝ)*(upper5) + (35617207712321/2500000000000 : ℝ)*(major0) + (35617207712321/2500000000000 : ℝ)*(major1) + (35617207712321/2500000000000 : ℝ)*(major2) + (1963952771632573/100000000000000 : ℝ)*(sp0) + (196396412162589/10000000000000 : ℝ)*(sp1) + (490990990616399/25000000000000 : ℝ)*(sp2) + (885405781905341/100000000000000 : ℝ)*(sp3) + (12883554271/100000000000000 : ℝ)*(sp4) + (1229725751/25000000000000 : ℝ)*(sp7) + (442705374732477/50000000000000 : ℝ)*(f.failure) + (392793121306047/20000000000000 : ℝ)*(f.sum) + (1472217201331/1173650000000000000000000000 : ℝ)*base66 + (270016830892944881/73353125000000000000000000000000 : ℝ)*base67 + (74362903189827061/18338281250000000000000000000000 : ℝ)*base70 + (1029986609648869/73353125000000000000000000000000 : ℝ)*base72 + (20008061127003/4694600000000000000000000000 : ℝ)*base73 + (212866436489119881/73353125000000000000000000000000 : ℝ)*base75 + (146549959552076131/73353125000000000000000000000000 : ℝ)*base77 + (553237046700573869/73353125000000000000000000000000 : ℝ)*base80 + (66639323998409/23473000000000000000000000000 : ℝ)*base82 + (38530373/5000000000000000000000 : ℝ)*base89 + (38530373/5000000000000000000000 : ℝ)*base91 + (38530373/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (123595257697713247459053/11736500000000000000000000000 : ℝ) := by norm_num
    linear_combination (100261169/5000000000000 : ℝ)*(base19) + (429854897/20000000000000 : ℝ)*(base23) + (272658861/100000000000000 : ℝ)*(upper3) + (28678421/50000000000000 : ℝ)*(lower4) + (224171481/100000000000000 : ℝ)*(upper5) + (72952788869827/5000000000000 : ℝ)*(major0) + (72952788869827/5000000000000 : ℝ)*(major1) + (72952788869827/5000000000000 : ℝ)*(major2) + (12340753933/100000000000000 : ℝ)*(sp1) + (1682729941/12500000000000 : ℝ)*(sp2) + (2011341869255197/100000000000000 : ℝ)*(sp4) + (502831880819471/25000000000000 : ℝ)*(sp5) + (982092899483/48828125000 : ℝ)*(sp6) + (906769334509727/100000000000000 : ℝ)*(sp7) + (906769334509727/100000000000000 : ℝ)*(f.failure) + (2011341869255197/100000000000000 : ℝ)*(f.sum) + (22605915894991/11736500000000000000000000000 : ℝ)*base66 + (3059924680868791/18338281250000000000000000000000 : ℝ)*base68 + (251259041999722039/73353125000000000000000000000000 : ℝ)*base70 + (87154287292262541/18338281250000000000000000000000 : ℝ)*base72 + (30706473604193/11736500000000000000000000000 : ℝ)*base73 + (2433096185484293/36676562500000000000000000000000 : ℝ)*base75 + (91561415293190543/36676562500000000000000000000000 : ℝ)*base77 + (27371414348171793/36676562500000000000000000000000 : ℝ)*base79 + (134242651866329/23473000000000000000000000000 : ℝ)*base82 + (33365623/10000000000000000000000 : ℝ)*base89 + (33365623/10000000000000000000000 : ℝ)*base91 + (33365623/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1481_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160907049/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6473/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2419/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (99/1250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3737/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1481_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1481_s2_0 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-190965567/1000000000 : ℝ)*x 0 + (170892409/312500000 : ℝ)*x 1 + (2594014257/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (190965567/1000000000 : ℝ)^4459 ≤ (5828707061777/50000000000000 : ℝ)^3435 := by
    have hnat : (190965567 : ℕ)^4459*50000000000000^3435 ≤ 5828707061777^3435*1000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190965567 1000000000 5828707061777 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (170892409/312500000 : ℝ)^4459 ≤ (22840236638769/50000000000000 : ℝ)^3435 := by
    have hnat : (170892409 : ℕ)^4459*50000000000000^3435 ≤ 22840236638769^3435*312500000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170892409 312500000 22840236638769 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2594014257/5000000000 : ℝ)^4459 ≤ (8532422517753/20000000000000 : ℝ)^3435 := by
    have hnat : (2594014257 : ℕ)^4459*20000000000000^3435 ≤ 8532422517753^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2594014257 5000000000 8532422517753 20000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-190965567/1000000000 : ℝ), (170892409/312500000 : ℝ), (2594014257/5000000000 : ℝ)] ![(5828707061777/50000000000000 : ℝ), (22840236638769/50000000000000 : ℝ), (8532422517753/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-190965567/1000000000 : ℝ)|^4459 ≤ (5828707061777/50000000000000 : ℝ)^3435
        have hw : |(-190965567/1000000000 : ℝ)|=(190965567/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(170892409/312500000 : ℝ)|^4459 ≤ (22840236638769/50000000000000 : ℝ)^3435
        have hw : |(170892409/312500000 : ℝ)|=(170892409/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2594014257/5000000000 : ℝ)|^4459 ≤ (8532422517753/20000000000000 : ℝ)^3435
        have hw : |(2594014257/5000000000 : ℝ)|=(2594014257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s2_1 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5361324343/10000000000 : ℝ)*x 0 + (-513588899/2500000000 : ℝ)*x 1 + (5188028139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5361324343/10000000000 : ℝ)^4459 ≤ (5565138964247/12500000000000 : ℝ)^3435 := by
    have hnat : (5361324343 : ℕ)^4459*12500000000000^3435 ≤ 5565138964247^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5361324343 10000000000 5565138964247 12500000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (513588899/2500000000 : ℝ)^4459 ≤ (12816779685119/100000000000000 : ℝ)^3435 := by
    have hnat : (513588899 : ℕ)^4459*100000000000000^3435 ≤ 12816779685119^3435*2500000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513588899 2500000000 12816779685119 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5188028139/10000000000 : ℝ)^4459 ≤ (42662108585799/100000000000000 : ℝ)^3435 := by
    have hnat : (5188028139 : ℕ)^4459*100000000000000^3435 ≤ 42662108585799^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5188028139 10000000000 42662108585799 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5361324343/10000000000 : ℝ), (-513588899/2500000000 : ℝ), (5188028139/10000000000 : ℝ)] ![(5565138964247/12500000000000 : ℝ), (12816779685119/100000000000000 : ℝ), (42662108585799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5361324343/10000000000 : ℝ)|^4459 ≤ (5565138964247/12500000000000 : ℝ)^3435
        have hw : |(5361324343/10000000000 : ℝ)|=(5361324343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-513588899/2500000000 : ℝ)|^4459 ≤ (12816779685119/100000000000000 : ℝ)^3435
        have hw : |(-513588899/2500000000 : ℝ)|=(513588899/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5188028139/10000000000 : ℝ)|^4459 ≤ (42662108585799/100000000000000 : ℝ)^3435
        have hw : |(5188028139/10000000000 : ℝ)|=(5188028139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s2_2 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2680662149/5000000000 : ℝ)*x 0 + (2594013997/5000000000 : ℝ)*x 1 + (-2054355847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2680662149/5000000000 : ℝ)^4459 ≤ (11130277807223/25000000000000 : ℝ)^3435 := by
    have hnat : (2680662149 : ℕ)^4459*25000000000000^3435 ≤ 11130277807223^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2680662149 5000000000 11130277807223 25000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2594013997/5000000000 : ℝ)^4459 ≤ (8532421407597/20000000000000 : ℝ)^3435 := by
    have hnat : (2594013997 : ℕ)^4459*20000000000000^3435 ≤ 8532421407597^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2594013997 5000000000 8532421407597 20000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2054355847/10000000000 : ℝ)^4459 ≤ (6408390858943/50000000000000 : ℝ)^3435 := by
    have hnat : (2054355847 : ℕ)^4459*50000000000000^3435 ≤ 6408390858943^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2054355847 10000000000 6408390858943 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2680662149/5000000000 : ℝ), (2594013997/5000000000 : ℝ), (-2054355847/10000000000 : ℝ)] ![(11130277807223/25000000000000 : ℝ), (8532421407597/20000000000000 : ℝ), (6408390858943/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2680662149/5000000000 : ℝ)|^4459 ≤ (11130277807223/25000000000000 : ℝ)^3435
        have hw : |(2680662149/5000000000 : ℝ)|=(2680662149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2594013997/5000000000 : ℝ)|^4459 ≤ (8532421407597/20000000000000 : ℝ)^3435
        have hw : |(2594013997/5000000000 : ℝ)|=(2594013997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2054355847/10000000000 : ℝ)|^4459 ≤ (6408390858943/50000000000000 : ℝ)^3435
        have hw : |(-2054355847/10000000000 : ℝ)|=(2054355847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s2_3 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2140555667/5000000000 : ℝ)*x 0 + (1989911921/5000000000 : ℝ)*x 1 + (287629791/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2140555667/5000000000 : ℝ)^4459 ≤ (16622283432661/50000000000000 : ℝ)^3435 := by
    have hnat : (2140555667 : ℕ)^4459*50000000000000^3435 ≤ 16622283432661^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140555667 5000000000 16622283432661 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1989911921/5000000000 : ℝ)^4459 ≤ (30239887838453/100000000000000 : ℝ)^3435 := by
    have hnat : (1989911921 : ℕ)^4459*100000000000000^3435 ≤ 30239887838453^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989911921 5000000000 30239887838453 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (287629791/625000000 : ℝ)^4459 ≤ (18257772643407/50000000000000 : ℝ)^3435 := by
    have hnat : (287629791 : ℕ)^4459*50000000000000^3435 ≤ 18257772643407^3435*625000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287629791 625000000 18257772643407 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2140555667/5000000000 : ℝ), (1989911921/5000000000 : ℝ), (287629791/625000000 : ℝ)] ![(16622283432661/50000000000000 : ℝ), (30239887838453/100000000000000 : ℝ), (18257772643407/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2140555667/5000000000 : ℝ)|^4459 ≤ (16622283432661/50000000000000 : ℝ)^3435
        have hw : |(2140555667/5000000000 : ℝ)|=(2140555667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1989911921/5000000000 : ℝ)|^4459 ≤ (30239887838453/100000000000000 : ℝ)^3435
        have hw : |(1989911921/5000000000 : ℝ)|=(1989911921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(287629791/625000000 : ℝ)|^4459 ≤ (18257772643407/50000000000000 : ℝ)^3435
        have hw : |(287629791/625000000 : ℝ)|=(287629791/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s2_4 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1909717117/10000000000 : ℝ)*x 0 + (5189843513/10000000000 : ℝ)*x 1 + (546672527/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1909717117/10000000000 : ℝ)^4459 ≤ (5828950523483/50000000000000 : ℝ)^3435 := by
    have hnat : (1909717117 : ℕ)^4459*50000000000000^3435 ≤ 5828950523483^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1909717117 10000000000 5828950523483 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5189843513/10000000000 : ℝ)^4459 ≤ (42681487948217/100000000000000 : ℝ)^3435 := by
    have hnat : (5189843513 : ℕ)^4459*100000000000000^3435 ≤ 42681487948217^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5189843513 10000000000 42681487948217 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (546672527/1000000000 : ℝ)^4459 ≤ (45660610992427/100000000000000 : ℝ)^3435 := by
    have hnat : (546672527 : ℕ)^4459*100000000000000^3435 ≤ 45660610992427^3435*1000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546672527 1000000000 45660610992427 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1909717117/10000000000 : ℝ), (5189843513/10000000000 : ℝ), (546672527/1000000000 : ℝ)] ![(5828950523483/50000000000000 : ℝ), (42681487948217/100000000000000 : ℝ), (45660610992427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1909717117/10000000000 : ℝ)|^4459 ≤ (5828950523483/50000000000000 : ℝ)^3435
        have hw : |(-1909717117/10000000000 : ℝ)|=(1909717117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5189843513/10000000000 : ℝ)|^4459 ≤ (42681487948217/100000000000000 : ℝ)^3435
        have hw : |(5189843513/10000000000 : ℝ)|=(5189843513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(546672527/1000000000 : ℝ)|^4459 ≤ (45660610992427/100000000000000 : ℝ)^3435
        have hw : |(546672527/1000000000 : ℝ)|=(546672527/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s2_5 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661002141/1250000000 : ℝ)*x 0 + (-887829659/5000000000 : ℝ)*x 1 + (5466725283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661002141/1250000000 : ℝ)^4459 ≤ (4373250132647/10000000000000 : ℝ)^3435 := by
    have hnat : (661002141 : ℕ)^4459*10000000000000^3435 ≤ 4373250132647^3435*1250000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661002141 1250000000 4373250132647 10000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (887829659/5000000000 : ℝ)^4459 ≤ (10606887530007/100000000000000 : ℝ)^3435 := by
    have hnat : (887829659 : ℕ)^4459*100000000000000^3435 ≤ 10606887530007^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      887829659 5000000000 10606887530007 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5466725283/10000000000 : ℝ)^4459 ≤ (22830305566689/50000000000000 : ℝ)^3435 := by
    have hnat : (5466725283 : ℕ)^4459*50000000000000^3435 ≤ 22830305566689^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5466725283 10000000000 22830305566689 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661002141/1250000000 : ℝ), (-887829659/5000000000 : ℝ), (5466725283/10000000000 : ℝ)] ![(4373250132647/10000000000000 : ℝ), (10606887530007/100000000000000 : ℝ), (22830305566689/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661002141/1250000000 : ℝ)|^4459 ≤ (4373250132647/10000000000000 : ℝ)^3435
        have hw : |(661002141/1250000000 : ℝ)|=(661002141/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-887829659/5000000000 : ℝ)|^4459 ≤ (10606887530007/100000000000000 : ℝ)^3435
        have hw : |(-887829659/5000000000 : ℝ)|=(887829659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5466725283/10000000000 : ℝ)|^4459 ≤ (22830305566689/50000000000000 : ℝ)^3435
        have hw : |(5466725283/10000000000 : ℝ)|=(5466725283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s2_6 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644008711/5000000000 : ℝ)*x 0 + (5466725327/10000000000 : ℝ)*x 1 + (-55489339/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644008711/5000000000 : ℝ)^4459 ≤ (21866252241353/50000000000000 : ℝ)^3435 := by
    have hnat : (2644008711 : ℕ)^4459*50000000000000^3435 ≤ 21866252241353^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644008711 5000000000 21866252241353 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5466725327/10000000000 : ℝ)^4459 ≤ (45660611610443/100000000000000 : ℝ)^3435 := by
    have hnat : (5466725327 : ℕ)^4459*100000000000000^3435 ≤ 45660611610443^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5466725327 10000000000 45660611610443 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (55489339/312500000 : ℝ)^4459 ≤ (2651720971379/25000000000000 : ℝ)^3435 := by
    have hnat : (55489339 : ℕ)^4459*25000000000000^3435 ≤ 2651720971379^3435*312500000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55489339 312500000 2651720971379 25000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644008711/5000000000 : ℝ), (5466725327/10000000000 : ℝ), (-55489339/312500000 : ℝ)] ![(21866252241353/50000000000000 : ℝ), (45660611610443/100000000000000 : ℝ), (2651720971379/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644008711/5000000000 : ℝ)|^4459 ≤ (21866252241353/50000000000000 : ℝ)^3435
        have hw : |(2644008711/5000000000 : ℝ)|=(2644008711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5466725327/10000000000 : ℝ)|^4459 ≤ (45660611610443/100000000000000 : ℝ)^3435
        have hw : |(5466725327/10000000000 : ℝ)|=(5466725327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-55489339/312500000 : ℝ)|^4459 ≤ (2651720971379/25000000000000 : ℝ)^3435
        have hw : |(-55489339/312500000 : ℝ)|=(55489339/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s2_7 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4281247753/10000000000 : ℝ)*x 0 + (919610023/2000000000 : ℝ)*x 1 + (248993/625000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4281247753/10000000000 : ℝ)^4459 ≤ (8311485505207/25000000000000 : ℝ)^3435 := by
    have hnat : (4281247753 : ℕ)^4459*25000000000000^3435 ≤ 8311485505207^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4281247753 10000000000 8311485505207 25000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (919610023/2000000000 : ℝ)^4459 ≤ (36474077567947/100000000000000 : ℝ)^3435 := by
    have hnat : (919610023 : ℕ)^4459*100000000000000^3435 ≤ 36474077567947^3435*2000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      919610023 2000000000 36474077567947 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (248993/625000 : ℝ)^4459 ≤ (30279980392667/100000000000000 : ℝ)^3435 := by
    have hnat : (248993 : ℕ)^4459*100000000000000^3435 ≤ 30279980392667^3435*625000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      248993 625000 30279980392667 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4281247753/10000000000 : ℝ), (919610023/2000000000 : ℝ), (248993/625000 : ℝ)] ![(8311485505207/25000000000000 : ℝ), (36474077567947/100000000000000 : ℝ), (30279980392667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4281247753/10000000000 : ℝ)|^4459 ≤ (8311485505207/25000000000000 : ℝ)^3435
        have hw : |(4281247753/10000000000 : ℝ)|=(4281247753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(919610023/2000000000 : ℝ)|^4459 ≤ (36474077567947/100000000000000 : ℝ)^3435
        have hw : |(919610023/2000000000 : ℝ)|=(919610023/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(248993/625000 : ℝ)|^4459 ≤ (30279980392667/100000000000000 : ℝ)^3435
        have hw : |(248993/625000 : ℝ)|=(248993/625000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1481_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160907049/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3737/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (99/1250 : ℝ)*pair X i i ≤ pair X i h) :
    (10193/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16127/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3737/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (99/1250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3737/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (99/1250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3737/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (99/1250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3737/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (99/1250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3737/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (99/1250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3737/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (99/1250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (99/1250 : ℝ) ^ (4457/1024 : ℝ) ≤ (1609379015524071/100000000000000000000 : ℝ) := by
    have hpowers : (99/1250 : ℝ)^4457 ≤ (1609379015524071/100000000000000000000 : ℝ)^1024 := by
      have hnat : (99 : ℕ)^4457*100000000000000000000^1024 ≤ 1609379015524071^1024*1250^4457 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        99 1250 1609379015524071 100000000000000000000 4457 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (99/1250 : ℝ)) (X := (1609379015524071/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4457 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3737/20000 : ℝ) ^ (4457/1024 : ℝ) ≤ (13495073853369067/20000000000000000000 : ℝ) := by
    have hpowers : (3737/20000 : ℝ)^4457 ≤ (13495073853369067/20000000000000000000 : ℝ)^1024 := by
      have hnat : (3737 : ℕ)^4457*20000000000000000000^1024 ≤ 13495073853369067^1024*20000^4457 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3737 20000 13495073853369067 20000000000000000000 4457 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3737/20000 : ℝ)) (X := (13495073853369067/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4457 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001609379015524071/50000000000000000000 : ℝ) ≤ (10000073950355991/10000000000000000 : ℝ) ^ (4457/1024 : ℝ) := by
    have hpowers : (50001609379015524071/50000000000000000000 : ℝ)^1024 ≤ (10000073950355991/10000000000000000 : ℝ)^4457 := by
      have hnat : (50001609379015524071 : ℕ)^1024*10000000000000000^4457 ≤ 10000073950355991^4457*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001609379015524071 50000000000000000000 10000073950355991 10000000000000000 1024 4457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000073950355991/10000000000000000 : ℝ)) (X := (50001609379015524071/50000000000000000000 : ℝ)) (by norm_num) 4457 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50034542374141184703/50000000000000000000 : ℝ) ≤ (5000793403274877/5000000000000000 : ℝ) ^ (4457/1024 : ℝ) := by
    have hpowers : (50034542374141184703/50000000000000000000 : ℝ)^1024 ≤ (5000793403274877/5000000000000000 : ℝ)^4457 := by
      have hnat : (50034542374141184703 : ℕ)^1024*5000000000000000^4457 ≤ 5000793403274877^4457*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034542374141184703 50000000000000000000 5000793403274877 5000000000000000 1024 4457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000793403274877/5000000000000000 : ℝ)) (X := (50034542374141184703/50000000000000000000 : ℝ)) (by norm_num) 4457 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10013495073853369067/10000000000000000000 : ℝ) ≤ (10003099662743517/10000000000000000 : ℝ) ^ (4457/1024 : ℝ) := by
    have hpowers : (10013495073853369067/10000000000000000000 : ℝ)^1024 ≤ (10003099662743517/10000000000000000 : ℝ)^4457 := by
      have hnat : (10013495073853369067 : ℕ)^1024*10000000000000000^4457 ≤ 10003099662743517^4457*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10013495073853369067 10000000000000000000 10003099662743517 10000000000000000 1024 4457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003099662743517/10000000000000000 : ℝ)) (X := (10013495073853369067/10000000000000000000 : ℝ)) (by norm_num) 4457 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1609379015524071/100000000000000000000 : ℝ) ≤ ((21525366486694607439/21530000000000000000 : ℝ)+2*(1512856193763/1076500000000000 : ℝ)*(99/1250 : ℝ))^(4457/1024 : ℝ) := by
    rw [show (21525366486694607439/21530000000000000000 : ℝ)+2*(1512856193763/1076500000000000 : ℝ)*(99/1250 : ℝ)=(10000073950355991/10000000000000000 : ℝ) by norm_num, show 1+2*(1609379015524071/100000000000000000000 : ℝ)=(50001609379015524071/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13495073853369067/20000000000000000000 : ℝ)+(1609379015524071/100000000000000000000 : ℝ) ≤ ((21525366486694607439/21530000000000000000 : ℝ)+(1512856193763/1076500000000000 : ℝ)*((3737/20000 : ℝ)+(99/1250 : ℝ)))^(4457/1024 : ℝ) := by
    rw [show (21525366486694607439/21530000000000000000 : ℝ)+(1512856193763/1076500000000000 : ℝ)*((3737/20000 : ℝ)+(99/1250 : ℝ))=(5000793403274877/5000000000000000 : ℝ) by norm_num, show 1+(13495073853369067/20000000000000000000 : ℝ)+(1609379015524071/100000000000000000000 : ℝ)=(50034542374141184703/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13495073853369067/20000000000000000000 : ℝ) ≤ ((21525366486694607439/21530000000000000000 : ℝ)+2*(1512856193763/1076500000000000 : ℝ)*(3737/20000 : ℝ))^(4457/1024 : ℝ) := by
    rw [show (21525366486694607439/21530000000000000000 : ℝ)+2*(1512856193763/1076500000000000 : ℝ)*(3737/20000 : ℝ)=(10003099662743517/10000000000000000 : ℝ) by norm_num, show 1+2*(13495073853369067/20000000000000000000 : ℝ)=(10013495073853369067/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (21525366486694607439/21530000000000000000 : ℝ)*(X 1 0+X 2 0)+(1512856193763/1076500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4457/1024 : ℝ)) (lo := (99/1250 : ℝ)) (hi := (3737/20000 : ℝ)) (c := (21525366486694607439/21530000000000000000 : ℝ)) (alpha := (1512856193763/1076500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (21525366486694607439/21530000000000000000 : ℝ)*(X 0 1+X 2 1)+(1512856193763/1076500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4457/1024 : ℝ)) (lo := (99/1250 : ℝ)) (hi := (3737/20000 : ℝ)) (c := (21525366486694607439/21530000000000000000 : ℝ)) (alpha := (1512856193763/1076500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (21525366486694607439/21530000000000000000 : ℝ)*(X 0 2+X 1 2)+(1512856193763/1076500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4457/1024 : ℝ)) (lo := (99/1250 : ℝ)) (hi := (3737/20000 : ℝ)) (c := (21525366486694607439/21530000000000000000 : ℝ)) (alpha := (1512856193763/1076500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-190965567/1000000000 : ℝ)*X 0 0+(170892409/312500000 : ℝ)*X 0 1+(2594014257/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5361324343/10000000000 : ℝ)*X 1 0+(-513588899/2500000000 : ℝ)*X 1 1+(5188028139/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2680662149/5000000000 : ℝ)*X 2 0+(2594013997/5000000000 : ℝ)*X 2 1+(-2054355847/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2140555667/5000000000 : ℝ)*X 0 0+(1989911921/5000000000 : ℝ)*X 0 1+(287629791/625000000 : ℝ)*X 0 2+(2140555667/5000000000 : ℝ)*X 1 0+(1989911921/5000000000 : ℝ)*X 1 1+(287629791/625000000 : ℝ)*X 1 2+(2140555667/5000000000 : ℝ)*X 2 0+(1989911921/5000000000 : ℝ)*X 2 1+(287629791/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1909717117/10000000000 : ℝ)*X 0 0+(5189843513/10000000000 : ℝ)*X 0 1+(546672527/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((661002141/1250000000 : ℝ)*X 1 0+(-887829659/5000000000 : ℝ)*X 1 1+(5466725283/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2644008711/5000000000 : ℝ)*X 2 0+(5466725327/10000000000 : ℝ)*X 2 1+(-55489339/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4281247753/10000000000 : ℝ)*X 0 0+(919610023/2000000000 : ℝ)*X 0 1+(248993/625000 : ℝ)*X 0 2+(4281247753/10000000000 : ℝ)*X 1 0+(919610023/2000000000 : ℝ)*X 1 1+(248993/625000 : ℝ)*X 1 2+(4281247753/10000000000 : ℝ)*X 2 0+(919610023/2000000000 : ℝ)*X 2 1+(248993/625000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (720515943858087442976338293/269125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1031795173/100000000000000 : ℝ)*(base19) + (5138529/500000000000 : ℝ)*(base23) + (15857623/100000000000000 : ℝ)*(upper2) + (4505881/2500000000000 : ℝ)*(upper3) + (2008847/100000000000000 : ℝ)*(upper4) + (646473870019443/25000000000000 : ℝ)*(major0) + (646473870019443/25000000000000 : ℝ)*(major1) + (646473870019443/25000000000000 : ℝ)*(major2) + (3564710237852867/100000000000000 : ℝ)*(sp0) + (356471575743693/10000000000000 : ℝ)*(sp1) + (111397367547697/3125000000000 : ℝ)*(sp2) + (321413640543249/20000000000000 : ℝ)*(sp3) + (1637844809/25000000000000 : ℝ)*(sp4) + (5878965393/100000000000000 : ℝ)*(sp7) + (803537040840819/50000000000000 : ℝ)*(f.failure) + (3564716789232103/100000000000000 : ℝ)*(f.sum) + (126928021703011/53825000000000000000000000000 : ℝ)*base65 + (4489915215611633523/538250000000000000000000000000000 : ℝ)*base68 + (3440194891120883523/538250000000000000000000000000000 : ℝ)*base70 + (262106201036633523/538250000000000000000000000000000 : ℝ)*base72 + (134245892673089/53825000000000000000000000000 : ℝ)*base74 + (4748481441254883523/538250000000000000000000000000000 : ℝ)*base76 + (6239451897813133523/538250000000000000000000000000000 : ℝ)*base78 + (5796725292170633523/538250000000000000000000000000000 : ℝ)*base80 + (55279026744091/13456250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (64033131/5000000000000000000000 : ℝ)*base89 + (64033131/5000000000000000000000 : ℝ)*base91 + (64033131/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13309336137793458973545969189/1076500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1632524129/100000000000000 : ℝ)*(base19) + (2044926393/100000000000000 : ℝ)*(base23) + (44713901/20000000000000 : ℝ)*(upper3) + (2519121/4000000000000 : ℝ)*(lower4) + (77066517/25000000000000 : ℝ)*(upper5) + (2619943505079417/100000000000000 : ℝ)*(major0) + (2619943505079417/100000000000000 : ℝ)*(major1) + (2619943505079417/100000000000000 : ℝ)*(major2) + (18701077171/100000000000000 : ℝ)*(sp1) + (12687136253/50000000000000 : ℝ)*(sp2) + (3611652458293051/100000000000000 : ℝ)*(sp4) + (3611632124691751/100000000000000 : ℝ)*(sp5) + (451453129886769/12500000000000 : ℝ)*(sp6) + (1628234139748233/100000000000000 : ℝ)*(sp7) + (1628234139748233/100000000000000 : ℝ)*(f.failure) + (3611652458293051/100000000000000 : ℝ)*(f.sum) + (107153114567479/53825000000000000000000000000 : ℝ)*base66 + (4982792426283403063/2153000000000000000000000000000000 : ℝ)*base67 + (9376593302952596937/2153000000000000000000000000000000 : ℝ)*base70 + (8408071549332596937/2153000000000000000000000000000000 : ℝ)*base72 + (124476661696423/26912500000000000000000000000 : ℝ)*base73 + (4478701183651403063/2153000000000000000000000000000000 : ℝ)*base75 + (6585088020435596937/2153000000000000000000000000000000 : ℝ)*base78 + (17845881036981596937/2153000000000000000000000000000000 : ℝ)*base80 + (272583608320479/53825000000000000000000000000 : ℝ)*base82 + (74994417/10000000000000000000000 : ℝ)*base89 + (74994417/10000000000000000000000 : ℝ)*base91 + (74994417/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1481_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160907049/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3737/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (99/1250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10193/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16127/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1481_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1481_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160907049/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10193/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16127/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1481_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1481_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1481_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160907049/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10193/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16127/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1481_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

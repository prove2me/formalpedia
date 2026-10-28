-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1186_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:51:28.285587+00:00
-- url     : https://prove2.me/submissions/db4af821-fdcd-45a0-8763-2b2cd77a9dea

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
theorem support_rectangle_w1186_s6_0 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-85839871/400000000 : ℝ)*x 0 + (337031507/625000000 : ℝ)*x 1 + (42129339/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (85839871/400000000 : ℝ)^8379 ≤ (6522128621211/50000000000000 : ℝ)^6331 := by
    have hnat : (85839871 : ℕ)^8379*50000000000000^6331 ≤ 6522128621211^6331*400000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85839871 400000000 6522128621211 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337031507/625000000 : ℝ)^8379 ≤ (44159895034719/100000000000000 : ℝ)^6331 := by
    have hnat : (337031507 : ℕ)^8379*100000000000000^6331 ≤ 44159895034719^6331*625000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337031507 625000000 44159895034719 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42129339/80000000 : ℝ)^8379 ≤ (21397923855139/50000000000000 : ℝ)^6331 := by
    have hnat : (42129339 : ℕ)^8379*50000000000000^6331 ≤ 21397923855139^6331*80000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42129339 80000000 21397923855139 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-85839871/400000000 : ℝ), (337031507/625000000 : ℝ), (42129339/80000000 : ℝ)] ![(6522128621211/50000000000000 : ℝ), (44159895034719/100000000000000 : ℝ), (21397923855139/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-85839871/400000000 : ℝ)|^8379 ≤ (6522128621211/50000000000000 : ℝ)^6331
        have hw : |(-85839871/400000000 : ℝ)|=(85839871/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337031507/625000000 : ℝ)|^8379 ≤ (44159895034719/100000000000000 : ℝ)^6331
        have hw : |(337031507/625000000 : ℝ)|=(337031507/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42129339/80000000 : ℝ)|^8379 ≤ (21397923855139/50000000000000 : ℝ)^6331
        have hw : |(42129339/80000000 : ℝ)|=(42129339/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s6_1 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672324259/5000000000 : ℝ)*x 0 + (-221006993/1000000000 : ℝ)*x 1 + (263308371/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672324259/5000000000 : ℝ)^8379 ≤ (10910493052139/25000000000000 : ℝ)^6331 := by
    have hnat : (2672324259 : ℕ)^8379*25000000000000^6331 ≤ 10910493052139^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672324259 5000000000 10910493052139 25000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (221006993/1000000000 : ℝ)^8379 ≤ (13562179578207/100000000000000 : ℝ)^6331 := by
    have hnat : (221006993 : ℕ)^8379*100000000000000^6331 ≤ 13562179578207^6331*1000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221006993 1000000000 13562179578207 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263308371/500000000 : ℝ)^8379 ≤ (42795848194271/100000000000000 : ℝ)^6331 := by
    have hnat : (263308371 : ℕ)^8379*100000000000000^6331 ≤ 42795848194271^6331*500000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263308371 500000000 42795848194271 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672324259/5000000000 : ℝ), (-221006993/1000000000 : ℝ), (263308371/500000000 : ℝ)] ![(10910493052139/25000000000000 : ℝ), (13562179578207/100000000000000 : ℝ), (42795848194271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672324259/5000000000 : ℝ)|^8379 ≤ (10910493052139/25000000000000 : ℝ)^6331
        have hw : |(2672324259/5000000000 : ℝ)|=(2672324259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-221006993/1000000000 : ℝ)|^8379 ≤ (13562179578207/100000000000000 : ℝ)^6331
        have hw : |(-221006993/1000000000 : ℝ)|=(221006993/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263308371/500000000 : ℝ)|^8379 ≤ (42795848194271/100000000000000 : ℝ)^6331
        have hw : |(263308371/500000000 : ℝ)|=(263308371/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s6_2 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344648611/10000000000 : ℝ)*x 0 + (2633083637/5000000000 : ℝ)*x 1 + (-221007/1000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344648611/10000000000 : ℝ)^8379 ≤ (43641973213607/100000000000000 : ℝ)^6331 := by
    have hnat : (5344648611 : ℕ)^8379*100000000000000^6331 ≤ 43641973213607^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344648611 10000000000 43641973213607 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633083637/5000000000 : ℝ)^8379 ≤ (42795846623981/100000000000000 : ℝ)^6331 := by
    have hnat : (2633083637 : ℕ)^8379*100000000000000^6331 ≤ 42795846623981^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633083637 5000000000 42795846623981 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (221007/1000000 : ℝ)^8379 ≤ (13562180146721/100000000000000 : ℝ)^6331 := by
    have hnat : (221007 : ℕ)^8379*100000000000000^6331 ≤ 13562180146721^6331*1000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221007 1000000 13562180146721 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344648611/10000000000 : ℝ), (2633083637/5000000000 : ℝ), (-221007/1000000 : ℝ)] ![(43641973213607/100000000000000 : ℝ), (42795846623981/100000000000000 : ℝ), (13562180146721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344648611/10000000000 : ℝ)|^8379 ≤ (43641973213607/100000000000000 : ℝ)^6331
        have hw : |(5344648611/10000000000 : ℝ)|=(5344648611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633083637/5000000000 : ℝ)|^8379 ≤ (42795846623981/100000000000000 : ℝ)^6331
        have hw : |(2633083637/5000000000 : ℝ)|=(2633083637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-221007/1000000 : ℝ)|^8379 ≤ (13562180146721/100000000000000 : ℝ)^6331
        have hw : |(-221007/1000000 : ℝ)|=(221007/1000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s6_3 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (87169959/200000000 : ℝ)*x 0 + (4233555587/10000000000 : ℝ)*x 1 + (2243535343/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (87169959/200000000 : ℝ)^8379 ≤ (33317068958917/100000000000000 : ℝ)^6331 := by
    have hnat : (87169959 : ℕ)^8379*100000000000000^6331 ≤ 33317068958917^6331*200000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87169959 200000000 33317068958917 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4233555587/10000000000 : ℝ)^8379 ≤ (32058931885481/100000000000000 : ℝ)^6331 := by
    have hnat : (4233555587 : ℕ)^8379*100000000000000^6331 ≤ 32058931885481^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4233555587 10000000000 32058931885481 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2243535343/5000000000 : ℝ)^8379 ≤ (4327999892607/12500000000000 : ℝ)^6331 := by
    have hnat : (2243535343 : ℕ)^8379*12500000000000^6331 ≤ 4327999892607^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243535343 5000000000 4327999892607 12500000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(87169959/200000000 : ℝ), (4233555587/10000000000 : ℝ), (2243535343/5000000000 : ℝ)] ![(33317068958917/100000000000000 : ℝ), (32058931885481/100000000000000 : ℝ), (4327999892607/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(87169959/200000000 : ℝ)|^8379 ≤ (33317068958917/100000000000000 : ℝ)^6331
        have hw : |(87169959/200000000 : ℝ)|=(87169959/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4233555587/10000000000 : ℝ)|^8379 ≤ (32058931885481/100000000000000 : ℝ)^6331
        have hw : |(4233555587/10000000000 : ℝ)|=(4233555587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2243535343/5000000000 : ℝ)|^8379 ≤ (4327999892607/12500000000000 : ℝ)^6331
        have hw : |(2243535343/5000000000 : ℝ)|=(2243535343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s6_4 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2146001677/10000000000 : ℝ)*x 0 + (329155409/625000000 : ℝ)*x 1 + (5392183737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2146001677/10000000000 : ℝ)^8379 ≤ (2608859335517/20000000000000 : ℝ)^6331 := by
    have hnat : (2146001677 : ℕ)^8379*20000000000000^6331 ≤ 2608859335517^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2146001677 10000000000 2608859335517 20000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329155409/625000000 : ℝ)^8379 ≤ (42799280536447/100000000000000 : ℝ)^6331 := by
    have hnat : (329155409 : ℕ)^8379*100000000000000^6331 ≤ 42799280536447^6331*625000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329155409 625000000 42799280536447 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392183737/10000000000 : ℝ)^8379 ≤ (22078211388827/50000000000000 : ℝ)^6331 := by
    have hnat : (5392183737 : ℕ)^8379*50000000000000^6331 ≤ 22078211388827^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392183737 10000000000 22078211388827 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2146001677/10000000000 : ℝ), (329155409/625000000 : ℝ), (5392183737/10000000000 : ℝ)] ![(2608859335517/20000000000000 : ℝ), (42799280536447/100000000000000 : ℝ), (22078211388827/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2146001677/10000000000 : ℝ)|^8379 ≤ (2608859335517/20000000000000 : ℝ)^6331
        have hw : |(-2146001677/10000000000 : ℝ)|=(2146001677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329155409/625000000 : ℝ)|^8379 ≤ (42799280536447/100000000000000 : ℝ)^6331
        have hw : |(329155409/625000000 : ℝ)|=(329155409/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392183737/10000000000 : ℝ)|^8379 ≤ (22078211388827/50000000000000 : ℝ)^6331
        have hw : |(5392183737/10000000000 : ℝ)|=(5392183737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s6_5 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656269083/5000000000 : ℝ)*x 0 + (-2084053511/10000000000 : ℝ)*x 1 + (5392183751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656269083/5000000000 : ℝ)^8379 ≤ (43295293349787/100000000000000 : ℝ)^6331 := by
    have hnat : (2656269083 : ℕ)^8379*100000000000000^6331 ≤ 43295293349787^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656269083 5000000000 43295293349787 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2084053511/10000000000 : ℝ)^8379 ≤ (12548283703081/100000000000000 : ℝ)^6331 := by
    have hnat : (2084053511 : ℕ)^8379*100000000000000^6331 ≤ 12548283703081^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084053511 10000000000 12548283703081 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392183751/10000000000 : ℝ)^8379 ≤ (22078211464693/50000000000000 : ℝ)^6331 := by
    have hnat : (5392183751 : ℕ)^8379*50000000000000^6331 ≤ 22078211464693^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392183751 10000000000 22078211464693 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656269083/5000000000 : ℝ), (-2084053511/10000000000 : ℝ), (5392183751/10000000000 : ℝ)] ![(43295293349787/100000000000000 : ℝ), (12548283703081/100000000000000 : ℝ), (22078211464693/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656269083/5000000000 : ℝ)|^8379 ≤ (43295293349787/100000000000000 : ℝ)^6331
        have hw : |(2656269083/5000000000 : ℝ)|=(2656269083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2084053511/10000000000 : ℝ)|^8379 ≤ (12548283703081/100000000000000 : ℝ)^6331
        have hw : |(-2084053511/10000000000 : ℝ)|=(2084053511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392183751/10000000000 : ℝ)|^8379 ≤ (22078211464693/50000000000000 : ℝ)^6331
        have hw : |(5392183751/10000000000 : ℝ)|=(5392183751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s6_6 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312538181/10000000000 : ℝ)*x 0 + (5392183743/10000000000 : ℝ)*x 1 + (-2084053501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312538181/10000000000 : ℝ)^8379 ≤ (43295293511577/100000000000000 : ℝ)^6331 := by
    have hnat : (5312538181 : ℕ)^8379*100000000000000^6331 ≤ 43295293511577^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312538181 10000000000 43295293511577 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392183743/10000000000 : ℝ)^8379 ≤ (22078211421341/50000000000000 : ℝ)^6331 := by
    have hnat : (5392183743 : ℕ)^8379*50000000000000^6331 ≤ 22078211421341^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392183743 10000000000 22078211421341 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2084053501/10000000000 : ℝ)^8379 ≤ (12548283623393/100000000000000 : ℝ)^6331 := by
    have hnat : (2084053501 : ℕ)^8379*100000000000000^6331 ≤ 12548283623393^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084053501 10000000000 12548283623393 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312538181/10000000000 : ℝ), (5392183743/10000000000 : ℝ), (-2084053501/10000000000 : ℝ)] ![(43295293511577/100000000000000 : ℝ), (22078211421341/50000000000000 : ℝ), (12548283623393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312538181/10000000000 : ℝ)|^8379 ≤ (43295293511577/100000000000000 : ℝ)^6331
        have hw : |(5312538181/10000000000 : ℝ)|=(5312538181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392183743/10000000000 : ℝ)|^8379 ≤ (22078211421341/50000000000000 : ℝ)^6331
        have hw : |(5392183743/10000000000 : ℝ)|=(5392183743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2084053501/10000000000 : ℝ)|^8379 ≤ (12548283623393/100000000000000 : ℝ)^6331
        have hw : |(-2084053501/10000000000 : ℝ)|=(2084053501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s6_7 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1089626873/2500000000 : ℝ)*x 0 + (1121607517/2500000000 : ℝ)*x 1 + (1058549677/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089626873/2500000000 : ℝ)^8379 ≤ (4164645686867/12500000000000 : ℝ)^6331 := by
    have hnat : (1089626873 : ℕ)^8379*12500000000000^6331 ≤ 4164645686867^6331*2500000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089626873 2500000000 4164645686867 12500000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1121607517/2500000000 : ℝ)^8379 ≤ (270448882411/781250000000 : ℝ)^6331 := by
    have hnat : (1121607517 : ℕ)^8379*781250000000^6331 ≤ 270448882411^6331*2500000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121607517 2500000000 270448882411 781250000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1058549677/2500000000 : ℝ)^8379 ≤ (8016344384987/25000000000000 : ℝ)^6331 := by
    have hnat : (1058549677 : ℕ)^8379*25000000000000^6331 ≤ 8016344384987^6331*2500000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058549677 2500000000 8016344384987 25000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089626873/2500000000 : ℝ), (1121607517/2500000000 : ℝ), (1058549677/2500000000 : ℝ)] ![(4164645686867/12500000000000 : ℝ), (270448882411/781250000000 : ℝ), (8016344384987/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089626873/2500000000 : ℝ)|^8379 ≤ (4164645686867/12500000000000 : ℝ)^6331
        have hw : |(1089626873/2500000000 : ℝ)|=(1089626873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1121607517/2500000000 : ℝ)|^8379 ≤ (270448882411/781250000000 : ℝ)^6331
        have hw : |(1121607517/2500000000 : ℝ)|=(1121607517/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1058549677/2500000000 : ℝ)|^8379 ≤ (8016344384987/25000000000000 : ℝ)^6331
        have hw : |(1058549677/2500000000 : ℝ)|=(1058549677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1186_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150332923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14107/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5689/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2851/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (88/625 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14107/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5689/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14107/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5689/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14107/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5689/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14107/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5689/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14107/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5689/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14107/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5689/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5689/50000 : ℝ) ^ (4189/1024 : ℝ) ≤ (687868361907073/5000000000000000000 : ℝ) := by
    have hpowers : (5689/50000 : ℝ)^4189 ≤ (687868361907073/5000000000000000000 : ℝ)^1024 := by
      have hnat : (5689 : ℕ)^4189*5000000000000000000^1024 ≤ 687868361907073^1024*50000^4189 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5689 50000 687868361907073 5000000000000000000 4189 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5689/50000 : ℝ)) (X := (687868361907073/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14107/100000 : ℝ) ^ (4189/1024 : ℝ) ≤ (6630099585246777/20000000000000000000 : ℝ) := by
    have hpowers : (14107/100000 : ℝ)^4189 ≤ (6630099585246777/20000000000000000000 : ℝ)^1024 := by
      have hnat : (14107 : ℕ)^4189*20000000000000000000^1024 ≤ 6630099585246777^1024*100000^4189 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14107 100000 6630099585246777 20000000000000000000 4189 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14107/100000 : ℝ)) (X := (6630099585246777/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500687868361907073/2500000000000000000 : ℝ) ≤ (200013450541871/200000000000000 : ℝ) ^ (4189/1024 : ℝ) := by
    have hpowers : (2500687868361907073/2500000000000000000 : ℝ)^1024 ≤ (200013450541871/200000000000000 : ℝ)^4189 := by
      have hnat : (2500687868361907073 : ℕ)^1024*200000000000000^4189 ≤ 200013450541871^4189*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500687868361907073 2500000000000000000 200013450541871 200000000000000 1024 4189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200013450541871/200000000000000 : ℝ)) (X := (2500687868361907073/2500000000000000000 : ℝ)) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009381573032875069/20000000000000000000 : ℝ) ≤ (1000114645844833/1000000000000000 : ℝ) ^ (4189/1024 : ℝ) := by
    have hpowers : (20009381573032875069/20000000000000000000 : ℝ)^1024 ≤ (1000114645844833/1000000000000000 : ℝ)^4189 := by
      have hnat : (20009381573032875069 : ℕ)^1024*1000000000000000^4189 ≤ 1000114645844833^4189*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009381573032875069 20000000000000000000 1000114645844833 1000000000000000 1024 4189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000114645844833/1000000000000000 : ℝ)) (X := (20009381573032875069/20000000000000000000 : ℝ)) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006630099585246777/10000000000000000000 : ℝ) ≤ (1000162038980311/1000000000000000 : ℝ) ^ (4189/1024 : ℝ) := by
    have hpowers : (10006630099585246777/10000000000000000000 : ℝ)^1024 ≤ (1000162038980311/1000000000000000 : ℝ)^4189 := by
      have hnat : (10006630099585246777 : ℕ)^1024*1000000000000000^4189 ≤ 1000162038980311^4189*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006630099585246777 10000000000000000000 1000162038980311 1000000000000000 1024 4189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000162038980311/1000000000000000 : ℝ)) (X := (10006630099585246777/10000000000000000000 : ℝ)) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(687868361907073/5000000000000000000 : ℝ) ≤ ((2728105054452892427/2729000000000000000 : ℝ)+2*(23696567739/13645000000000 : ℝ)*(5689/50000 : ℝ))^(4189/1024 : ℝ) := by
    rw [show (2728105054452892427/2729000000000000000 : ℝ)+2*(23696567739/13645000000000 : ℝ)*(5689/50000 : ℝ)=(200013450541871/200000000000000 : ℝ) by norm_num, show 1+2*(687868361907073/5000000000000000000 : ℝ)=(2500687868361907073/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6630099585246777/20000000000000000000 : ℝ)+(687868361907073/5000000000000000000 : ℝ) ≤ ((2728105054452892427/2729000000000000000 : ℝ)+(23696567739/13645000000000 : ℝ)*((14107/100000 : ℝ)+(5689/50000 : ℝ)))^(4189/1024 : ℝ) := by
    rw [show (2728105054452892427/2729000000000000000 : ℝ)+(23696567739/13645000000000 : ℝ)*((14107/100000 : ℝ)+(5689/50000 : ℝ))=(1000114645844833/1000000000000000 : ℝ) by norm_num, show 1+(6630099585246777/20000000000000000000 : ℝ)+(687868361907073/5000000000000000000 : ℝ)=(20009381573032875069/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6630099585246777/20000000000000000000 : ℝ) ≤ ((2728105054452892427/2729000000000000000 : ℝ)+2*(23696567739/13645000000000 : ℝ)*(14107/100000 : ℝ))^(4189/1024 : ℝ) := by
    rw [show (2728105054452892427/2729000000000000000 : ℝ)+2*(23696567739/13645000000000 : ℝ)*(14107/100000 : ℝ)=(1000162038980311/1000000000000000 : ℝ) by norm_num, show 1+2*(6630099585246777/20000000000000000000 : ℝ)=(10006630099585246777/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2728105054452892427/2729000000000000000 : ℝ)*(X 1 0+X 2 0)+(23696567739/13645000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4189/1024 : ℝ)) (lo := (5689/50000 : ℝ)) (hi := (14107/100000 : ℝ)) (c := (2728105054452892427/2729000000000000000 : ℝ)) (alpha := (23696567739/13645000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2728105054452892427/2729000000000000000 : ℝ)*(X 0 1+X 2 1)+(23696567739/13645000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4189/1024 : ℝ)) (lo := (5689/50000 : ℝ)) (hi := (14107/100000 : ℝ)) (c := (2728105054452892427/2729000000000000000 : ℝ)) (alpha := (23696567739/13645000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2728105054452892427/2729000000000000000 : ℝ)*(X 0 2+X 1 2)+(23696567739/13645000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4189/1024 : ℝ)) (lo := (5689/50000 : ℝ)) (hi := (14107/100000 : ℝ)) (c := (2728105054452892427/2729000000000000000 : ℝ)) (alpha := (23696567739/13645000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-85839871/400000000 : ℝ)*X 0 0+(337031507/625000000 : ℝ)*X 0 1+(42129339/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672324259/5000000000 : ℝ)*X 1 0+(-221006993/1000000000 : ℝ)*X 1 1+(263308371/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344648611/10000000000 : ℝ)*X 2 0+(2633083637/5000000000 : ℝ)*X 2 1+(-221007/1000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((87169959/200000000 : ℝ)*X 0 0+(4233555587/10000000000 : ℝ)*X 0 1+(2243535343/5000000000 : ℝ)*X 0 2+(87169959/200000000 : ℝ)*X 1 0+(4233555587/10000000000 : ℝ)*X 1 1+(2243535343/5000000000 : ℝ)*X 1 2+(87169959/200000000 : ℝ)*X 2 0+(4233555587/10000000000 : ℝ)*X 2 1+(2243535343/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2146001677/10000000000 : ℝ)*X 0 0+(329155409/625000000 : ℝ)*X 0 1+(5392183737/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656269083/5000000000 : ℝ)*X 1 0+(-2084053511/10000000000 : ℝ)*X 1 1+(5392183751/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312538181/10000000000 : ℝ)*X 2 0+(5392183743/10000000000 : ℝ)*X 2 1+(-2084053501/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1089626873/2500000000 : ℝ)*X 0 0+(1121607517/2500000000 : ℝ)*X 0 1+(1058549677/2500000000 : ℝ)*X 0 2+(1089626873/2500000000 : ℝ)*X 1 0+(1121607517/2500000000 : ℝ)*X 1 1+(1058549677/2500000000 : ℝ)*X 1 2+(1089626873/2500000000 : ℝ)*X 2 0+(1121607517/2500000000 : ℝ)*X 2 1+(1058549677/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (764767949919798784542077679/136450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (991427473/100000000000000 : ℝ)*(base19) + (112615421/12500000000000 : ℝ)*(base23) + (136181173/100000000000000 : ℝ)*(lower2) + (256060933/100000000000000 : ℝ)*(upper3) + (887293/6250000000000 : ℝ)*(lower4) + (5929984820330053/100000000000000 : ℝ)*(major0) + (5929984820330053/100000000000000 : ℝ)*(major1) + (5929984820330053/100000000000000 : ℝ)*(major2) + (7915381406925181/100000000000000 : ℝ)*(sp0) + (7915400165594829/100000000000000 : ℝ)*(sp1) + (3957700128049467/50000000000000 : ℝ)*(sp2) + (1972274826749773/50000000000000 : ℝ)*(sp3) + (19750097121/100000000000000 : ℝ)*(sp4) + (4660828323/25000000000000 : ℝ)*(sp7) + (986142074203209/25000000000000 : ℝ)*(f.failure) + (3957700578511151/50000000000000 : ℝ)*(f.sum) + (511105197693/68225000000000000000000000 : ℝ)*base66 + (3942103345118991369/272900000000000000000000000000000 : ℝ)*base68 + (4138568118599991369/272900000000000000000000000000000 : ℝ)*base70 + (38955552121791369/272900000000000000000000000000000 : ℝ)*base72 + (513158532287/85281250000000000000000000 : ℝ)*base74 + (5810184355531191369/272900000000000000000000000000000 : ℝ)*base76 + (1261101975192591369/272900000000000000000000000000000 : ℝ)*base78 + (1452873781796991369/272900000000000000000000000000000 : ℝ)*base80 + (12422643689/3411250000000000000000000 : ℝ)*base82 + (20050093/2500000000000000000000 : ℝ)*base90 + (20050093/2500000000000000000000 : ℝ)*base92 + (20050093/2500000000000000000000 : ℝ)*base94 + (1/50000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1879586320584059231397/341125000000000000000000000 : ℝ) := by norm_num
    linear_combination (1037055149/100000000000000 : ℝ)*(base19) + (284975783/25000000000000 : ℝ)*(base23) + (118340857/100000000000000 : ℝ)*(upper3) + (33438929/100000000000000 : ℝ)*(lower4) + (11122001/10000000000000 : ℝ)*(upper5) + (5960120233303293/100000000000000 : ℝ)*(major0) + (5960120233303293/100000000000000 : ℝ)*(major1) + (5960120233303293/100000000000000 : ℝ)*(major2) + (5882618147/20000000000000 : ℝ)*(sp1) + (16149345551/50000000000000 : ℝ)*(sp2) + (994453275270379/12500000000000 : ℝ)*(sp4) + (1988898938004287/25000000000000 : ℝ)*(sp5) + (3977796381784399/50000000000000 : ℝ)*(sp6) + (247788380048631/6250000000000 : ℝ)*(sp7) + (247788380048631/6250000000000 : ℝ)*(f.failure) + (994453275270379/12500000000000 : ℝ)*(f.sum) + (1715374025491/682250000000000000000000000 : ℝ)*base66 + (1156106355835137889/272900000000000000000000000000000 : ℝ)*base68 + (314913560141537889/272900000000000000000000000000000 : ℝ)*base70 + (58151768537737889/272900000000000000000000000000000 : ℝ)*base72 + (2635783231021/1364500000000000000000000000 : ℝ)*base74 + (3585699283312862111/272900000000000000000000000000000 : ℝ)*base75 + (1643684161782462111/272900000000000000000000000000000 : ℝ)*base77 + (4874218035768262111/272900000000000000000000000000000 : ℝ)*base79 + (6553280223911/1364500000000000000000000000 : ℝ)*base82 + (871587/625000000000000000000 : ℝ)*base90 + (871587/625000000000000000000 : ℝ)*base92 + (871587/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1186_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150332923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14107/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5689/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2851/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (88/625 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1186_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1186_s7_0 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2146018593/10000000000 : ℝ)*x 0 + (1348060901/2500000000 : ℝ)*x 1 + (1053282713/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2146018593/10000000000 : ℝ)^8379 ≤ (6522216381051/50000000000000 : ℝ)^6331 := by
    have hnat : (2146018593 : ℕ)^8379*50000000000000^6331 ≤ 6522216381051^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2146018593 10000000000 6522216381051 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348060901/2500000000 : ℝ)^8379 ≤ (22078535808631/50000000000000 : ℝ)^6331 := by
    have hnat : (1348060901 : ℕ)^8379*50000000000000^6331 ≤ 22078535808631^6331*2500000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348060901 2500000000 22078535808631 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053282713/2000000000 : ℝ)^8379 ≤ (8559699120793/20000000000000 : ℝ)^6331 := by
    have hnat : (1053282713 : ℕ)^8379*20000000000000^6331 ≤ 8559699120793^6331*2000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053282713 2000000000 8559699120793 20000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2146018593/10000000000 : ℝ), (1348060901/2500000000 : ℝ), (1053282713/2000000000 : ℝ)] ![(6522216381051/50000000000000 : ℝ), (22078535808631/50000000000000 : ℝ), (8559699120793/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2146018593/10000000000 : ℝ)|^8379 ≤ (6522216381051/50000000000000 : ℝ)^6331
        have hw : |(-2146018593/10000000000 : ℝ)|=(2146018593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348060901/2500000000 : ℝ)|^8379 ≤ (22078535808631/50000000000000 : ℝ)^6331
        have hw : |(1348060901/2500000000 : ℝ)|=(1348060901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053282713/2000000000 : ℝ)|^8379 ≤ (8559699120793/20000000000000 : ℝ)^6331
        have hw : |(1053282713/2000000000 : ℝ)|=(1053282713/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s7_1 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344583039/10000000000 : ℝ)*x 0 + (-1104915543/5000000000 : ℝ)*x 1 + (1053282713/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344583039/10000000000 : ℝ)^8379 ≤ (43641264578497/100000000000000 : ℝ)^6331 := by
    have hnat : (5344583039 : ℕ)^8379*100000000000000^6331 ≤ 43641264578497^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344583039 10000000000 43641264578497 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1104915543/5000000000 : ℝ)^8379 ≤ (6780119904421/50000000000000 : ℝ)^6331 := by
    have hnat : (1104915543 : ℕ)^8379*50000000000000^6331 ≤ 6780119904421^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104915543 5000000000 6780119904421 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053282713/2000000000 : ℝ)^8379 ≤ (8559699120793/20000000000000 : ℝ)^6331 := by
    have hnat : (1053282713 : ℕ)^8379*20000000000000^6331 ≤ 8559699120793^6331*2000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053282713 2000000000 8559699120793 20000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344583039/10000000000 : ℝ), (-1104915543/5000000000 : ℝ), (1053282713/2000000000 : ℝ)] ![(43641264578497/100000000000000 : ℝ), (6780119904421/50000000000000 : ℝ), (8559699120793/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344583039/10000000000 : ℝ)|^8379 ≤ (43641264578497/100000000000000 : ℝ)^6331
        have hw : |(5344583039/10000000000 : ℝ)|=(5344583039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1104915543/5000000000 : ℝ)|^8379 ≤ (6780119904421/50000000000000 : ℝ)^6331
        have hw : |(-1104915543/5000000000 : ℝ)|=(1104915543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053282713/2000000000 : ℝ)|^8379 ≤ (8559699120793/20000000000000 : ℝ)^6331
        have hw : |(1053282713/2000000000 : ℝ)|=(1053282713/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s7_2 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672291519/5000000000 : ℝ)*x 0 + (2633206783/5000000000 : ℝ)*x 1 + (-1104915543/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672291519/5000000000 : ℝ)^8379 ≤ (4364126456769/10000000000000 : ℝ)^6331 := by
    have hnat : (2672291519 : ℕ)^8379*10000000000000^6331 ≤ 4364126456769^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672291519 5000000000 4364126456769 10000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633206783/5000000000 : ℝ)^8379 ≤ (42798495614721/100000000000000 : ℝ)^6331 := by
    have hnat : (2633206783 : ℕ)^8379*100000000000000^6331 ≤ 42798495614721^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633206783 5000000000 42798495614721 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1104915543/5000000000 : ℝ)^8379 ≤ (6780119904421/50000000000000 : ℝ)^6331 := by
    have hnat : (1104915543 : ℕ)^8379*50000000000000^6331 ≤ 6780119904421^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104915543 5000000000 6780119904421 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672291519/5000000000 : ℝ), (2633206783/5000000000 : ℝ), (-1104915543/5000000000 : ℝ)] ![(4364126456769/10000000000000 : ℝ), (42798495614721/100000000000000 : ℝ), (6780119904421/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672291519/5000000000 : ℝ)|^8379 ≤ (4364126456769/10000000000000 : ℝ)^6331
        have hw : |(2672291519/5000000000 : ℝ)|=(2672291519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633206783/5000000000 : ℝ)|^8379 ≤ (42798495614721/100000000000000 : ℝ)^6331
        have hw : |(2633206783/5000000000 : ℝ)|=(2633206783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1104915543/5000000000 : ℝ)|^8379 ≤ (6780119904421/50000000000000 : ℝ)^6331
        have hw : |(-1104915543/5000000000 : ℝ)|=(1104915543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s7_3 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4358510641/10000000000 : ℝ)*x 0 + (423406261/1000000000 : ℝ)*x 1 + (4486560521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4358510641/10000000000 : ℝ)^8379 ≤ (33317197353253/100000000000000 : ℝ)^6331 := by
    have hnat : (4358510641 : ℕ)^8379*100000000000000^6331 ≤ 33317197353253^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4358510641 10000000000 33317197353253 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (423406261/1000000000 : ℝ)^8379 ≤ (32064013476773/100000000000000 : ℝ)^6331 := by
    have hnat : (423406261 : ℕ)^8379*100000000000000^6331 ≤ 32064013476773^6331*1000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423406261 1000000000 32064013476773 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4486560521/10000000000 : ℝ)^8379 ≤ (34618789151121/100000000000000 : ℝ)^6331 := by
    have hnat : (4486560521 : ℕ)^8379*100000000000000^6331 ≤ 34618789151121^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486560521 10000000000 34618789151121 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4358510641/10000000000 : ℝ), (423406261/1000000000 : ℝ), (4486560521/10000000000 : ℝ)] ![(33317197353253/100000000000000 : ℝ), (32064013476773/100000000000000 : ℝ), (34618789151121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4358510641/10000000000 : ℝ)|^8379 ≤ (33317197353253/100000000000000 : ℝ)^6331
        have hw : |(4358510641/10000000000 : ℝ)|=(4358510641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(423406261/1000000000 : ℝ)|^8379 ≤ (32064013476773/100000000000000 : ℝ)^6331
        have hw : |(423406261/1000000000 : ℝ)|=(423406261/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4486560521/10000000000 : ℝ)|^8379 ≤ (34618789151121/100000000000000 : ℝ)^6331
        have hw : |(4486560521/10000000000 : ℝ)|=(4486560521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s7_4 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1073011681/5000000000 : ℝ)*x 0 + (210669211/400000000 : ℝ)*x 1 + (2695962879/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073011681/5000000000 : ℝ)^8379 ≤ (3261117781861/25000000000000 : ℝ)^6331 := by
    have hnat : (1073011681 : ℕ)^8379*25000000000000^6331 ≤ 3261117781861^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073011681 5000000000 3261117781861 25000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210669211/400000000 : ℝ)^8379 ≤ (2675118877099/6250000000000 : ℝ)^6331 := by
    have hnat : (210669211 : ℕ)^8379*6250000000000^6331 ≤ 2675118877099^6331*400000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210669211 400000000 2675118877099 6250000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695962879/5000000000 : ℝ)^8379 ≤ (22076813411667/50000000000000 : ℝ)^6331 := by
    have hnat : (2695962879 : ℕ)^8379*50000000000000^6331 ≤ 22076813411667^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695962879 5000000000 22076813411667 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1073011681/5000000000 : ℝ), (210669211/400000000 : ℝ), (2695962879/5000000000 : ℝ)] ![(3261117781861/25000000000000 : ℝ), (2675118877099/6250000000000 : ℝ), (22076813411667/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1073011681/5000000000 : ℝ)|^8379 ≤ (3261117781861/25000000000000 : ℝ)^6331
        have hw : |(-1073011681/5000000000 : ℝ)|=(1073011681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210669211/400000000 : ℝ)|^8379 ≤ (2675118877099/6250000000000 : ℝ)^6331
        have hw : |(210669211/400000000 : ℝ)|=(210669211/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695962879/5000000000 : ℝ)|^8379 ≤ (22076813411667/50000000000000 : ℝ)^6331
        have hw : |(2695962879/5000000000 : ℝ)|=(2695962879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s7_5 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (20752349/39062500 : ℝ)*x 0 + (-16674551/80000000 : ℝ)*x 1 + (5391925757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20752349/39062500 : ℝ)^8379 ≤ (21647987393/50000000000 : ℝ)^6331 := by
    have hnat : (20752349 : ℕ)^8379*50000000000^6331 ≤ 21647987393^6331*39062500^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20752349 39062500 21647987393 50000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16674551/80000000 : ℝ)^8379 ≤ (12550398391023/100000000000000 : ℝ)^6331 := by
    have hnat : (16674551 : ℕ)^8379*100000000000000^6331 ≤ 12550398391023^6331*80000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16674551 80000000 12550398391023 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391925757/10000000000 : ℝ)^8379 ≤ (2759601675781/6250000000000 : ℝ)^6331 := by
    have hnat : (5391925757 : ℕ)^8379*6250000000000^6331 ≤ 2759601675781^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391925757 10000000000 2759601675781 6250000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20752349/39062500 : ℝ), (-16674551/80000000 : ℝ), (5391925757/10000000000 : ℝ)] ![(21647987393/50000000000 : ℝ), (12550398391023/100000000000000 : ℝ), (2759601675781/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20752349/39062500 : ℝ)|^8379 ≤ (21647987393/50000000000 : ℝ)^6331
        have hw : |(20752349/39062500 : ℝ)|=(20752349/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-16674551/80000000 : ℝ)|^8379 ≤ (12550398391023/100000000000000 : ℝ)^6331
        have hw : |(-16674551/80000000 : ℝ)|=(16674551/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391925757/10000000000 : ℝ)|^8379 ≤ (2759601675781/6250000000000 : ℝ)^6331
        have hw : |(5391925757/10000000000 : ℝ)|=(5391925757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s7_6 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (332037583/625000000 : ℝ)*x 0 + (539192577/1000000000 : ℝ)*x 1 + (-2084318879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332037583/625000000 : ℝ)^8379 ≤ (1731838984537/4000000000000 : ℝ)^6331 := by
    have hnat : (332037583 : ℕ)^8379*4000000000000^6331 ≤ 1731838984537^6331*625000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332037583 625000000 1731838984537 4000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539192577/1000000000 : ℝ)^8379 ≤ (11038406738347/25000000000000 : ℝ)^6331 := by
    have hnat : (539192577 : ℕ)^8379*25000000000000^6331 ≤ 11038406738347^6331*1000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539192577 1000000000 11038406738347 25000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2084318879/10000000000 : ℝ)^8379 ≤ (125503984229/1000000000000 : ℝ)^6331 := by
    have hnat : (2084318879 : ℕ)^8379*1000000000000^6331 ≤ 125503984229^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084318879 10000000000 125503984229 1000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(332037583/625000000 : ℝ), (539192577/1000000000 : ℝ), (-2084318879/10000000000 : ℝ)] ![(1731838984537/4000000000000 : ℝ), (11038406738347/25000000000000 : ℝ), (125503984229/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(332037583/625000000 : ℝ)|^8379 ≤ (1731838984537/4000000000000 : ℝ)^6331
        have hw : |(332037583/625000000 : ℝ)|=(332037583/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539192577/1000000000 : ℝ)|^8379 ≤ (11038406738347/25000000000000 : ℝ)^6331
        have hw : |(539192577/1000000000 : ℝ)|=(539192577/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2084318879/10000000000 : ℝ)|^8379 ≤ (125503984229/1000000000000 : ℝ)^6331
        have hw : |(-2084318879/10000000000 : ℝ)|=(2084318879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s7_7 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4358520239/10000000000 : ℝ)*x 0 + (2242962507/5000000000 : ℝ)*x 1 + (2117350209/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4358520239/10000000000 : ℝ)^8379 ≤ (16658647227957/50000000000000 : ℝ)^6331 := by
    have hnat : (4358520239 : ℕ)^8379*50000000000000^6331 ≤ 16658647227957^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4358520239 10000000000 16658647227957 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2242962507/5000000000 : ℝ)^8379 ≤ (1730614969577/5000000000000 : ℝ)^6331 := by
    have hnat : (2242962507 : ℕ)^8379*5000000000000^6331 ≤ 1730614969577^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242962507 5000000000 1730614969577 5000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2117350209/5000000000 : ℝ)^8379 ≤ (32070406128237/100000000000000 : ℝ)^6331 := by
    have hnat : (2117350209 : ℕ)^8379*100000000000000^6331 ≤ 32070406128237^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117350209 5000000000 32070406128237 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4358520239/10000000000 : ℝ), (2242962507/5000000000 : ℝ), (2117350209/5000000000 : ℝ)] ![(16658647227957/50000000000000 : ℝ), (1730614969577/5000000000000 : ℝ), (32070406128237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4358520239/10000000000 : ℝ)|^8379 ≤ (16658647227957/50000000000000 : ℝ)^6331
        have hw : |(4358520239/10000000000 : ℝ)|=(4358520239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2242962507/5000000000 : ℝ)|^8379 ≤ (1730614969577/5000000000000 : ℝ)^6331
        have hw : |(2242962507/5000000000 : ℝ)|=(2242962507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2117350209/5000000000 : ℝ)|^8379 ≤ (32070406128237/100000000000000 : ℝ)^6331
        have hw : |(2117350209/5000000000 : ℝ)|=(2117350209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1186_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150332923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (88/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2851/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11409/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (563/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (88/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2851/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (88/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2851/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (88/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2851/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (88/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2851/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (88/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2851/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (88/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2851/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2851/25000 : ℝ) ^ (4189/1024 : ℝ) ≤ (2777285145008181/20000000000000000000 : ℝ) := by
    have hpowers : (2851/25000 : ℝ)^4189 ≤ (2777285145008181/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2851 : ℕ)^4189*20000000000000000000^1024 ≤ 2777285145008181^1024*25000^4189 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2851 25000 2777285145008181 20000000000000000000 4189 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2851/25000 : ℝ)) (X := (2777285145008181/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (88/625 : ℝ) ^ (4189/1024 : ℝ) ≤ (8222927381864769/25000000000000000000 : ℝ) := by
    have hpowers : (88/625 : ℝ)^4189 ≤ (8222927381864769/25000000000000000000 : ℝ)^1024 := by
      have hnat : (88 : ℕ)^4189*25000000000000000000^1024 ≤ 8222927381864769^1024*625^4189 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        88 625 8222927381864769 25000000000000000000 4189 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (88/625 : ℝ)) (X := (8222927381864769/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002777285145008181/10000000000000000000 : ℝ) ≤ (10000678835438971/10000000000000000 : ℝ) ^ (4189/1024 : ℝ) := by
    have hpowers : (10002777285145008181/10000000000000000000 : ℝ)^1024 ≤ (10000678835438971/10000000000000000 : ℝ)^4189 := by
      have hnat : (10002777285145008181 : ℕ)^1024*10000000000000000^4189 ≤ 10000678835438971^4189*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002777285145008181 10000000000000000000 10000678835438971 10000000000000000 1024 4189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000678835438971/10000000000000000 : ℝ)) (X := (10002777285145008181/10000000000000000000 : ℝ)) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046778135252499981/100000000000000000000 : ℝ) ≤ (10001143288325799/10000000000000000 : ℝ) ^ (4189/1024 : ℝ) := by
    have hpowers : (100046778135252499981/100000000000000000000 : ℝ)^1024 ≤ (10001143288325799/10000000000000000 : ℝ)^4189 := by
      have hnat : (100046778135252499981 : ℕ)^1024*10000000000000000^4189 ≤ 10001143288325799^4189*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046778135252499981 100000000000000000000 10001143288325799 10000000000000000 1024 4189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001143288325799/10000000000000000 : ℝ)) (X := (100046778135252499981/100000000000000000000 : ℝ)) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508222927381864769/12500000000000000000 : ℝ) ≤ (10001607741212627/10000000000000000 : ℝ) ^ (4189/1024 : ℝ) := by
    have hpowers : (12508222927381864769/12500000000000000000 : ℝ)^1024 ≤ (10001607741212627/10000000000000000 : ℝ)^4189 := by
      have hnat : (12508222927381864769 : ℕ)^1024*10000000000000000^4189 ≤ 10001607741212627^4189*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508222927381864769 12500000000000000000 10001607741212627 10000000000000000 1024 4189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001607741212627/10000000000000000 : ℝ)) (X := (12508222927381864769/12500000000000000000 : ℝ)) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2777285145008181/20000000000000000000 : ℝ) ≤ ((6687805830547978343/6690000000000000000 : ℝ)+2*(116113221707/66900000000000 : ℝ)*(2851/25000 : ℝ))^(4189/1024 : ℝ) := by
    rw [show (6687805830547978343/6690000000000000000 : ℝ)+2*(116113221707/66900000000000 : ℝ)*(2851/25000 : ℝ)=(10000678835438971/10000000000000000 : ℝ) by norm_num, show 1+2*(2777285145008181/20000000000000000000 : ℝ)=(10002777285145008181/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8222927381864769/25000000000000000000 : ℝ)+(2777285145008181/20000000000000000000 : ℝ) ≤ ((6687805830547978343/6690000000000000000 : ℝ)+(116113221707/66900000000000 : ℝ)*((88/625 : ℝ)+(2851/25000 : ℝ)))^(4189/1024 : ℝ) := by
    rw [show (6687805830547978343/6690000000000000000 : ℝ)+(116113221707/66900000000000 : ℝ)*((88/625 : ℝ)+(2851/25000 : ℝ))=(10001143288325799/10000000000000000 : ℝ) by norm_num, show 1+(8222927381864769/25000000000000000000 : ℝ)+(2777285145008181/20000000000000000000 : ℝ)=(100046778135252499981/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8222927381864769/25000000000000000000 : ℝ) ≤ ((6687805830547978343/6690000000000000000 : ℝ)+2*(116113221707/66900000000000 : ℝ)*(88/625 : ℝ))^(4189/1024 : ℝ) := by
    rw [show (6687805830547978343/6690000000000000000 : ℝ)+2*(116113221707/66900000000000 : ℝ)*(88/625 : ℝ)=(10001607741212627/10000000000000000 : ℝ) by norm_num, show 1+2*(8222927381864769/25000000000000000000 : ℝ)=(12508222927381864769/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6687805830547978343/6690000000000000000 : ℝ)*(X 1 0+X 2 0)+(116113221707/66900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4189/1024 : ℝ)) (lo := (2851/25000 : ℝ)) (hi := (88/625 : ℝ)) (c := (6687805830547978343/6690000000000000000 : ℝ)) (alpha := (116113221707/66900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6687805830547978343/6690000000000000000 : ℝ)*(X 0 1+X 2 1)+(116113221707/66900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4189/1024 : ℝ)) (lo := (2851/25000 : ℝ)) (hi := (88/625 : ℝ)) (c := (6687805830547978343/6690000000000000000 : ℝ)) (alpha := (116113221707/66900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6687805830547978343/6690000000000000000 : ℝ)*(X 0 2+X 1 2)+(116113221707/66900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4189/1024 : ℝ)) (lo := (2851/25000 : ℝ)) (hi := (88/625 : ℝ)) (c := (6687805830547978343/6690000000000000000 : ℝ)) (alpha := (116113221707/66900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2146018593/10000000000 : ℝ)*X 0 0+(1348060901/2500000000 : ℝ)*X 0 1+(1053282713/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344583039/10000000000 : ℝ)*X 1 0+(-1104915543/5000000000 : ℝ)*X 1 1+(1053282713/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672291519/5000000000 : ℝ)*X 2 0+(2633206783/5000000000 : ℝ)*X 2 1+(-1104915543/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4358510641/10000000000 : ℝ)*X 0 0+(423406261/1000000000 : ℝ)*X 0 1+(4486560521/10000000000 : ℝ)*X 0 2+(4358510641/10000000000 : ℝ)*X 1 0+(423406261/1000000000 : ℝ)*X 1 1+(4486560521/10000000000 : ℝ)*X 1 2+(4358510641/10000000000 : ℝ)*X 2 0+(423406261/1000000000 : ℝ)*X 2 1+(4486560521/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1073011681/5000000000 : ℝ)*X 0 0+(210669211/400000000 : ℝ)*X 0 1+(2695962879/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((20752349/39062500 : ℝ)*X 1 0+(-16674551/80000000 : ℝ)*X 1 1+(5391925757/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((332037583/625000000 : ℝ)*X 2 0+(539192577/1000000000 : ℝ)*X 2 1+(-2084318879/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4358520239/10000000000 : ℝ)*X 0 0+(2242962507/5000000000 : ℝ)*X 0 1+(2117350209/5000000000 : ℝ)*X 0 2+(4358520239/10000000000 : ℝ)*X 1 0+(2242962507/5000000000 : ℝ)*X 1 1+(2117350209/5000000000 : ℝ)*X 1 2+(4358520239/10000000000 : ℝ)*X 2 0+(2242962507/5000000000 : ℝ)*X 2 1+(2117350209/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (171440454355115624595085917/22300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (752315397/50000000000000 : ℝ)*(base19) + (699770267/50000000000000 : ℝ)*(base23) + (55371629/100000000000000 : ℝ)*(lower2) + (12107819/6250000000000 : ℝ)*(upper3) + (58536643/50000000000000 : ℝ)*(upper5) + (1190778387887273/20000000000000 : ℝ)*(major0) + (1190778387887273/20000000000000 : ℝ)*(major1) + (1190778387887273/20000000000000 : ℝ)*(major2) + (1986817807822689/25000000000000 : ℝ)*(sp0) + (1589462207555363/20000000000000 : ℝ)*(sp1) + (317892445714683/4000000000000 : ℝ)*(sp2) + (3960448828638137/100000000000000 : ℝ)*(sp3) + (10327779213/25000000000000 : ℝ)*(sp4) + (4450312643/20000000000000 : ℝ)*(sp7) + (495058885025169/12500000000000 : ℝ)*(f.failure) + (7947312542407609/100000000000000 : ℝ)*(f.sum) + (3319776948419/669000000000000000000000000 : ℝ)*base66 + (5702651604771361/133800000000000000000000000000000 : ℝ)*base68 + (2046253764130971361/133800000000000000000000000000000 : ℝ)*base70 + (5198022630171361/133800000000000000000000000000000 : ℝ)*base72 + (1042531066799/669000000000000000000000000 : ℝ)*base74 + (3391521314373171361/133800000000000000000000000000000 : ℝ)*base76 + (2683503806727171361/133800000000000000000000000000000 : ℝ)*base78 + (770813937983571361/133800000000000000000000000000000 : ℝ)*base80 + (1901671204591/334500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (21838987/1250000000000000000000 : ℝ)*base89 + (21838987/1250000000000000000000 : ℝ)*base91 + (21838987/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1121562969934487554528079841/111500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1825991343/100000000000000 : ℝ)*(base19) + (992349757/50000000000000 : ℝ)*(base23) + (49722379/25000000000000 : ℝ)*(upper3) + (83575603/100000000000000 : ℝ)*(lower4) + (196277517/100000000000000 : ℝ)*(upper5) + (5984003735448087/100000000000000 : ℝ)*(major0) + (5984003735448087/100000000000000 : ℝ)*(major1) + (5984003735448087/100000000000000 : ℝ)*(major2) + (51129861629/100000000000000 : ℝ)*(sp1) + (2767858433/5000000000000 : ℝ)*(sp2) + (399375299060379/5000000000000 : ℝ)*(sp4) + (499215814084663/6250000000000 : ℝ)*(sp5) + (3993724319669703/50000000000000 : ℝ)*(sp6) + (3980501154393231/100000000000000 : ℝ)*(sp7) + (3980501154393231/100000000000000 : ℝ)*(f.failure) + (399375299060379/5000000000000 : ℝ)*(f.sum) + (1060101501533/278750000000000000000000000 : ℝ)*base66 + (1365915613839440053/223000000000000000000000000000000 : ℝ)*base68 + (1604849290311440053/223000000000000000000000000000000 : ℝ)*base70 + (566793907926559947/223000000000000000000000000000000 : ℝ)*base71 + (394496360403/1115000000000000000000000000 : ℝ)*base73 + (1588255860534440053/223000000000000000000000000000000 : ℝ)*base76 + (1014618813931559947/223000000000000000000000000000000 : ℝ)*base77 + (4201683892479440053/223000000000000000000000000000000 : ℝ)*base80 + (7137222473757/1115000000000000000000000000 : ℝ)*base82 + (7644213/10000000000000000000000 : ℝ)*base89 + (7644213/10000000000000000000000 : ℝ)*base91 + (7644213/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1186_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150332923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (88/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2851/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11409/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (563/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1186_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1186_s8_0 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2146022053/10000000000 : ℝ)*x 0 + (5392195201/10000000000 : ℝ)*x 1 + (5266459751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2146022053/10000000000 : ℝ)^8379 ≤ (13044460596883/100000000000000 : ℝ)^6331 := by
    have hnat : (2146022053 : ℕ)^8379*100000000000000^6331 ≤ 13044460596883^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2146022053 10000000000 13044460596883 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392195201/10000000000 : ℝ)^8379 ≤ (44156547024509/100000000000000 : ℝ)^6331 := by
    have hnat : (5392195201 : ℕ)^8379*100000000000000^6331 ≤ 44156547024509^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392195201 10000000000 44156547024509 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266459751/10000000000 : ℝ)^8379 ≤ (42798992361413/100000000000000 : ℝ)^6331 := by
    have hnat : (5266459751 : ℕ)^8379*100000000000000^6331 ≤ 42798992361413^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266459751 10000000000 42798992361413 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2146022053/10000000000 : ℝ), (5392195201/10000000000 : ℝ), (5266459751/10000000000 : ℝ)] ![(13044460596883/100000000000000 : ℝ), (44156547024509/100000000000000 : ℝ), (42798992361413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2146022053/10000000000 : ℝ)|^8379 ≤ (13044460596883/100000000000000 : ℝ)^6331
        have hw : |(-2146022053/10000000000 : ℝ)|=(2146022053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392195201/10000000000 : ℝ)|^8379 ≤ (44156547024509/100000000000000 : ℝ)^6331
        have hw : |(5392195201/10000000000 : ℝ)|=(5392195201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266459751/10000000000 : ℝ)|^8379 ≤ (42798992361413/100000000000000 : ℝ)^6331
        have hw : |(5266459751/10000000000 : ℝ)|=(5266459751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s8_1 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (334035691/625000000 : ℝ)*x 0 + (-2209785967/10000000000 : ℝ)*x 1 + (2633229837/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334035691/625000000 : ℝ)^8379 ≤ (43641135078793/100000000000000 : ℝ)^6331 := by
    have hnat : (334035691 : ℕ)^8379*100000000000000^6331 ≤ 43641135078793^6331*625000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334035691 625000000 43641135078793 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2209785967/10000000000 : ℝ)^8379 ≤ (13559873382911/100000000000000 : ℝ)^6331 := by
    have hnat : (2209785967 : ℕ)^8379*100000000000000^6331 ≤ 13559873382911^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209785967 10000000000 13559873382911 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633229837/5000000000 : ℝ)^8379 ≤ (42798991533231/100000000000000 : ℝ)^6331 := by
    have hnat : (2633229837 : ℕ)^8379*100000000000000^6331 ≤ 42798991533231^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633229837 5000000000 42798991533231 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334035691/625000000 : ℝ), (-2209785967/10000000000 : ℝ), (2633229837/5000000000 : ℝ)] ![(43641135078793/100000000000000 : ℝ), (13559873382911/100000000000000 : ℝ), (42798991533231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334035691/625000000 : ℝ)|^8379 ≤ (43641135078793/100000000000000 : ℝ)^6331
        have hw : |(334035691/625000000 : ℝ)|=(334035691/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2209785967/10000000000 : ℝ)|^8379 ≤ (13559873382911/100000000000000 : ℝ)^6331
        have hw : |(-2209785967/10000000000 : ℝ)|=(2209785967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633229837/5000000000 : ℝ)|^8379 ≤ (42798991533231/100000000000000 : ℝ)^6331
        have hw : |(2633229837/5000000000 : ℝ)|=(2633229837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s8_2 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672285503/5000000000 : ℝ)*x 0 + (5266459747/10000000000 : ℝ)*x 1 + (-441957187/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672285503/5000000000 : ℝ)^8379 ≤ (8728226907689/20000000000000 : ℝ)^6331 := by
    have hnat : (2672285503 : ℕ)^8379*20000000000000^6331 ≤ 8728226907689^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672285503 5000000000 8728226907689 20000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266459747/10000000000 : ℝ)^8379 ≤ (4279899231839/10000000000000 : ℝ)^6331 := by
    have hnat : (5266459747 : ℕ)^8379*10000000000000^6331 ≤ 4279899231839^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266459747 10000000000 4279899231839 10000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (441957187/2000000000 : ℝ)^8379 ≤ (1355987312303/10000000000000 : ℝ)^6331 := by
    have hnat : (441957187 : ℕ)^8379*10000000000000^6331 ≤ 1355987312303^6331*2000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441957187 2000000000 1355987312303 10000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672285503/5000000000 : ℝ), (5266459747/10000000000 : ℝ), (-441957187/2000000000 : ℝ)] ![(8728226907689/20000000000000 : ℝ), (4279899231839/10000000000000 : ℝ), (1355987312303/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672285503/5000000000 : ℝ)|^8379 ≤ (8728226907689/20000000000000 : ℝ)^6331
        have hw : |(2672285503/5000000000 : ℝ)|=(2672285503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266459747/10000000000 : ℝ)|^8379 ≤ (4279899231839/10000000000000 : ℝ)^6331
        have hw : |(5266459747/10000000000 : ℝ)|=(5266459747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-441957187/2000000000 : ℝ)|^8379 ≤ (1355987312303/10000000000000 : ℝ)^6331
        have hw : |(-441957187/2000000000 : ℝ)|=(441957187/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s8_3 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (544814127/1250000000 : ℝ)*x 0 + (2117078573/5000000000 : ℝ)*x 1 + (4486465387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544814127/1250000000 : ℝ)^8379 ≤ (16658610690523/50000000000000 : ℝ)^6331 := by
    have hnat : (544814127 : ℕ)^8379*50000000000000^6331 ≤ 16658610690523^6331*1250000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544814127 1250000000 16658610690523 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2117078573/5000000000 : ℝ)^8379 ≤ (6412992195379/20000000000000 : ℝ)^6331 := by
    have hnat : (2117078573 : ℕ)^8379*20000000000000^6331 ≤ 6412992195379^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117078573 5000000000 6412992195379 20000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4486465387/10000000000 : ℝ)^8379 ≤ (1730890881473/5000000000000 : ℝ)^6331 := by
    have hnat : (4486465387 : ℕ)^8379*5000000000000^6331 ≤ 1730890881473^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486465387 10000000000 1730890881473 5000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(544814127/1250000000 : ℝ), (2117078573/5000000000 : ℝ), (4486465387/10000000000 : ℝ)] ![(16658610690523/50000000000000 : ℝ), (6412992195379/20000000000000 : ℝ), (1730890881473/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(544814127/1250000000 : ℝ)|^8379 ≤ (16658610690523/50000000000000 : ℝ)^6331
        have hw : |(544814127/1250000000 : ℝ)|=(544814127/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2117078573/5000000000 : ℝ)|^8379 ≤ (6412992195379/20000000000000 : ℝ)^6331
        have hw : |(2117078573/5000000000 : ℝ)|=(2117078573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4486465387/10000000000 : ℝ)|^8379 ≤ (1730890881473/5000000000000 : ℝ)^6331
        have hw : |(4486465387/10000000000 : ℝ)|=(4486465387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s8_4 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-42920531/200000000 : ℝ)*x 0 + (5266775983/10000000000 : ℝ)*x 1 + (539187803/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42920531/200000000 : ℝ)^8379 ≤ (521779870963/4000000000000 : ℝ)^6331 := by
    have hnat : (42920531 : ℕ)^8379*4000000000000^6331 ≤ 521779870963^6331*200000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42920531 200000000 521779870963 4000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266775983/10000000000 : ℝ)^8379 ≤ (21401196829709/50000000000000 : ℝ)^6331 := by
    have hnat : (5266775983 : ℕ)^8379*50000000000000^6331 ≤ 21401196829709^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266775983 10000000000 21401196829709 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539187803/1000000000 : ℝ)^8379 ≤ (22076554778049/50000000000000 : ℝ)^6331 := by
    have hnat : (539187803 : ℕ)^8379*50000000000000^6331 ≤ 22076554778049^6331*1000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539187803 1000000000 22076554778049 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-42920531/200000000 : ℝ), (5266775983/10000000000 : ℝ), (539187803/1000000000 : ℝ)] ![(521779870963/4000000000000 : ℝ), (21401196829709/50000000000000 : ℝ), (22076554778049/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-42920531/200000000 : ℝ)|^8379 ≤ (521779870963/4000000000000 : ℝ)^6331
        have hw : |(-42920531/200000000 : ℝ)|=(42920531/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266775983/10000000000 : ℝ)|^8379 ≤ (21401196829709/50000000000000 : ℝ)^6331
        have hw : |(5266775983/10000000000 : ℝ)|=(5266775983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539187803/1000000000 : ℝ)|^8379 ≤ (22076554778049/50000000000000 : ℝ)^6331
        have hw : |(539187803/1000000000 : ℝ)|=(539187803/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s8_5 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312613109/10000000000 : ℝ)*x 0 + (-260545997/1250000000 : ℝ)*x 1 + (5391877943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312613109/10000000000 : ℝ)^8379 ≤ (676501588801/1562500000000 : ℝ)^6331 := by
    have hnat : (5312613109 : ℕ)^8379*1562500000000^6331 ≤ 676501588801^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312613109 10000000000 676501588801 1562500000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260545997/1250000000 : ℝ)^8379 ≤ (12550789686853/100000000000000 : ℝ)^6331 := by
    have hnat : (260545997 : ℕ)^8379*100000000000000^6331 ≤ 12550789686853^6331*1250000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260545997 1250000000 12550789686853 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391877943/10000000000 : ℝ)^8379 ≤ (4415310861321/10000000000000 : ℝ)^6331 := by
    have hnat : (5391877943 : ℕ)^8379*10000000000000^6331 ≤ 4415310861321^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391877943 10000000000 4415310861321 10000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312613109/10000000000 : ℝ), (-260545997/1250000000 : ℝ), (5391877943/10000000000 : ℝ)] ![(676501588801/1562500000000 : ℝ), (12550789686853/100000000000000 : ℝ), (4415310861321/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312613109/10000000000 : ℝ)|^8379 ≤ (676501588801/1562500000000 : ℝ)^6331
        have hw : |(5312613109/10000000000 : ℝ)|=(5312613109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-260545997/1250000000 : ℝ)|^8379 ≤ (12550789686853/100000000000000 : ℝ)^6331
        have hw : |(-260545997/1250000000 : ℝ)|=(260545997/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391877943/10000000000 : ℝ)|^8379 ≤ (4415310861321/10000000000000 : ℝ)^6331
        have hw : |(5391877943/10000000000 : ℝ)|=(5391877943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s8_6 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (332038319/625000000 : ℝ)*x 0 + (2695939009/5000000000 : ℝ)*x 1 + (-2084367881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332038319/625000000 : ℝ)^8379 ≤ (21648050814667/50000000000000 : ℝ)^6331 := by
    have hnat : (332038319 : ℕ)^8379*50000000000000^6331 ≤ 21648050814667^6331*625000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332038319 625000000 21648050814667 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695939009/5000000000 : ℝ)^8379 ≤ (8830621885209/20000000000000 : ℝ)^6331 := by
    have hnat : (2695939009 : ℕ)^8379*20000000000000^6331 ≤ 8830621885209^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695939009 5000000000 8830621885209 20000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2084367881/10000000000 : ℝ)^8379 ≤ (784424308111/6250000000000 : ℝ)^6331 := by
    have hnat : (2084367881 : ℕ)^8379*6250000000000^6331 ≤ 784424308111^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084367881 10000000000 784424308111 6250000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(332038319/625000000 : ℝ), (2695939009/5000000000 : ℝ), (-2084367881/10000000000 : ℝ)] ![(21648050814667/50000000000000 : ℝ), (8830621885209/20000000000000 : ℝ), (784424308111/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(332038319/625000000 : ℝ)|^8379 ≤ (21648050814667/50000000000000 : ℝ)^6331
        have hw : |(332038319/625000000 : ℝ)|=(332038319/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695939009/5000000000 : ℝ)|^8379 ≤ (8830621885209/20000000000000 : ℝ)^6331
        have hw : |(2695939009/5000000000 : ℝ)|=(2695939009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2084367881/10000000000 : ℝ)|^8379 ≤ (784424308111/6250000000000 : ℝ)^6331
        have hw : |(-2084367881/10000000000 : ℝ)|=(2084367881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s8_7 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2179261341/5000000000 : ℝ)*x 0 + (2242915331/5000000000 : ℝ)*x 1 + (4234794081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179261341/5000000000 : ℝ)^8379 ≤ (16658659585839/50000000000000 : ℝ)^6331 := by
    have hnat : (2179261341 : ℕ)^8379*50000000000000^6331 ≤ 16658659585839^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179261341 5000000000 16658659585839 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2242915331/5000000000 : ℝ)^8379 ≤ (34611335899897/100000000000000 : ℝ)^6331 := by
    have hnat : (2242915331 : ℕ)^8379*100000000000000^6331 ≤ 34611335899897^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242915331 5000000000 34611335899897 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4234794081/10000000000 : ℝ)^8379 ≤ (32071344924307/100000000000000 : ℝ)^6331 := by
    have hnat : (4234794081 : ℕ)^8379*100000000000000^6331 ≤ 32071344924307^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4234794081 10000000000 32071344924307 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2179261341/5000000000 : ℝ), (2242915331/5000000000 : ℝ), (4234794081/10000000000 : ℝ)] ![(16658659585839/50000000000000 : ℝ), (34611335899897/100000000000000 : ℝ), (32071344924307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2179261341/5000000000 : ℝ)|^8379 ≤ (16658659585839/50000000000000 : ℝ)^6331
        have hw : |(2179261341/5000000000 : ℝ)|=(2179261341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2242915331/5000000000 : ℝ)|^8379 ≤ (34611335899897/100000000000000 : ℝ)^6331
        have hw : |(2242915331/5000000000 : ℝ)|=(2242915331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4234794081/10000000000 : ℝ)|^8379 ≤ (32071344924307/100000000000000 : ℝ)^6331
        have hw : |(4234794081/10000000000 : ℝ)|=(4234794081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1186_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150332923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (563/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11409/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1141/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7037/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (563/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11409/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (563/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11409/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (563/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11409/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (563/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11409/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (563/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11409/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (563/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11409/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11409/100000 : ℝ) ^ (4189/1024 : ℝ) ≤ (86945932262541/625000000000000000 : ℝ) := by
    have hpowers : (11409/100000 : ℝ)^4189 ≤ (86945932262541/625000000000000000 : ℝ)^1024 := by
      have hnat : (11409 : ℕ)^4189*625000000000000000^1024 ≤ 86945932262541^1024*100000^4189 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11409 100000 86945932262541 625000000000000000 4189 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11409/100000 : ℝ)) (X := (86945932262541/625000000000000000 : ℝ)) (by norm_num) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (563/4000 : ℝ) ^ (4189/1024 : ℝ) ≤ (6568790751446741/20000000000000000000 : ℝ) := by
    have hpowers : (563/4000 : ℝ)^4189 ≤ (6568790751446741/20000000000000000000 : ℝ)^1024 := by
      have hnat : (563 : ℕ)^4189*20000000000000000000^1024 ≤ 6568790751446741^1024*4000^4189 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        563 4000 6568790751446741 20000000000000000000 4189 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (563/4000 : ℝ)) (X := (6568790751446741/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (312586945932262541/312500000000000000 : ℝ) ≤ (10000680053688699/10000000000000000 : ℝ) ^ (4189/1024 : ℝ) := by
    have hpowers : (312586945932262541/312500000000000000 : ℝ)^1024 ≤ (10000680053688699/10000000000000000 : ℝ)^4189 := by
      have hnat : (312586945932262541 : ℕ)^1024*10000000000000000^4189 ≤ 10000680053688699^4189*312500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        312586945932262541 312500000000000000 10000680053688699 10000000000000000 1024 4189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000680053688699/10000000000000000 : ℝ)) (X := (312586945932262541/312500000000000000 : ℝ)) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009351060583848053/20000000000000000000 : ℝ) ≤ (10001142730387119/10000000000000000 : ℝ) ^ (4189/1024 : ℝ) := by
    have hpowers : (20009351060583848053/20000000000000000000 : ℝ)^1024 ≤ (10001142730387119/10000000000000000 : ℝ)^4189 := by
      have hnat : (20009351060583848053 : ℕ)^1024*10000000000000000^4189 ≤ 10001142730387119^4189*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009351060583848053 20000000000000000000 10001142730387119 10000000000000000 1024 4189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001142730387119/10000000000000000 : ℝ)) (X := (20009351060583848053/20000000000000000000 : ℝ)) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006568790751446741/10000000000000000000 : ℝ) ≤ (10001605407085539/10000000000000000 : ℝ) ^ (4189/1024 : ℝ) := by
    have hpowers : (10006568790751446741/10000000000000000000 : ℝ)^1024 ≤ (10001605407085539/10000000000000000 : ℝ)^4189 := by
      have hnat : (10006568790751446741 : ℕ)^1024*10000000000000000^4189 ≤ 10001605407085539^4189*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006568790751446741 10000000000000000000 10001605407085539 10000000000000000 1024 4189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001605407085539/10000000000000000 : ℝ)) (X := (10006568790751446741/10000000000000000000 : ℝ)) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(86945932262541/625000000000000000 : ℝ) ≤ ((13325627833114761987/13330000000000000000 : ℝ)+2*(23133834921/13330000000000 : ℝ)*(11409/100000 : ℝ))^(4189/1024 : ℝ) := by
    rw [show (13325627833114761987/13330000000000000000 : ℝ)+2*(23133834921/13330000000000 : ℝ)*(11409/100000 : ℝ)=(10000680053688699/10000000000000000 : ℝ) by norm_num, show 1+2*(86945932262541/625000000000000000 : ℝ)=(312586945932262541/312500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6568790751446741/20000000000000000000 : ℝ)+(86945932262541/625000000000000000 : ℝ) ≤ ((13325627833114761987/13330000000000000000 : ℝ)+(23133834921/13330000000000 : ℝ)*((563/4000 : ℝ)+(11409/100000 : ℝ)))^(4189/1024 : ℝ) := by
    rw [show (13325627833114761987/13330000000000000000 : ℝ)+(23133834921/13330000000000 : ℝ)*((563/4000 : ℝ)+(11409/100000 : ℝ))=(10001142730387119/10000000000000000 : ℝ) by norm_num, show 1+(6568790751446741/20000000000000000000 : ℝ)+(86945932262541/625000000000000000 : ℝ)=(20009351060583848053/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6568790751446741/20000000000000000000 : ℝ) ≤ ((13325627833114761987/13330000000000000000 : ℝ)+2*(23133834921/13330000000000 : ℝ)*(563/4000 : ℝ))^(4189/1024 : ℝ) := by
    rw [show (13325627833114761987/13330000000000000000 : ℝ)+2*(23133834921/13330000000000 : ℝ)*(563/4000 : ℝ)=(10001605407085539/10000000000000000 : ℝ) by norm_num, show 1+2*(6568790751446741/20000000000000000000 : ℝ)=(10006568790751446741/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13325627833114761987/13330000000000000000 : ℝ)*(X 1 0+X 2 0)+(23133834921/13330000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4189/1024 : ℝ)) (lo := (11409/100000 : ℝ)) (hi := (563/4000 : ℝ)) (c := (13325627833114761987/13330000000000000000 : ℝ)) (alpha := (23133834921/13330000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13325627833114761987/13330000000000000000 : ℝ)*(X 0 1+X 2 1)+(23133834921/13330000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4189/1024 : ℝ)) (lo := (11409/100000 : ℝ)) (hi := (563/4000 : ℝ)) (c := (13325627833114761987/13330000000000000000 : ℝ)) (alpha := (23133834921/13330000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13325627833114761987/13330000000000000000 : ℝ)*(X 0 2+X 1 2)+(23133834921/13330000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4189/1024 : ℝ)) (lo := (11409/100000 : ℝ)) (hi := (563/4000 : ℝ)) (c := (13325627833114761987/13330000000000000000 : ℝ)) (alpha := (23133834921/13330000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2146022053/10000000000 : ℝ)*X 0 0+(5392195201/10000000000 : ℝ)*X 0 1+(5266459751/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334035691/625000000 : ℝ)*X 1 0+(-2209785967/10000000000 : ℝ)*X 1 1+(2633229837/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672285503/5000000000 : ℝ)*X 2 0+(5266459747/10000000000 : ℝ)*X 2 1+(-441957187/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((544814127/1250000000 : ℝ)*X 0 0+(2117078573/5000000000 : ℝ)*X 0 1+(4486465387/10000000000 : ℝ)*X 0 2+(544814127/1250000000 : ℝ)*X 1 0+(2117078573/5000000000 : ℝ)*X 1 1+(4486465387/10000000000 : ℝ)*X 1 2+(544814127/1250000000 : ℝ)*X 2 0+(2117078573/5000000000 : ℝ)*X 2 1+(4486465387/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-42920531/200000000 : ℝ)*X 0 0+(5266775983/10000000000 : ℝ)*X 0 1+(539187803/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312613109/10000000000 : ℝ)*X 1 0+(-260545997/1250000000 : ℝ)*X 1 1+(5391877943/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((332038319/625000000 : ℝ)*X 2 0+(2695939009/5000000000 : ℝ)*X 2 1+(-2084367881/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2179261341/5000000000 : ℝ)*X 0 0+(2242915331/5000000000 : ℝ)*X 0 1+(4234794081/10000000000 : ℝ)*X 0 2+(2179261341/5000000000 : ℝ)*X 1 0+(2242915331/5000000000 : ℝ)*X 1 1+(4234794081/10000000000 : ℝ)*X 1 2+(2179261341/5000000000 : ℝ)*X 2 0+(2242915331/5000000000 : ℝ)*X 2 1+(4234794081/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5069807504317199492040852579/666500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (746208029/50000000000000 : ℝ)*(base19) + (1310471337/100000000000000 : ℝ)*(base23) + (11495047/20000000000000 : ℝ)*(lower2) + (33101117/20000000000000 : ℝ)*(upper3) + (15412763/12500000000000 : ℝ)*(upper5) + (5958365532945287/100000000000000 : ℝ)*(major0) + (5958365532945287/100000000000000 : ℝ)*(major1) + (5958365532945287/100000000000000 : ℝ)*(major2) + (7953245693553529/100000000000000 : ℝ)*(sp0) + (7953282448775101/100000000000000 : ℝ)*(sp1) + (3976641315359911/50000000000000 : ℝ)*(sp2) + (396342584612221/10000000000000 : ℝ)*(sp3) + (38247637631/100000000000000 : ℝ)*(sp4) + (2628127929/12500000000000 : ℝ)*(sp7) + (1981723435572821/50000000000000 : ℝ)*(f.failure) + (198832098529779/2500000000000 : ℝ)*(f.sum) + (7409073435953/1333000000000000000000000000 : ℝ)*base65 + (6279524530507405269/1333000000000000000000000000000000 : ℝ)*base67 + (15554013028582405269/1333000000000000000000000000000000 : ℝ)*base69 + (10870201382305405269/1333000000000000000000000000000000 : ℝ)*base71 + (4022714675687/1333000000000000000000000000 : ℝ)*base74 + (32244347581537405269/1333000000000000000000000000000000 : ℝ)*base75 + (56099882397405269/1333000000000000000000000000000000 : ℝ)*base77 + (4880175212651405269/1333000000000000000000000000000000 : ℝ)*base79 + (248430430609/666500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (10285783/5000000000000000000000 : ℝ)*base89 + (10285783/5000000000000000000000 : ℝ)*base91 + (10285783/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1738059434615793156891800691/133300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (39316359/5000000000000 : ℝ)*(base19) + (1543866009/100000000000000 : ℝ)*(base23) + (233730361/100000000000000 : ℝ)*(lower1) + (29537877/50000000000000 : ℝ)*(upper3) + (352106953/100000000000000 : ℝ)*(lower4) + (132057431/50000000000000 : ℝ)*(upper5) + (1197692334088069/20000000000000 : ℝ)*(major0) + (1197692334088069/20000000000000 : ℝ)*(major1) + (1197692334088069/20000000000000 : ℝ)*(major2) + (17003880041/100000000000000 : ℝ)*(sp2) + (7993456376812779/100000000000000 : ℝ)*(sp4) + (3996727795242799/50000000000000 : ℝ)*(sp5) + (799343782906673/10000000000000 : ℝ)*(sp6) + (995866632361087/25000000000000 : ℝ)*(sp7) + (995866632361087/25000000000000 : ℝ)*(f.failure) + (7993456376812779/100000000000000 : ℝ)*(f.sum) + (206043699887/333250000000000000000000000 : ℝ)*base66 + (10662228092722633103/266600000000000000000000000000000 : ℝ)*base67 + (1276664557017633103/266600000000000000000000000000000 : ℝ)*base69 + (30191401381918366897/266600000000000000000000000000000 : ℝ)*base72 + (1041435900533/666500000000000000000000000 : ℝ)*base73 + (64726926146587233103/266600000000000000000000000000000 : ℝ)*base75 + (491961330147233103/266600000000000000000000000000000 : ℝ)*base77 + (2444004932343366897/266600000000000000000000000000000 : ℝ)*base80 + (1333735138731/1333000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (24832699/2500000000000000000000 : ℝ)*base90 + (24832699/2500000000000000000000 : ℝ)*base92 + (24832699/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1186_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150332923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (563/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11409/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1141/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7037/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1186_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1186_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150332923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14107/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5689/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1141/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7037/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1186_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1186_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1186_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150332923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14107/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5689/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1141/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7037/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1186_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

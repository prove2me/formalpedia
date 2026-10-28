-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1162_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:40:58.8623+00:00
-- url     : https://prove2.me/submissions/6e79715c-ae5c-45d2-9606-f6cd2452e3f0

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
theorem support_rectangle_w1162_s6_0 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2157331819/10000000000 : ℝ)*x 0 + (1348245557/2500000000 : ℝ)*x 1 + (5265763517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2157331819/10000000000 : ℝ)^8355 ≤ (524429854173/4000000000000 : ℝ)^6307 := by
    have hnat : (2157331819 : ℕ)^8355*4000000000000^6307 ≤ 524429854173^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157331819 10000000000 524429854173 4000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348245557/2500000000 : ℝ)^8355 ≤ (4413151969/10000000000 : ℝ)^6307 := by
    have hnat : (1348245557 : ℕ)^8355*10000000000^6307 ≤ 4413151969^6307*2500000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348245557 2500000000 4413151969 10000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265763517/10000000000 : ℝ)^8355 ≤ (8551546786099/20000000000000 : ℝ)^6307 := by
    have hnat : (5265763517 : ℕ)^8355*20000000000000^6307 ≤ 8551546786099^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265763517 10000000000 8551546786099 20000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2157331819/10000000000 : ℝ), (1348245557/2500000000 : ℝ), (5265763517/10000000000 : ℝ)] ![(524429854173/4000000000000 : ℝ), (4413151969/10000000000 : ℝ), (8551546786099/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2157331819/10000000000 : ℝ)|^8355 ≤ (524429854173/4000000000000 : ℝ)^6307
        have hw : |(-2157331819/10000000000 : ℝ)|=(2157331819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348245557/2500000000 : ℝ)|^8355 ≤ (4413151969/10000000000 : ℝ)^6307
        have hw : |(1348245557/2500000000 : ℝ)|=(1348245557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265763517/10000000000 : ℝ)|^8355 ≤ (8551546786099/20000000000000 : ℝ)^6307
        have hw : |(5265763517/10000000000 : ℝ)|=(5265763517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s6_1 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (213790373/400000000 : ℝ)*x 0 + (-444371737/2000000000 : ℝ)*x 1 + (5265763517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213790373/400000000 : ℝ)^8355 ≤ (8721905348999/20000000000000 : ℝ)^6307 := by
    have hnat : (213790373 : ℕ)^8355*20000000000000^6307 ≤ 8721905348999^6307*400000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213790373 400000000 8721905348999 20000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (444371737/2000000000 : ℝ)^8355 ≤ (109061914477/800000000000 : ℝ)^6307 := by
    have hnat : (444371737 : ℕ)^8355*800000000000^6307 ≤ 109061914477^6307*2000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      444371737 2000000000 109061914477 800000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265763517/10000000000 : ℝ)^8355 ≤ (8551546786099/20000000000000 : ℝ)^6307 := by
    have hnat : (5265763517 : ℕ)^8355*20000000000000^6307 ≤ 8551546786099^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265763517 10000000000 8551546786099 20000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213790373/400000000 : ℝ), (-444371737/2000000000 : ℝ), (5265763517/10000000000 : ℝ)] ![(8721905348999/20000000000000 : ℝ), (109061914477/800000000000 : ℝ), (8551546786099/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213790373/400000000 : ℝ)|^8355 ≤ (8721905348999/20000000000000 : ℝ)^6307
        have hw : |(213790373/400000000 : ℝ)|=(213790373/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-444371737/2000000000 : ℝ)|^8355 ≤ (109061914477/800000000000 : ℝ)^6307
        have hw : |(-444371737/2000000000 : ℝ)|=(444371737/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265763517/10000000000 : ℝ)|^8355 ≤ (8551546786099/20000000000000 : ℝ)^6307
        have hw : |(5265763517/10000000000 : ℝ)|=(5265763517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s6_2 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336189831/2500000000 : ℝ)*x 0 + (5265763517/10000000000 : ℝ)*x 1 + (-1110929343/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336189831/2500000000 : ℝ)^8355 ≤ (21804763367093/50000000000000 : ℝ)^6307 := by
    have hnat : (1336189831 : ℕ)^8355*50000000000000^6307 ≤ 21804763367093^6307*2500000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336189831 2500000000 21804763367093 50000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265763517/10000000000 : ℝ)^8355 ≤ (8551546786099/20000000000000 : ℝ)^6307 := by
    have hnat : (5265763517 : ℕ)^8355*20000000000000^6307 ≤ 8551546786099^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265763517 10000000000 8551546786099 20000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1110929343/5000000000 : ℝ)^8355 ≤ (13632739317753/100000000000000 : ℝ)^6307 := by
    have hnat : (1110929343 : ℕ)^8355*100000000000000^6307 ≤ 13632739317753^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1110929343 5000000000 13632739317753 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336189831/2500000000 : ℝ), (5265763517/10000000000 : ℝ), (-1110929343/5000000000 : ℝ)] ![(21804763367093/50000000000000 : ℝ), (8551546786099/20000000000000 : ℝ), (13632739317753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336189831/2500000000 : ℝ)|^8355 ≤ (21804763367093/50000000000000 : ℝ)^6307
        have hw : |(1336189831/2500000000 : ℝ)|=(1336189831/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265763517/10000000000 : ℝ)|^8355 ≤ (8551546786099/20000000000000 : ℝ)^6307
        have hw : |(5265763517/10000000000 : ℝ)|=(5265763517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1110929343/5000000000 : ℝ)|^8355 ≤ (13632739317753/100000000000000 : ℝ)^6307
        have hw : |(-1110929343/5000000000 : ℝ)|=(1110929343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s6_3 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4361847799/10000000000 : ℝ)*x 0 + (4236634529/10000000000 : ℝ)*x 1 + (35925809/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4361847799/10000000000 : ℝ)^8355 ≤ (33316918847577/100000000000000 : ℝ)^6307 := by
    have hnat : (4361847799 : ℕ)^8355*100000000000000^6307 ≤ 33316918847577^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4361847799 10000000000 33316918847577 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4236634529/10000000000 : ℝ)^8355 ≤ (32055886787863/100000000000000 : ℝ)^6307 := by
    have hnat : (4236634529 : ℕ)^8355*100000000000000^6307 ≤ 32055886787863^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4236634529 10000000000 32055886787863 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35925809/80000000 : ℝ)^8355 ≤ (6925438869743/20000000000000 : ℝ)^6307 := by
    have hnat : (35925809 : ℕ)^8355*20000000000000^6307 ≤ 6925438869743^6307*80000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35925809 80000000 6925438869743 20000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4361847799/10000000000 : ℝ), (4236634529/10000000000 : ℝ), (35925809/80000000 : ℝ)] ![(33316918847577/100000000000000 : ℝ), (32055886787863/100000000000000 : ℝ), (6925438869743/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4361847799/10000000000 : ℝ)|^8355 ≤ (33316918847577/100000000000000 : ℝ)^6307
        have hw : |(4361847799/10000000000 : ℝ)|=(4361847799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4236634529/10000000000 : ℝ)|^8355 ≤ (32055886787863/100000000000000 : ℝ)^6307
        have hw : |(4236634529/10000000000 : ℝ)|=(4236634529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(35925809/80000000 : ℝ)|^8355 ≤ (6925438869743/20000000000000 : ℝ)^6307
        have hw : |(35925809/80000000 : ℝ)|=(35925809/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s6_4 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1078668377/5000000000 : ℝ)*x 0 + (5266084839/10000000000 : ℝ)*x 1 + (5392659717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078668377/5000000000 : ℝ)^8355 ≤ (2622157216917/20000000000000 : ℝ)^6307 := by
    have hnat : (1078668377 : ℕ)^8355*20000000000000^6307 ≤ 2622157216917^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078668377 5000000000 2622157216917 20000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266084839/10000000000 : ℝ)^8355 ≤ (855223806247/2000000000000 : ℝ)^6307 := by
    have hnat : (5266084839 : ℕ)^8355*2000000000000^6307 ≤ 855223806247^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266084839 10000000000 855223806247 2000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392659717/10000000000 : ℝ)^8355 ≤ (11032005897529/25000000000000 : ℝ)^6307 := by
    have hnat : (5392659717 : ℕ)^8355*25000000000000^6307 ≤ 11032005897529^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392659717 10000000000 11032005897529 25000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1078668377/5000000000 : ℝ), (5266084839/10000000000 : ℝ), (5392659717/10000000000 : ℝ)] ![(2622157216917/20000000000000 : ℝ), (855223806247/2000000000000 : ℝ), (11032005897529/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1078668377/5000000000 : ℝ)|^8355 ≤ (2622157216917/20000000000000 : ℝ)^6307
        have hw : |(-1078668377/5000000000 : ℝ)|=(1078668377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266084839/10000000000 : ℝ)|^8355 ≤ (855223806247/2000000000000 : ℝ)^6307
        have hw : |(5266084839/10000000000 : ℝ)|=(5266084839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392659717/10000000000 : ℝ)|^8355 ≤ (11032005897529/25000000000000 : ℝ)^6307
        have hw : |(5392659717/10000000000 : ℝ)|=(5392659717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s6_5 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656240281/5000000000 : ℝ)*x 0 + (-2094962521/10000000000 : ℝ)*x 1 + (2696329837/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656240281/5000000000 : ℝ)^8355 ≤ (43260975135161/100000000000000 : ℝ)^6307 := by
    have hnat : (2656240281 : ℕ)^8355*100000000000000^6307 ≤ 43260975135161^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656240281 5000000000 43260975135161 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2094962521/10000000000 : ℝ)^8355 ≤ (3152750432263/25000000000000 : ℝ)^6307 := by
    have hnat : (2094962521 : ℕ)^8355*25000000000000^6307 ≤ 3152750432263^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2094962521 10000000000 3152750432263 25000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696329837/5000000000 : ℝ)^8355 ≤ (4412802312399/10000000000000 : ℝ)^6307 := by
    have hnat : (2696329837 : ℕ)^8355*10000000000000^6307 ≤ 4412802312399^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696329837 5000000000 4412802312399 10000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656240281/5000000000 : ℝ), (-2094962521/10000000000 : ℝ), (2696329837/5000000000 : ℝ)] ![(43260975135161/100000000000000 : ℝ), (3152750432263/25000000000000 : ℝ), (4412802312399/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656240281/5000000000 : ℝ)|^8355 ≤ (43260975135161/100000000000000 : ℝ)^6307
        have hw : |(2656240281/5000000000 : ℝ)|=(2656240281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2094962521/10000000000 : ℝ)|^8355 ≤ (3152750432263/25000000000000 : ℝ)^6307
        have hw : |(-2094962521/10000000000 : ℝ)|=(2094962521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696329837/5000000000 : ℝ)|^8355 ≤ (4412802312399/10000000000000 : ℝ)^6307
        have hw : |(2696329837/5000000000 : ℝ)|=(2696329837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s6_6 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (265624029/500000000 : ℝ)*x 0 + (1348164907/2500000000 : ℝ)*x 1 + (-1047481279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265624029/500000000 : ℝ)^8355 ≤ (43260975329337/100000000000000 : ℝ)^6307 := by
    have hnat : (265624029 : ℕ)^8355*100000000000000^6307 ≤ 43260975329337^6307*500000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265624029 500000000 43260975329337 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348164907/2500000000 : ℝ)^8355 ≤ (44128022625343/100000000000000 : ℝ)^6307 := by
    have hnat : (1348164907 : ℕ)^8355*100000000000000^6307 ≤ 44128022625343^6307*2500000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348164907 2500000000 44128022625343 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1047481279/5000000000 : ℝ)^8355 ≤ (1576375253013/12500000000000 : ℝ)^6307 := by
    have hnat : (1047481279 : ℕ)^8355*12500000000000^6307 ≤ 1576375253013^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047481279 5000000000 1576375253013 12500000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265624029/500000000 : ℝ), (1348164907/2500000000 : ℝ), (-1047481279/5000000000 : ℝ)] ![(43260975329337/100000000000000 : ℝ), (44128022625343/100000000000000 : ℝ), (1576375253013/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265624029/500000000 : ℝ)|^8355 ≤ (43260975329337/100000000000000 : ℝ)^6307
        have hw : |(265624029/500000000 : ℝ)|=(265624029/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348164907/2500000000 : ℝ)|^8355 ≤ (44128022625343/100000000000000 : ℝ)^6307
        have hw : |(1348164907/2500000000 : ℝ)|=(1348164907/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1047481279/5000000000 : ℝ)|^8355 ≤ (1576375253013/12500000000000 : ℝ)^6307
        have hw : |(-1047481279/5000000000 : ℝ)|=(1047481279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s6_7 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4361857531/10000000000 : ℝ)*x 0 + (4490084293/10000000000 : ℝ)*x 1 + (105931969/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4361857531/10000000000 : ℝ)^8355 ≤ (6663403464253/20000000000000 : ℝ)^6307 := by
    have hnat : (4361857531 : ℕ)^8355*20000000000000^6307 ≤ 6663403464253^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4361857531 10000000000 6663403464253 20000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4490084293/10000000000 : ℝ)^8355 ≤ (8655159599629/25000000000000 : ℝ)^6307 := by
    have hnat : (4490084293 : ℕ)^8355*25000000000000^6307 ≤ 8655159599629^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490084293 10000000000 8655159599629 25000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105931969/250000000 : ℝ)^8355 ≤ (32062344263229/100000000000000 : ℝ)^6307 := by
    have hnat : (105931969 : ℕ)^8355*100000000000000^6307 ≤ 32062344263229^6307*250000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105931969 250000000 32062344263229 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4361857531/10000000000 : ℝ), (4490084293/10000000000 : ℝ), (105931969/250000000 : ℝ)] ![(6663403464253/20000000000000 : ℝ), (8655159599629/25000000000000 : ℝ), (32062344263229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4361857531/10000000000 : ℝ)|^8355 ≤ (6663403464253/20000000000000 : ℝ)^6307
        have hw : |(4361857531/10000000000 : ℝ)|=(4361857531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4490084293/10000000000 : ℝ)|^8355 ≤ (8655159599629/25000000000000 : ℝ)^6307
        have hw : |(4490084293/10000000000 : ℝ)|=(4490084293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105931969/250000000 : ℝ)|^8355 ≤ (32062344263229/100000000000000 : ℝ)^6307
        have hw : |(105931969/250000000 : ℝ)|=(105931969/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1162_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74932041/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14097/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (709/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (11373/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14067/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14097/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (709/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14097/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (709/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14097/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (709/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14097/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (709/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14097/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (709/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14097/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (709/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (709/6250 : ℝ) ^ (4177/1024 : ℝ) ≤ (6970523675014527/50000000000000000000 : ℝ) := by
    have hpowers : (709/6250 : ℝ)^4177 ≤ (6970523675014527/50000000000000000000 : ℝ)^1024 := by
      have hnat : (709 : ℕ)^4177*50000000000000000000^1024 ≤ 6970523675014527^1024*6250^4177 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        709 6250 6970523675014527 50000000000000000000 4177 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (709/6250 : ℝ)) (X := (6970523675014527/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14097/100000 : ℝ) ^ (4177/1024 : ℝ) ≤ (33822164029192931/100000000000000000000 : ℝ) := by
    have hpowers : (14097/100000 : ℝ)^4177 ≤ (33822164029192931/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14097 : ℕ)^4177*100000000000000000000^1024 ≤ 33822164029192931^1024*100000^4177 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14097 100000 33822164029192931 100000000000000000000 4177 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14097/100000 : ℝ)) (X := (33822164029192931/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006970523675014527/25000000000000000000 : ℝ) ≤ (2000136692654571/2000000000000000 : ℝ) ^ (4177/1024 : ℝ) := by
    have hpowers : (25006970523675014527/25000000000000000000 : ℝ)^1024 ≤ (2000136692654571/2000000000000000 : ℝ)^4177 := by
      have hnat : (25006970523675014527 : ℕ)^1024*2000000000000000^4177 ≤ 2000136692654571^4177*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006970523675014527 25000000000000000000 2000136692654571 2000000000000000 1024 4177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000136692654571/2000000000000000 : ℝ)) (X := (25006970523675014527/25000000000000000000 : ℝ)) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009552642275844397/20000000000000000000 : ℝ) ≤ (625073169610371/625000000000000 : ℝ) ^ (4177/1024 : ℝ) := by
    have hpowers : (20009552642275844397/20000000000000000000 : ℝ)^1024 ≤ (625073169610371/625000000000000 : ℝ)^4177 := by
      have hnat : (20009552642275844397 : ℕ)^1024*625000000000000^4177 ≤ 625073169610371^4177*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009552642275844397 20000000000000000000 625073169610371 625000000000000 1024 4177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625073169610371/625000000000000 : ℝ)) (X := (20009552642275844397/20000000000000000000 : ℝ)) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033822164029192931/50000000000000000000 : ℝ) ≤ (10001657964259017/10000000000000000 : ℝ) ^ (4177/1024 : ℝ) := by
    have hpowers : (50033822164029192931/50000000000000000000 : ℝ)^1024 ≤ (10001657964259017/10000000000000000 : ℝ)^4177 := by
      have hnat : (50033822164029192931 : ℕ)^1024*10000000000000000^4177 ≤ 10001657964259017^4177*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033822164029192931 50000000000000000000 10001657964259017 10000000000000000 1024 4177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001657964259017/10000000000000000 : ℝ)) (X := (50033822164029192931/50000000000000000000 : ℝ)) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6970523675014527/50000000000000000000 : ℝ) ≤ ((27520826835203148087/27530000000000000000 : ℝ)+2*(487250493081/275300000000000 : ℝ)*(709/6250 : ℝ))^(4177/1024 : ℝ) := by
    rw [show (27520826835203148087/27530000000000000000 : ℝ)+2*(487250493081/275300000000000 : ℝ)*(709/6250 : ℝ)=(2000136692654571/2000000000000000 : ℝ) by norm_num, show 1+2*(6970523675014527/50000000000000000000 : ℝ)=(25006970523675014527/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33822164029192931/100000000000000000000 : ℝ)+(6970523675014527/50000000000000000000 : ℝ) ≤ ((27520826835203148087/27530000000000000000 : ℝ)+(487250493081/275300000000000 : ℝ)*((14097/100000 : ℝ)+(709/6250 : ℝ)))^(4177/1024 : ℝ) := by
    rw [show (27520826835203148087/27530000000000000000 : ℝ)+(487250493081/275300000000000 : ℝ)*((14097/100000 : ℝ)+(709/6250 : ℝ))=(625073169610371/625000000000000 : ℝ) by norm_num, show 1+(33822164029192931/100000000000000000000 : ℝ)+(6970523675014527/50000000000000000000 : ℝ)=(20009552642275844397/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33822164029192931/100000000000000000000 : ℝ) ≤ ((27520826835203148087/27530000000000000000 : ℝ)+2*(487250493081/275300000000000 : ℝ)*(14097/100000 : ℝ))^(4177/1024 : ℝ) := by
    rw [show (27520826835203148087/27530000000000000000 : ℝ)+2*(487250493081/275300000000000 : ℝ)*(14097/100000 : ℝ)=(10001657964259017/10000000000000000 : ℝ) by norm_num, show 1+2*(33822164029192931/100000000000000000000 : ℝ)=(50033822164029192931/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27520826835203148087/27530000000000000000 : ℝ)*(X 1 0+X 2 0)+(487250493081/275300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4177/1024 : ℝ)) (lo := (709/6250 : ℝ)) (hi := (14097/100000 : ℝ)) (c := (27520826835203148087/27530000000000000000 : ℝ)) (alpha := (487250493081/275300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27520826835203148087/27530000000000000000 : ℝ)*(X 0 1+X 2 1)+(487250493081/275300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4177/1024 : ℝ)) (lo := (709/6250 : ℝ)) (hi := (14097/100000 : ℝ)) (c := (27520826835203148087/27530000000000000000 : ℝ)) (alpha := (487250493081/275300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27520826835203148087/27530000000000000000 : ℝ)*(X 0 2+X 1 2)+(487250493081/275300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4177/1024 : ℝ)) (lo := (709/6250 : ℝ)) (hi := (14097/100000 : ℝ)) (c := (27520826835203148087/27530000000000000000 : ℝ)) (alpha := (487250493081/275300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2157331819/10000000000 : ℝ)*X 0 0+(1348245557/2500000000 : ℝ)*X 0 1+(5265763517/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((213790373/400000000 : ℝ)*X 1 0+(-444371737/2000000000 : ℝ)*X 1 1+(5265763517/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336189831/2500000000 : ℝ)*X 2 0+(5265763517/10000000000 : ℝ)*X 2 1+(-1110929343/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4361847799/10000000000 : ℝ)*X 0 0+(4236634529/10000000000 : ℝ)*X 0 1+(35925809/80000000 : ℝ)*X 0 2+(4361847799/10000000000 : ℝ)*X 1 0+(4236634529/10000000000 : ℝ)*X 1 1+(35925809/80000000 : ℝ)*X 1 2+(4361847799/10000000000 : ℝ)*X 2 0+(4236634529/10000000000 : ℝ)*X 2 1+(35925809/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1078668377/5000000000 : ℝ)*X 0 0+(5266084839/10000000000 : ℝ)*X 0 1+(5392659717/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656240281/5000000000 : ℝ)*X 1 0+(-2094962521/10000000000 : ℝ)*X 1 1+(2696329837/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((265624029/500000000 : ℝ)*X 2 0+(1348164907/2500000000 : ℝ)*X 2 1+(-1047481279/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4361857531/10000000000 : ℝ)*X 0 0+(4490084293/10000000000 : ℝ)*X 0 1+(105931969/250000000 : ℝ)*X 0 2+(4361857531/10000000000 : ℝ)*X 1 0+(4490084293/10000000000 : ℝ)*X 1 1+(105931969/250000000 : ℝ)*X 1 2+(4361857531/10000000000 : ℝ)*X 2 0+(4490084293/10000000000 : ℝ)*X 2 1+(105931969/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3575366871123963374126221089/1376500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (258298173/50000000000000 : ℝ)*(base19) + (478790139/100000000000000 : ℝ)*(base23) + (3884091/20000000000000 : ℝ)*(lower2) + (13452659/20000000000000 : ℝ)*(upper3) + (1914941/5000000000000 : ℝ)*(upper5) + (5898055432844783/100000000000000 : ℝ)*(major0) + (5898055432844783/100000000000000 : ℝ)*(major1) + (5898055432844783/100000000000000 : ℝ)*(major2) + (3930246861359393/50000000000000 : ℝ)*(sp0) + (1572101435723173/20000000000000 : ℝ)*(sp1) + (982563402052759/12500000000000 : ℝ)*(sp2) + (3935595455930549/100000000000000 : ℝ)*(sp3) + (558899737/4000000000000 : ℝ)*(sp4) + (7627965687/100000000000000 : ℝ)*(sp7) + (983900770974059/25000000000000 : ℝ)*(f.failure) + (786050769521221/10000000000000 : ℝ)*(f.sum) + (41736115527537/13765000000000000000000000000 : ℝ)*base66 + (38252123285458319879/2753000000000000000000000000000000 : ℝ)*base68 + (13924116489219319879/2753000000000000000000000000000000 : ℝ)*base70 + (13320520526192319879/2753000000000000000000000000000000 : ℝ)*base72 + (10558386309671/1720625000000000000000000000 : ℝ)*base73 + (8583863932073319879/2753000000000000000000000000000000 : ℝ)*base76 + (68902787209051319879/2753000000000000000000000000000000 : ℝ)*base78 + (35090931683531319879/2753000000000000000000000000000000 : ℝ)*base80 + (21128082546189/6882500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (11424419/1250000000000000000000 : ℝ)*base89 + (11424419/1250000000000000000000 : ℝ)*base91 + (11424419/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (436178571586722889880138313/172062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (247341643/50000000000000 : ℝ)*(base19) + (561436049/100000000000000 : ℝ)*(base23) + (7576531/25000000000000 : ℝ)*(upper2) + (4562277/20000000000000 : ℝ)*(upper3) + (1531039/2000000000000 : ℝ)*(upper5) + (1482009019329267/25000000000000 : ℝ)*(major0) + (1482009019329267/25000000000000 : ℝ)*(major1) + (1482009019329267/25000000000000 : ℝ)*(major2) + (168576861/1250000000000 : ℝ)*(sp1) + (667369133/6250000000000 : ℝ)*(sp2) + (3950231881394967/50000000000000 : ℝ)*(sp4) + (987556222744721/12500000000000 : ℝ)*(sp5) + (7900452523447757/100000000000000 : ℝ)*(sp6) + (1977804153672081/50000000000000 : ℝ)*(sp7) + (1977804153672081/50000000000000 : ℝ)*(f.failure) + (3950231881394967/50000000000000 : ℝ)*(f.sum) + (34335165201109/6882500000000000000000000000 : ℝ)*base65 + (10767666654957862229/688250000000000000000000000000000 : ℝ)*base67 + (6177638134803362229/688250000000000000000000000000000 : ℝ)*base69 + (2874514513923362229/688250000000000000000000000000000 : ℝ)*base71 + (15639117192969/6882500000000000000000000000 : ℝ)*base73 + (9767433191492862229/688250000000000000000000000000000 : ℝ)*base75 + (8556344054513637771/688250000000000000000000000000000 : ℝ)*base78 + (13840719460123362229/688250000000000000000000000000000 : ℝ)*base79 + (38120959207709/6882500000000000000000000000 : ℝ)*base81 + (25952679/2500000000000000000000 : ℝ)*base90 + (25952679/2500000000000000000000 : ℝ)*base92 + (25952679/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1162_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74932041/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14097/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (709/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11373/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14067/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1162_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1162_s7_0 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2157356241/10000000000 : ℝ)*x 0 + (5392686663/10000000000 : ℝ)*x 1 + (5266043099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2157356241/10000000000 : ℝ)^8355 ≤ (3277735742271/25000000000000 : ℝ)^6307 := by
    have hnat : (2157356241 : ℕ)^8355*25000000000000^6307 ≤ 3277735742271^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157356241 10000000000 3277735742271 25000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392686663/10000000000 : ℝ)^8355 ≤ (8825663137779/20000000000000 : ℝ)^6307 := by
    have hnat : (5392686663 : ℕ)^8355*20000000000000^6307 ≤ 8825663137779^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392686663 10000000000 8825663137779 20000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266043099/10000000000 : ℝ)^8355 ≤ (42760741321549/100000000000000 : ℝ)^6307 := by
    have hnat : (5266043099 : ℕ)^8355*100000000000000^6307 ≤ 42760741321549^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266043099 10000000000 42760741321549 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2157356241/10000000000 : ℝ), (5392686663/10000000000 : ℝ), (5266043099/10000000000 : ℝ)] ![(3277735742271/25000000000000 : ℝ), (8825663137779/20000000000000 : ℝ), (42760741321549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2157356241/10000000000 : ℝ)|^8355 ≤ (3277735742271/25000000000000 : ℝ)^6307
        have hw : |(-2157356241/10000000000 : ℝ)|=(2157356241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392686663/10000000000 : ℝ)|^8355 ≤ (8825663137779/20000000000000 : ℝ)^6307
        have hw : |(5392686663/10000000000 : ℝ)|=(5392686663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266043099/10000000000 : ℝ)|^8355 ≤ (42760741321549/100000000000000 : ℝ)^6307
        have hw : |(5266043099/10000000000 : ℝ)|=(5266043099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s7_1 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668085649/1250000000 : ℝ)*x 0 + (-444317453/2000000000 : ℝ)*x 1 + (2633021549/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668085649/1250000000 : ℝ)^8355 ≤ (8721745091841/20000000000000 : ℝ)^6307 := by
    have hnat : (668085649 : ℕ)^8355*20000000000000^6307 ≤ 8721745091841^6307*1250000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668085649 1250000000 8721745091841 20000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (444317453/2000000000 : ℝ)^8355 ≤ (13630533217969/100000000000000 : ℝ)^6307 := by
    have hnat : (444317453 : ℕ)^8355*100000000000000^6307 ≤ 13630533217969^6307*2000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      444317453 2000000000 13630533217969 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633021549/5000000000 : ℝ)^8355 ≤ (5345092663849/12500000000000 : ℝ)^6307 := by
    have hnat : (2633021549 : ℕ)^8355*12500000000000^6307 ≤ 5345092663849^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633021549 5000000000 5345092663849 12500000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668085649/1250000000 : ℝ), (-444317453/2000000000 : ℝ), (2633021549/5000000000 : ℝ)] ![(8721745091841/20000000000000 : ℝ), (13630533217969/100000000000000 : ℝ), (5345092663849/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668085649/1250000000 : ℝ)|^8355 ≤ (8721745091841/20000000000000 : ℝ)^6307
        have hw : |(668085649/1250000000 : ℝ)|=(668085649/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-444317453/2000000000 : ℝ)|^8355 ≤ (13630533217969/100000000000000 : ℝ)^6307
        have hw : |(-444317453/2000000000 : ℝ)|=(444317453/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633021549/5000000000 : ℝ)|^8355 ≤ (5345092663849/12500000000000 : ℝ)^6307
        have hw : |(2633021549/5000000000 : ℝ)|=(2633021549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s7_2 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344685191/10000000000 : ℝ)*x 0 + (5266043099/10000000000 : ℝ)*x 1 + (-444317453/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344685191/10000000000 : ℝ)^8355 ≤ (43608725448397/100000000000000 : ℝ)^6307 := by
    have hnat : (5344685191 : ℕ)^8355*100000000000000^6307 ≤ 43608725448397^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344685191 10000000000 43608725448397 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266043099/10000000000 : ℝ)^8355 ≤ (42760741321549/100000000000000 : ℝ)^6307 := by
    have hnat : (5266043099 : ℕ)^8355*100000000000000^6307 ≤ 42760741321549^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266043099 10000000000 42760741321549 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (444317453/2000000000 : ℝ)^8355 ≤ (13630533217969/100000000000000 : ℝ)^6307 := by
    have hnat : (444317453 : ℕ)^8355*100000000000000^6307 ≤ 13630533217969^6307*2000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      444317453 2000000000 13630533217969 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344685191/10000000000 : ℝ), (5266043099/10000000000 : ℝ), (-444317453/2000000000 : ℝ)] ![(43608725448397/100000000000000 : ℝ), (42760741321549/100000000000000 : ℝ), (13630533217969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344685191/10000000000 : ℝ)|^8355 ≤ (43608725448397/100000000000000 : ℝ)^6307
        have hw : |(5344685191/10000000000 : ℝ)|=(5344685191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266043099/10000000000 : ℝ)|^8355 ≤ (42760741321549/100000000000000 : ℝ)^6307
        have hw : |(5266043099/10000000000 : ℝ)|=(5266043099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-444317453/2000000000 : ℝ)|^8355 ≤ (13630533217969/100000000000000 : ℝ)^6307
        have hw : |(-444317453/2000000000 : ℝ)|=(444317453/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s7_3 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4361862421/10000000000 : ℝ)*x 0 + (1059301751/2500000000 : ℝ)*x 1 + (4490149867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4361862421/10000000000 : ℝ)^8355 ≤ (33317066800981/100000000000000 : ℝ)^6307 := by
    have hnat : (4361862421 : ℕ)^8355*100000000000000^6307 ≤ 33317066800981^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4361862421 10000000000 33317066800981 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1059301751/2500000000 : ℝ)^8355 ≤ (4007703124787/12500000000000 : ℝ)^6307 := by
    have hnat : (1059301751 : ℕ)^8355*12500000000000^6307 ≤ 4007703124787^6307*2500000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059301751 2500000000 4007703124787 12500000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4490149867/10000000000 : ℝ)^8355 ≤ (17310654092907/50000000000000 : ℝ)^6307 := by
    have hnat : (4490149867 : ℕ)^8355*50000000000000^6307 ≤ 17310654092907^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490149867 10000000000 17310654092907 50000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4361862421/10000000000 : ℝ), (1059301751/2500000000 : ℝ), (4490149867/10000000000 : ℝ)] ![(33317066800981/100000000000000 : ℝ), (4007703124787/12500000000000 : ℝ), (17310654092907/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4361862421/10000000000 : ℝ)|^8355 ≤ (33317066800981/100000000000000 : ℝ)^6307
        have hw : |(4361862421/10000000000 : ℝ)|=(4361862421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1059301751/2500000000 : ℝ)|^8355 ≤ (4007703124787/12500000000000 : ℝ)^6307
        have hw : |(1059301751/2500000000 : ℝ)|=(1059301751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4490149867/10000000000 : ℝ)|^8355 ≤ (17310654092907/50000000000000 : ℝ)^6307
        have hw : |(4490149867/10000000000 : ℝ)|=(4490149867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s7_4 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-269670089/1250000000 : ℝ)*x 0 + (5266361287/10000000000 : ℝ)*x 1 + (1078473519/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269670089/1250000000 : ℝ)^8355 ≤ (2622195792789/20000000000000 : ℝ)^6307 := by
    have hnat : (269670089 : ℕ)^8355*20000000000000^6307 ≤ 2622195792789^6307*1250000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269670089 1250000000 2622195792789 20000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266361287/10000000000 : ℝ)^8355 ≤ (42764164050411/100000000000000 : ℝ)^6307 := by
    have hnat : (5266361287 : ℕ)^8355*100000000000000^6307 ≤ 42764164050411^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266361287 10000000000 42764164050411 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078473519/2000000000 : ℝ)^8355 ≤ (4412485697319/10000000000000 : ℝ)^6307 := by
    have hnat : (1078473519 : ℕ)^8355*10000000000000^6307 ≤ 4412485697319^6307*2000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078473519 2000000000 4412485697319 10000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-269670089/1250000000 : ℝ), (5266361287/10000000000 : ℝ), (1078473519/2000000000 : ℝ)] ![(2622195792789/20000000000000 : ℝ), (42764164050411/100000000000000 : ℝ), (4412485697319/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-269670089/1250000000 : ℝ)|^8355 ≤ (2622195792789/20000000000000 : ℝ)^6307
        have hw : |(-269670089/1250000000 : ℝ)|=(269670089/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266361287/10000000000 : ℝ)|^8355 ≤ (42764164050411/100000000000000 : ℝ)^6307
        have hw : |(5266361287/10000000000 : ℝ)|=(5266361287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078473519/2000000000 : ℝ)|^8355 ≤ (4412485697319/10000000000000 : ℝ)^6307
        have hw : |(1078473519/2000000000 : ℝ)|=(1078473519/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s7_5 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328138133/2500000000 : ℝ)*x 0 + (-65476989/312500000 : ℝ)*x 1 + (2696183263/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328138133/2500000000 : ℝ)^8355 ≤ (43261751516399/100000000000000 : ℝ)^6307 := by
    have hnat : (1328138133 : ℕ)^8355*100000000000000^6307 ≤ 43261751516399^6307*2500000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328138133 2500000000 43261751516399 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65476989/312500000 : ℝ)^8355 ≤ (12613403086347/100000000000000 : ℝ)^6307 := by
    have hnat : (65476989 : ℕ)^8355*100000000000000^6307 ≤ 12613403086347^6307*312500000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65476989 312500000 12613403086347 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696183263/5000000000 : ℝ)^8355 ≤ (44124845385279/100000000000000 : ℝ)^6307 := by
    have hnat : (2696183263 : ℕ)^8355*100000000000000^6307 ≤ 44124845385279^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696183263 5000000000 44124845385279 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328138133/2500000000 : ℝ), (-65476989/312500000 : ℝ), (2696183263/5000000000 : ℝ)] ![(43261751516399/100000000000000 : ℝ), (12613403086347/100000000000000 : ℝ), (44124845385279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328138133/2500000000 : ℝ)|^8355 ≤ (43261751516399/100000000000000 : ℝ)^6307
        have hw : |(1328138133/2500000000 : ℝ)|=(1328138133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-65476989/312500000 : ℝ)|^8355 ≤ (12613403086347/100000000000000 : ℝ)^6307
        have hw : |(-65476989/312500000 : ℝ)|=(65476989/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696183263/5000000000 : ℝ)|^8355 ≤ (44124845385279/100000000000000 : ℝ)^6307
        have hw : |(2696183263/5000000000 : ℝ)|=(2696183263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s7_6 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328137993/2500000000 : ℝ)*x 0 + (5392367411/10000000000 : ℝ)*x 1 + (-1047631601/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328137993/2500000000 : ℝ)^8355 ≤ (10815436368837/25000000000000 : ℝ)^6307 := by
    have hnat : (1328137993 : ℕ)^8355*25000000000000^6307 ≤ 10815436368837^6307*2500000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328137993 2500000000 10815436368837 25000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392367411/10000000000 : ℝ)^8355 ≤ (22062427489319/50000000000000 : ℝ)^6307 := by
    have hnat : (5392367411 : ℕ)^8355*50000000000000^6307 ≤ 22062427489319^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392367411 10000000000 22062427489319 50000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1047631601/5000000000 : ℝ)^8355 ≤ (12613399529607/100000000000000 : ℝ)^6307 := by
    have hnat : (1047631601 : ℕ)^8355*100000000000000^6307 ≤ 12613399529607^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047631601 5000000000 12613399529607 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328137993/2500000000 : ℝ), (5392367411/10000000000 : ℝ), (-1047631601/5000000000 : ℝ)] ![(10815436368837/25000000000000 : ℝ), (22062427489319/50000000000000 : ℝ), (12613399529607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328137993/2500000000 : ℝ)|^8355 ≤ (10815436368837/25000000000000 : ℝ)^6307
        have hw : |(1328137993/2500000000 : ℝ)|=(1328137993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392367411/10000000000 : ℝ)|^8355 ≤ (22062427489319/50000000000000 : ℝ)^6307
        have hw : |(5392367411/10000000000 : ℝ)|=(5392367411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1047631601/5000000000 : ℝ)|^8355 ≤ (12613399529607/100000000000000 : ℝ)^6307
        have hw : |(-1047631601/5000000000 : ℝ)|=(1047631601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s7_7 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4361871861/10000000000 : ℝ)*x 0 + (1122378431/2500000000 : ℝ)*x 1 + (2118922839/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4361871861/10000000000 : ℝ)^8355 ≤ (33317162320157/100000000000000 : ℝ)^6307 := by
    have hnat : (4361871861 : ℕ)^8355*100000000000000^6307 ≤ 33317162320157^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4361871861 10000000000 33317162320157 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1122378431/2500000000 : ℝ)^8355 ≤ (540856415859/1562500000000 : ℝ)^6307 := by
    have hnat : (1122378431 : ℕ)^8355*1562500000000^6307 ≤ 540856415859^6307*2500000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122378431 2500000000 540856415859 1562500000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2118922839/5000000000 : ℝ)^8355 ≤ (6413605410469/20000000000000 : ℝ)^6307 := by
    have hnat : (2118922839 : ℕ)^8355*20000000000000^6307 ≤ 6413605410469^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118922839 5000000000 6413605410469 20000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4361871861/10000000000 : ℝ), (1122378431/2500000000 : ℝ), (2118922839/5000000000 : ℝ)] ![(33317162320157/100000000000000 : ℝ), (540856415859/1562500000000 : ℝ), (6413605410469/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4361871861/10000000000 : ℝ)|^8355 ≤ (33317162320157/100000000000000 : ℝ)^6307
        have hw : |(4361871861/10000000000 : ℝ)|=(4361871861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1122378431/2500000000 : ℝ)|^8355 ≤ (540856415859/1562500000000 : ℝ)^6307
        have hw : |(1122378431/2500000000 : ℝ)|=(1122378431/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2118922839/5000000000 : ℝ)|^8355 ≤ (6413605410469/20000000000000 : ℝ)^6307
        have hw : |(2118922839/5000000000 : ℝ)|=(2118922839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1162_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74932041/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14067/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11373/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11379/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14061/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14067/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11373/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14067/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11373/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14067/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11373/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14067/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11373/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14067/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11373/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14067/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11373/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11373/100000 : ℝ) ^ (4177/1024 : ℝ) ≤ (7043498092466717/50000000000000000000 : ℝ) := by
    have hpowers : (11373/100000 : ℝ)^4177 ≤ (7043498092466717/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11373 : ℕ)^4177*50000000000000000000^1024 ≤ 7043498092466717^1024*100000^4177 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11373 100000 7043498092466717 50000000000000000000 4177 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11373/100000 : ℝ)) (X := (7043498092466717/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14067/100000 : ℝ) ^ (4177/1024 : ℝ) ≤ (6705904313941911/20000000000000000000 : ℝ) := by
    have hpowers : (14067/100000 : ℝ)^4177 ≤ (6705904313941911/20000000000000000000 : ℝ)^1024 := by
      have hnat : (14067 : ℕ)^4177*20000000000000000000^1024 ≤ 6705904313941911^1024*100000^4177 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14067 100000 6705904313941911 20000000000000000000 4177 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14067/100000 : ℝ)) (X := (6705904313941911/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007043498092466717/25000000000000000000 : ℝ) ≤ (10000690617689679/10000000000000000 : ℝ) ^ (4177/1024 : ℝ) := by
    have hpowers : (25007043498092466717/25000000000000000000 : ℝ)^1024 ≤ (10000690617689679/10000000000000000 : ℝ)^4177 := by
      have hnat : (25007043498092466717 : ℕ)^1024*10000000000000000^4177 ≤ 10000690617689679^4177*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007043498092466717 25000000000000000000 10000690617689679 10000000000000000 1024 4177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000690617689679/10000000000000000 : ℝ)) (X := (25007043498092466717/25000000000000000000 : ℝ)) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047616517754642989/100000000000000000000 : ℝ) ≤ (5000583559418051/5000000000000000 : ℝ) ^ (4177/1024 : ℝ) := by
    have hpowers : (100047616517754642989/100000000000000000000 : ℝ)^1024 ≤ (5000583559418051/5000000000000000 : ℝ)^4177 := by
      have hnat : (100047616517754642989 : ℕ)^1024*5000000000000000^4177 ≤ 5000583559418051^4177*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047616517754642989 100000000000000000000 5000583559418051 5000000000000000 1024 4177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000583559418051/5000000000000000 : ℝ)) (X := (100047616517754642989/100000000000000000000 : ℝ)) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006705904313941911/10000000000000000000 : ℝ) ≤ (400065744799301/400000000000000 : ℝ) ^ (4177/1024 : ℝ) := by
    have hpowers : (10006705904313941911/10000000000000000000 : ℝ)^1024 ≤ (400065744799301/400000000000000 : ℝ)^4177 := by
      have hnat : (10006705904313941911 : ℕ)^1024*400000000000000^4177 ≤ 400065744799301^4177*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006705904313941911 10000000000000000000 400065744799301 400000000000000 1024 4177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400065744799301/400000000000000 : ℝ)) (X := (10006705904313941911/10000000000000000000 : ℝ)) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7043498092466717/50000000000000000000 : ℝ) ≤ ((2244251835748288139/2245000000000000000 : ℝ)+2*(476501146423/269400000000000 : ℝ)*(11373/100000 : ℝ))^(4177/1024 : ℝ) := by
    rw [show (2244251835748288139/2245000000000000000 : ℝ)+2*(476501146423/269400000000000 : ℝ)*(11373/100000 : ℝ)=(10000690617689679/10000000000000000 : ℝ) by norm_num, show 1+2*(7043498092466717/50000000000000000000 : ℝ)=(25007043498092466717/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6705904313941911/20000000000000000000 : ℝ)+(7043498092466717/50000000000000000000 : ℝ) ≤ ((2244251835748288139/2245000000000000000 : ℝ)+(476501146423/269400000000000 : ℝ)*((14067/100000 : ℝ)+(11373/100000 : ℝ)))^(4177/1024 : ℝ) := by
    rw [show (2244251835748288139/2245000000000000000 : ℝ)+(476501146423/269400000000000 : ℝ)*((14067/100000 : ℝ)+(11373/100000 : ℝ))=(5000583559418051/5000000000000000 : ℝ) by norm_num, show 1+(6705904313941911/20000000000000000000 : ℝ)+(7043498092466717/50000000000000000000 : ℝ)=(100047616517754642989/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6705904313941911/20000000000000000000 : ℝ) ≤ ((2244251835748288139/2245000000000000000 : ℝ)+2*(476501146423/269400000000000 : ℝ)*(14067/100000 : ℝ))^(4177/1024 : ℝ) := by
    rw [show (2244251835748288139/2245000000000000000 : ℝ)+2*(476501146423/269400000000000 : ℝ)*(14067/100000 : ℝ)=(400065744799301/400000000000000 : ℝ) by norm_num, show 1+2*(6705904313941911/20000000000000000000 : ℝ)=(10006705904313941911/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2244251835748288139/2245000000000000000 : ℝ)*(X 1 0+X 2 0)+(476501146423/269400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4177/1024 : ℝ)) (lo := (11373/100000 : ℝ)) (hi := (14067/100000 : ℝ)) (c := (2244251835748288139/2245000000000000000 : ℝ)) (alpha := (476501146423/269400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2244251835748288139/2245000000000000000 : ℝ)*(X 0 1+X 2 1)+(476501146423/269400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4177/1024 : ℝ)) (lo := (11373/100000 : ℝ)) (hi := (14067/100000 : ℝ)) (c := (2244251835748288139/2245000000000000000 : ℝ)) (alpha := (476501146423/269400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2244251835748288139/2245000000000000000 : ℝ)*(X 0 2+X 1 2)+(476501146423/269400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4177/1024 : ℝ)) (lo := (11373/100000 : ℝ)) (hi := (14067/100000 : ℝ)) (c := (2244251835748288139/2245000000000000000 : ℝ)) (alpha := (476501146423/269400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2157356241/10000000000 : ℝ)*X 0 0+(5392686663/10000000000 : ℝ)*X 0 1+(5266043099/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668085649/1250000000 : ℝ)*X 1 0+(-444317453/2000000000 : ℝ)*X 1 1+(2633021549/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344685191/10000000000 : ℝ)*X 2 0+(5266043099/10000000000 : ℝ)*X 2 1+(-444317453/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4361862421/10000000000 : ℝ)*X 0 0+(1059301751/2500000000 : ℝ)*X 0 1+(4490149867/10000000000 : ℝ)*X 0 2+(4361862421/10000000000 : ℝ)*X 1 0+(1059301751/2500000000 : ℝ)*X 1 1+(4490149867/10000000000 : ℝ)*X 1 2+(4361862421/10000000000 : ℝ)*X 2 0+(1059301751/2500000000 : ℝ)*X 2 1+(4490149867/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-269670089/1250000000 : ℝ)*X 0 0+(5266361287/10000000000 : ℝ)*X 0 1+(1078473519/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328138133/2500000000 : ℝ)*X 1 0+(-65476989/312500000 : ℝ)*X 1 1+(2696183263/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328137993/2500000000 : ℝ)*X 2 0+(5392367411/10000000000 : ℝ)*X 2 1+(-1047631601/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4361871861/10000000000 : ℝ)*X 0 0+(1122378431/2500000000 : ℝ)*X 0 1+(2118922839/5000000000 : ℝ)*X 0 2+(4361871861/10000000000 : ℝ)*X 1 0+(1122378431/2500000000 : ℝ)*X 1 1+(2118922839/5000000000 : ℝ)*X 1 2+(4361871861/10000000000 : ℝ)*X 2 0+(1122378431/2500000000 : ℝ)*X 2 1+(2118922839/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (246273751174478658277415971/112250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (216190361/50000000000000 : ℝ)*(base19) + (199793329/50000000000000 : ℝ)*(base23) + (4184443/25000000000000 : ℝ)*(lower2) + (54966399/100000000000000 : ℝ)*(upper3) + (15778239/50000000000000 : ℝ)*(upper5) + (5924837716198163/100000000000000 : ℝ)*(major0) + (5924837716198163/100000000000000 : ℝ)*(major1) + (5924837716198163/100000000000000 : ℝ)*(major2) + (7896189436913807/100000000000000 : ℝ)*(sp0) + (1579240158820621/20000000000000 : ℝ)*(sp1) + (7896200826897169/100000000000000 : ℝ)*(sp2) + (247091733586553/6250000000000 : ℝ)*(sp3) + (11789570019/100000000000000 : ℝ)*(sp4) + (6395395123/100000000000000 : ℝ)*(sp7) + (395347413277997/10000000000000 : ℝ)*(f.failure) + (3948100613241913/50000000000000 : ℝ)*(f.sum) + (76873381438171/13470000000000000000000000000 : ℝ)*base66 + (5114486553920190971/673500000000000000000000000000000 : ℝ)*base67 + (3425555320524809029/673500000000000000000000000000000 : ℝ)*base70 + (9922200211344690971/673500000000000000000000000000000 : ℝ)*base71 + (21823750666981/13470000000000000000000000000 : ℝ)*base74 + (21297764881986809029/673500000000000000000000000000000 : ℝ)*base76 + (8544767789301809029/673500000000000000000000000000000 : ℝ)*base78 + (11768930141699309029/673500000000000000000000000000000 : ℝ)*base80 + (23535057208199/13470000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (601877/500000000000000000000 : ℝ)*base89 + (601877/500000000000000000000 : ℝ)*base91 + (601877/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (93535176150117042271708319/14031250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (131949633/25000000000000 : ℝ)*(base19) + (16284209/20000000000000 : ℝ)*(lower2) + (28429387/25000000000000 : ℝ)*(lower3) + (85101373/50000000000000 : ℝ)*(lower4) + (1488709758840293/25000000000000 : ℝ)*(major0) + (1488709758840293/25000000000000 : ℝ)*(major1) + (1488709758840293/25000000000000 : ℝ)*(major2) + (19452694987/50000000000000 : ℝ)*(sp0) + (23417790119/100000000000000 : ℝ)*(sp2) + (1446196659/25000000000000 : ℝ)*(sp3) + (1587229158254003/20000000000000 : ℝ)*(sp4) + (496011510553841/6250000000000 : ℝ)*(sp5) + (7936161278869869/100000000000000 : ℝ)*(sp6) + (496685920883613/12500000000000 : ℝ)*(sp7) + (198674657592777/5000000000000 : ℝ)*(f.failure) + (1984046174164997/25000000000000 : ℝ)*(f.sum) + (11598430532167/1683750000000000000000000000 : ℝ)*base65 + (387308342651095819/168375000000000000000000000000000 : ℝ)*base68 + (1793507460711904181/168375000000000000000000000000000 : ℝ)*base69 + (1084599037224529181/168375000000000000000000000000000 : ℝ)*base71 + (7031663874421/3367500000000000000000000000 : ℝ)*base74 + (2197882163682529181/168375000000000000000000000000000 : ℝ)*base75 + (3471693033682654181/168375000000000000000000000000000 : ℝ)*base77 + (735390585732529181/168375000000000000000000000000000 : ℝ)*base79 + (17879336311607/6735000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (2532143/250000000000000000000 : ℝ)*base90 + (2532143/250000000000000000000 : ℝ)*base92 + (2532143/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1162_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74932041/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14067/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11373/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11379/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14061/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1162_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1162_s8_0 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-431472101/2000000000 : ℝ)*x 0 + (337039223/625000000 : ℝ)*x 1 + (5266099461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431472101/2000000000 : ℝ)^8355 ≤ (13110977297441/100000000000000 : ℝ)^6307 := by
    have hnat : (431472101 : ℕ)^8355*100000000000000^6307 ≤ 13110977297441^6307*2000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431472101 2000000000 13110977297441 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337039223/625000000 : ℝ)^8355 ≤ (22063837545319/50000000000000 : ℝ)^6307 := by
    have hnat : (337039223 : ℕ)^8355*50000000000000^6307 ≤ 22063837545319^6307*625000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337039223 625000000 22063837545319 50000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266099461/10000000000 : ℝ)^8355 ≤ (42761347599243/100000000000000 : ℝ)^6307 := by
    have hnat : (5266099461 : ℕ)^8355*100000000000000^6307 ≤ 42761347599243^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266099461 10000000000 42761347599243 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-431472101/2000000000 : ℝ), (337039223/625000000 : ℝ), (5266099461/10000000000 : ℝ)] ![(13110977297441/100000000000000 : ℝ), (22063837545319/50000000000000 : ℝ), (42761347599243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-431472101/2000000000 : ℝ)|^8355 ≤ (13110977297441/100000000000000 : ℝ)^6307
        have hw : |(-431472101/2000000000 : ℝ)|=(431472101/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337039223/625000000 : ℝ)|^8355 ≤ (22063837545319/50000000000000 : ℝ)^6307
        have hw : |(337039223/625000000 : ℝ)|=(337039223/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266099461/10000000000 : ℝ)|^8355 ≤ (42761347599243/100000000000000 : ℝ)^6307
        have hw : |(5266099461/10000000000 : ℝ)|=(5266099461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s8_1 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344670561/10000000000 : ℝ)*x 0 + (-222153209/1000000000 : ℝ)*x 1 + (164565609/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344670561/10000000000 : ℝ)^8355 ≤ (43608567316667/100000000000000 : ℝ)^6307 := by
    have hnat : (5344670561 : ℕ)^8355*100000000000000^6307 ≤ 43608567316667^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344670561 10000000000 43608567316667 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (222153209/1000000000 : ℝ)^8355 ≤ (6815042384163/50000000000000 : ℝ)^6307 := by
    have hnat : (222153209 : ℕ)^8355*50000000000000^6307 ≤ 6815042384163^6307*1000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222153209 1000000000 6815042384163 50000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164565609/312500000 : ℝ)^8355 ≤ (21380673944839/50000000000000 : ℝ)^6307 := by
    have hnat : (164565609 : ℕ)^8355*50000000000000^6307 ≤ 21380673944839^6307*312500000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164565609 312500000 21380673944839 50000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344670561/10000000000 : ℝ), (-222153209/1000000000 : ℝ), (164565609/312500000 : ℝ)] ![(43608567316667/100000000000000 : ℝ), (6815042384163/50000000000000 : ℝ), (21380673944839/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344670561/10000000000 : ℝ)|^8355 ≤ (43608567316667/100000000000000 : ℝ)^6307
        have hw : |(5344670561/10000000000 : ℝ)|=(5344670561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-222153209/1000000000 : ℝ)|^8355 ≤ (6815042384163/50000000000000 : ℝ)^6307
        have hw : |(-222153209/1000000000 : ℝ)|=(222153209/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164565609/312500000 : ℝ)|^8355 ≤ (21380673944839/50000000000000 : ℝ)^6307
        have hw : |(164565609/312500000 : ℝ)|=(164565609/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s8_2 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672335263/5000000000 : ℝ)*x 0 + (5266099561/10000000000 : ℝ)*x 1 + (-2221532041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672335263/5000000000 : ℝ)^8355 ≤ (21804283469181/50000000000000 : ℝ)^6307 := by
    have hnat : (2672335263 : ℕ)^8355*50000000000000^6307 ≤ 21804283469181^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672335263 5000000000 21804283469181 50000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266099561/10000000000 : ℝ)^8355 ≤ (4276134867493/10000000000000 : ℝ)^6307 := by
    have hnat : (5266099561 : ℕ)^8355*10000000000000^6307 ≤ 4276134867493^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266099561 10000000000 4276134867493 10000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2221532041/10000000000 : ℝ)^8355 ≤ (13630084370067/100000000000000 : ℝ)^6307 := by
    have hnat : (2221532041 : ℕ)^8355*100000000000000^6307 ≤ 13630084370067^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2221532041 10000000000 13630084370067 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672335263/5000000000 : ℝ), (5266099561/10000000000 : ℝ), (-2221532041/10000000000 : ℝ)] ![(21804283469181/50000000000000 : ℝ), (4276134867493/10000000000000 : ℝ), (13630084370067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672335263/5000000000 : ℝ)|^8355 ≤ (21804283469181/50000000000000 : ℝ)^6307
        have hw : |(2672335263/5000000000 : ℝ)|=(2672335263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266099561/10000000000 : ℝ)|^8355 ≤ (4276134867493/10000000000000 : ℝ)^6307
        have hw : |(5266099561/10000000000 : ℝ)|=(5266099561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2221532041/10000000000 : ℝ)|^8355 ≤ (13630084370067/100000000000000 : ℝ)^6307
        have hw : |(-2221532041/10000000000 : ℝ)|=(2221532041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s8_3 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (272616587/625000000 : ℝ)*x 0 + (529665259/1250000000 : ℝ)*x 1 + (2245017001/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272616587/625000000 : ℝ)^8355 ≤ (16658548431603/50000000000000 : ℝ)^6307 := by
    have hnat : (272616587 : ℕ)^8355*50000000000000^6307 ≤ 16658548431603^6307*625000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272616587 625000000 16658548431603 50000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (529665259/1250000000 : ℝ)^8355 ≤ (16031389207121/50000000000000 : ℝ)^6307 := by
    have hnat : (529665259 : ℕ)^8355*50000000000000^6307 ≤ 16031389207121^6307*1250000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529665259 1250000000 16031389207121 50000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2245017001/5000000000 : ℝ)^8355 ≤ (34620124717303/100000000000000 : ℝ)^6307 := by
    have hnat : (2245017001 : ℕ)^8355*100000000000000^6307 ≤ 34620124717303^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245017001 5000000000 34620124717303 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(272616587/625000000 : ℝ), (529665259/1250000000 : ℝ), (2245017001/5000000000 : ℝ)] ![(16658548431603/50000000000000 : ℝ), (16031389207121/50000000000000 : ℝ), (34620124717303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(272616587/625000000 : ℝ)|^8355 ≤ (16658548431603/50000000000000 : ℝ)^6307
        have hw : |(272616587/625000000 : ℝ)|=(272616587/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(529665259/1250000000 : ℝ)|^8355 ≤ (16031389207121/50000000000000 : ℝ)^6307
        have hw : |(529665259/1250000000 : ℝ)|=(529665259/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2245017001/5000000000 : ℝ)|^8355 ≤ (34620124717303/100000000000000 : ℝ)^6307
        have hw : |(2245017001/5000000000 : ℝ)|=(2245017001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s8_4 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2157365311/10000000000 : ℝ)*x 0 + (1316604207/2500000000 : ℝ)*x 1 + (5392309063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2157365311/10000000000 : ℝ)^8355 ≤ (6555507994663/50000000000000 : ℝ)^6307 := by
    have hnat : (2157365311 : ℕ)^8355*50000000000000^6307 ≤ 6555507994663^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157365311 10000000000 6555507994663 50000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316604207/2500000000 : ℝ)^8355 ≤ (10691190377109/25000000000000 : ℝ)^6307 := by
    have hnat : (1316604207 : ℕ)^8355*25000000000000^6307 ≤ 10691190377109^6307*2500000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316604207 2500000000 10691190377109 25000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392309063/10000000000 : ℝ)^8355 ≤ (22062111245057/50000000000000 : ℝ)^6307 := by
    have hnat : (5392309063 : ℕ)^8355*50000000000000^6307 ≤ 22062111245057^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392309063 10000000000 22062111245057 50000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2157365311/10000000000 : ℝ), (1316604207/2500000000 : ℝ), (5392309063/10000000000 : ℝ)] ![(6555507994663/50000000000000 : ℝ), (10691190377109/25000000000000 : ℝ), (22062111245057/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2157365311/10000000000 : ℝ)|^8355 ≤ (6555507994663/50000000000000 : ℝ)^6307
        have hw : |(-2157365311/10000000000 : ℝ)|=(2157365311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316604207/2500000000 : ℝ)|^8355 ≤ (10691190377109/25000000000000 : ℝ)^6307
        have hw : |(1316604207/2500000000 : ℝ)|=(1316604207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392309063/10000000000 : ℝ)|^8355 ≤ (22062111245057/50000000000000 : ℝ)^6307
        have hw : |(5392309063/10000000000 : ℝ)|=(5392309063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s8_5 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312567531/10000000000 : ℝ)*x 0 + (-1047661659/5000000000 : ℝ)*x 1 + (53923077/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312567531/10000000000 : ℝ)^8355 ≤ (8652382663911/20000000000000 : ℝ)^6307 := by
    have hnat : (5312567531 : ℕ)^8355*20000000000000^6307 ≤ 8652382663911^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312567531 10000000000 8652382663911 20000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1047661659/5000000000 : ℝ)^8355 ≤ (2522775788407/20000000000000 : ℝ)^6307 := by
    have hnat : (1047661659 : ℕ)^8355*20000000000000^6307 ≤ 2522775788407^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047661659 5000000000 2522775788407 20000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53923077/100000000 : ℝ)^8355 ≤ (44124207715309/100000000000000 : ℝ)^6307 := by
    have hnat : (53923077 : ℕ)^8355*100000000000000^6307 ≤ 44124207715309^6307*100000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53923077 100000000 44124207715309 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312567531/10000000000 : ℝ), (-1047661659/5000000000 : ℝ), (53923077/100000000 : ℝ)] ![(8652382663911/20000000000000 : ℝ), (2522775788407/20000000000000 : ℝ), (44124207715309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312567531/10000000000 : ℝ)|^8355 ≤ (8652382663911/20000000000000 : ℝ)^6307
        have hw : |(5312567531/10000000000 : ℝ)|=(5312567531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1047661659/5000000000 : ℝ)|^8355 ≤ (2522775788407/20000000000000 : ℝ)^6307
        have hw : |(-1047661659/5000000000 : ℝ)|=(1047661659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(53923077/100000000 : ℝ)|^8355 ≤ (44124207715309/100000000000000 : ℝ)^6307
        have hw : |(53923077/100000000 : ℝ)|=(53923077/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s8_6 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (26562833/50000000 : ℝ)*x 0 + (539230877/1000000000 : ℝ)*x 1 + (-3352517/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26562833/50000000 : ℝ)^8355 ≤ (21630951638149/50000000000000 : ℝ)^6307 := by
    have hnat : (26562833 : ℕ)^8355*50000000000000^6307 ≤ 21630951638149^6307*50000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26562833 50000000 21630951638149 50000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539230877/1000000000 : ℝ)^8355 ≤ (22062109657009/50000000000000 : ℝ)^6307 := by
    have hnat : (539230877 : ℕ)^8355*50000000000000^6307 ≤ 22062109657009^6307*1000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539230877 1000000000 22062109657009 50000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3352517/16000000 : ℝ)^8355 ≤ (6306938701447/50000000000000 : ℝ)^6307 := by
    have hnat : (3352517 : ℕ)^8355*50000000000000^6307 ≤ 6306938701447^6307*16000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3352517 16000000 6306938701447 50000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26562833/50000000 : ℝ), (539230877/1000000000 : ℝ), (-3352517/16000000 : ℝ)] ![(21630951638149/50000000000000 : ℝ), (22062109657009/50000000000000 : ℝ), (6306938701447/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26562833/50000000 : ℝ)|^8355 ≤ (21630951638149/50000000000000 : ℝ)^6307
        have hw : |(26562833/50000000 : ℝ)|=(26562833/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539230877/1000000000 : ℝ)|^8355 ≤ (22062109657009/50000000000000 : ℝ)^6307
        have hw : |(539230877/1000000000 : ℝ)|=(539230877/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3352517/16000000 : ℝ)|^8355 ≤ (6306938701447/50000000000000 : ℝ)^6307
        have hw : |(-3352517/16000000 : ℝ)|=(3352517/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s8_7 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2180937657/5000000000 : ℝ)*x 0 + (4489398757/10000000000 : ℝ)*x 1 + (1059489833/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180937657/5000000000 : ℝ)^8355 ≤ (666343945191/2000000000000 : ℝ)^6307 := by
    have hnat : (2180937657 : ℕ)^8355*2000000000000^6307 ≤ 666343945191^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180937657 5000000000 666343945191 2000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4489398757/10000000000 : ℝ)^8355 ≤ (17306818186403/50000000000000 : ℝ)^6307 := by
    have hnat : (4489398757 : ℕ)^8355*50000000000000^6307 ≤ 17306818186403^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489398757 10000000000 17306818186403 50000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1059489833/2500000000 : ℝ)^8355 ≤ (16034583175183/50000000000000 : ℝ)^6307 := by
    have hnat : (1059489833 : ℕ)^8355*50000000000000^6307 ≤ 16034583175183^6307*2500000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059489833 2500000000 16034583175183 50000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180937657/5000000000 : ℝ), (4489398757/10000000000 : ℝ), (1059489833/2500000000 : ℝ)] ![(666343945191/2000000000000 : ℝ), (17306818186403/50000000000000 : ℝ), (16034583175183/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180937657/5000000000 : ℝ)|^8355 ≤ (666343945191/2000000000000 : ℝ)^6307
        have hw : |(2180937657/5000000000 : ℝ)|=(2180937657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4489398757/10000000000 : ℝ)|^8355 ≤ (17306818186403/50000000000000 : ℝ)^6307
        have hw : |(4489398757/10000000000 : ℝ)|=(4489398757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1059489833/2500000000 : ℝ)|^8355 ≤ (16034583175183/50000000000000 : ℝ)^6307
        have hw : |(1059489833/2500000000 : ℝ)|=(1059489833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1162_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74932041/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14061/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11379/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (569/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (703/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14061/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11379/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14061/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11379/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14061/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11379/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14061/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11379/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14061/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11379/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14061/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11379/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11379/100000 : ℝ) ^ (4177/1024 : ℝ) ≤ (3529333981193053/25000000000000000000 : ℝ) := by
    have hpowers : (11379/100000 : ℝ)^4177 ≤ (3529333981193053/25000000000000000000 : ℝ)^1024 := by
      have hnat : (11379 : ℕ)^4177*25000000000000000000^1024 ≤ 3529333981193053^1024*100000^4177 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11379 100000 3529333981193053 25000000000000000000 4177 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11379/100000 : ℝ)) (X := (3529333981193053/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14061/100000 : ℝ) ^ (4177/1024 : ℝ) ≤ (8367805798899581/25000000000000000000 : ℝ) := by
    have hpowers : (14061/100000 : ℝ)^4177 ≤ (8367805798899581/25000000000000000000 : ℝ)^1024 := by
      have hnat : (14061 : ℕ)^4177*25000000000000000000^1024 ≤ 8367805798899581^1024*100000^4177 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14061 100000 8367805798899581 25000000000000000000 4177 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14061/100000 : ℝ)) (X := (8367805798899581/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503529333981193053/12500000000000000000 : ℝ) ≤ (5000346052471387/5000000000000000 : ℝ) ^ (4177/1024 : ℝ) := by
    have hpowers : (12503529333981193053/12500000000000000000 : ℝ)^1024 ≤ (5000346052471387/5000000000000000 : ℝ)^4177 := by
      have hnat : (12503529333981193053 : ℕ)^1024*5000000000000000^4177 ≤ 5000346052471387^4177*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503529333981193053 12500000000000000000 5000346052471387 5000000000000000 1024 4177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000346052471387/5000000000000000 : ℝ)) (X := (12503529333981193053/12500000000000000000 : ℝ)) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505948569890046317/12500000000000000000 : ℝ) ≤ (10001166433670711/10000000000000000 : ℝ) ^ (4177/1024 : ℝ) := by
    have hpowers : (12505948569890046317/12500000000000000000 : ℝ)^1024 ≤ (10001166433670711/10000000000000000 : ℝ)^4177 := by
      have hnat : (12505948569890046317 : ℕ)^1024*10000000000000000^4177 ≤ 10001166433670711^4177*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505948569890046317 12500000000000000000 10001166433670711 10000000000000000 1024 4177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001166433670711/10000000000000000 : ℝ)) (X := (12505948569890046317/12500000000000000000 : ℝ)) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508367805798899581/12500000000000000000 : ℝ) ≤ (1250205095299831/1250000000000000 : ℝ) ^ (4177/1024 : ℝ) := by
    have hpowers : (12508367805798899581/12500000000000000000 : ℝ)^1024 ≤ (1250205095299831/1250000000000000 : ℝ)^4177 := by
      have hnat : (12508367805798899581 : ℕ)^1024*1250000000000000^4177 ≤ 1250205095299831^4177*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508367805798899581 12500000000000000000 1250205095299831 1250000000000000 1024 4177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250205095299831/1250000000000000 : ℝ)) (X := (12508367805798899581/12500000000000000000 : ℝ)) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3529333981193053/25000000000000000000 : ℝ) ≤ ((1489503414014784979/1490000000000000000 : ℝ)+2*(52703191993/29800000000000 : ℝ)*(11379/100000 : ℝ))^(4177/1024 : ℝ) := by
    rw [show (1489503414014784979/1490000000000000000 : ℝ)+2*(52703191993/29800000000000 : ℝ)*(11379/100000 : ℝ)=(5000346052471387/5000000000000000 : ℝ) by norm_num, show 1+2*(3529333981193053/25000000000000000000 : ℝ)=(12503529333981193053/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8367805798899581/25000000000000000000 : ℝ)+(3529333981193053/25000000000000000000 : ℝ) ≤ ((1489503414014784979/1490000000000000000 : ℝ)+(52703191993/29800000000000 : ℝ)*((14061/100000 : ℝ)+(11379/100000 : ℝ)))^(4177/1024 : ℝ) := by
    rw [show (1489503414014784979/1490000000000000000 : ℝ)+(52703191993/29800000000000 : ℝ)*((14061/100000 : ℝ)+(11379/100000 : ℝ))=(10001166433670711/10000000000000000 : ℝ) by norm_num, show 1+(8367805798899581/25000000000000000000 : ℝ)+(3529333981193053/25000000000000000000 : ℝ)=(12505948569890046317/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8367805798899581/25000000000000000000 : ℝ) ≤ ((1489503414014784979/1490000000000000000 : ℝ)+2*(52703191993/29800000000000 : ℝ)*(14061/100000 : ℝ))^(4177/1024 : ℝ) := by
    rw [show (1489503414014784979/1490000000000000000 : ℝ)+2*(52703191993/29800000000000 : ℝ)*(14061/100000 : ℝ)=(1250205095299831/1250000000000000 : ℝ) by norm_num, show 1+2*(8367805798899581/25000000000000000000 : ℝ)=(12508367805798899581/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1489503414014784979/1490000000000000000 : ℝ)*(X 1 0+X 2 0)+(52703191993/29800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4177/1024 : ℝ)) (lo := (11379/100000 : ℝ)) (hi := (14061/100000 : ℝ)) (c := (1489503414014784979/1490000000000000000 : ℝ)) (alpha := (52703191993/29800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1489503414014784979/1490000000000000000 : ℝ)*(X 0 1+X 2 1)+(52703191993/29800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4177/1024 : ℝ)) (lo := (11379/100000 : ℝ)) (hi := (14061/100000 : ℝ)) (c := (1489503414014784979/1490000000000000000 : ℝ)) (alpha := (52703191993/29800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1489503414014784979/1490000000000000000 : ℝ)*(X 0 2+X 1 2)+(52703191993/29800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4177/1024 : ℝ)) (lo := (11379/100000 : ℝ)) (hi := (14061/100000 : ℝ)) (c := (1489503414014784979/1490000000000000000 : ℝ)) (alpha := (52703191993/29800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-431472101/2000000000 : ℝ)*X 0 0+(337039223/625000000 : ℝ)*X 0 1+(5266099461/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344670561/10000000000 : ℝ)*X 1 0+(-222153209/1000000000 : ℝ)*X 1 1+(164565609/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672335263/5000000000 : ℝ)*X 2 0+(5266099561/10000000000 : ℝ)*X 2 1+(-2221532041/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((272616587/625000000 : ℝ)*X 0 0+(529665259/1250000000 : ℝ)*X 0 1+(2245017001/5000000000 : ℝ)*X 0 2+(272616587/625000000 : ℝ)*X 1 0+(529665259/1250000000 : ℝ)*X 1 1+(2245017001/5000000000 : ℝ)*X 1 2+(272616587/625000000 : ℝ)*X 2 0+(529665259/1250000000 : ℝ)*X 2 1+(2245017001/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2157365311/10000000000 : ℝ)*X 0 0+(1316604207/2500000000 : ℝ)*X 0 1+(5392309063/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312567531/10000000000 : ℝ)*X 1 0+(-1047661659/5000000000 : ℝ)*X 1 1+(53923077/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((26562833/50000000 : ℝ)*X 2 0+(539230877/1000000000 : ℝ)*X 2 1+(-3352517/16000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2180937657/5000000000 : ℝ)*X 0 0+(4489398757/10000000000 : ℝ)*X 0 1+(1059489833/2500000000 : ℝ)*X 0 2+(2180937657/5000000000 : ℝ)*X 1 0+(4489398757/10000000000 : ℝ)*X 1 1+(1059489833/2500000000 : ℝ)*X 1 2+(2180937657/5000000000 : ℝ)*X 2 0+(4489398757/10000000000 : ℝ)*X 2 1+(1059489833/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (291447243268267734606897789/74500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (879625301/100000000000000 : ℝ)*(base19) + (46798797/6250000000000 : ℝ)*(base23) + (5283759/12500000000000 : ℝ)*(lower2) + (20226501/25000000000000 : ℝ)*(upper3) + (92802573/100000000000000 : ℝ)*(upper5) + (5930267365583401/100000000000000 : ℝ)*(major0) + (5930267365583401/100000000000000 : ℝ)*(major1) + (5930267365583401/100000000000000 : ℝ)*(major2) + (1580681829055493/20000000000000 : ℝ)*(sp0) + (7903436539185921/100000000000000 : ℝ)*(sp1) + (790343667003047/10000000000000 : ℝ)*(sp2) + (395708598754501/10000000000000 : ℝ)*(sp3) + (14136766879/50000000000000 : ℝ)*(sp4) + (5597204551/50000000000000 : ℝ)*(sp7) + (61829643468033/1562500000000 : ℝ)*(f.failure) + (3951718709405611/50000000000000 : ℝ)*(f.sum) + (8145014964543/1490000000000000000000000000 : ℝ)*base65 + (2118640725294183579/149000000000000000000000000000000 : ℝ)*base67 + (997567209869183579/149000000000000000000000000000000 : ℝ)*base69 + (2058773724595183579/149000000000000000000000000000000 : ℝ)*base71 + (8116364262633/1490000000000000000000000000 : ℝ)*base73 + (3220183323848183579/149000000000000000000000000000000 : ℝ)*base75 + (1215946949284183579/149000000000000000000000000000000 : ℝ)*base77 + (1373910575320183579/149000000000000000000000000000000 : ℝ)*base79 + (6848806206667/1490000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1085897/78125000000000000000 : ℝ)*base90 + (1085897/78125000000000000000 : ℝ)*base92 + (1085897/78125000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (198957224749370551058643153/37250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1118665881/50000000000000 : ℝ)*(base19) + (236743309/20000000000000 : ℝ)*(base23) + (323432531/100000000000000 : ℝ)*(lower1) + (90560223/50000000000000 : ℝ)*(lower4) + (333842603/100000000000000 : ℝ)*(upper5) + (5960203088907569/100000000000000 : ℝ)*(major0) + (5960203088907569/100000000000000 : ℝ)*(major1) + (5960203088907569/100000000000000 : ℝ)*(major2) + (15072907013/50000000000000 : ℝ)*(sp0) + (416284717/100000000000000 : ℝ)*(sp1) + (1588660684630787/20000000000000 : ℝ)*(sp4) + (7943330915351483/100000000000000 : ℝ)*(sp5) + (992916548156427/12500000000000 : ℝ)*(sp6) + (497134053851173/12500000000000 : ℝ)*(sp7) + (497134053851173/12500000000000 : ℝ)*(f.failure) + (7943333568967961/100000000000000 : ℝ)*(f.sum) + (1525901450127/1490000000000000000000000000 : ℝ)*base65 + (1026205078472543949/149000000000000000000000000000000 : ℝ)*base68 + (217120438179543949/149000000000000000000000000000000 : ℝ)*base70 + (1109054837322543949/149000000000000000000000000000000 : ℝ)*base72 + (2029435085343/1490000000000000000000000000 : ℝ)*base74 + (2239615312824543949/149000000000000000000000000000000 : ℝ)*base76 + (403046779932543949/149000000000000000000000000000000 : ℝ)*base78 + (1264724847099456051/149000000000000000000000000000000 : ℝ)*base79 + (847105072103/1490000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (3115907/625000000000000000000 : ℝ)*base90 + (3115907/625000000000000000000 : ℝ)*base92 + (3115907/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1162_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74932041/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14061/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11379/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (569/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (703/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1162_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1162_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74932041/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14097/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (709/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (569/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (703/5000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1162_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1162_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1162_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74932041/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14097/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (709/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (569/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (703/5000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1162_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

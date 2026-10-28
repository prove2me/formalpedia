-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1051_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:55:12.65596+00:00
-- url     : https://prove2.me/submissions/38a6ef3b-54fe-4b8f-bfac-b0c9a4162f69

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
theorem support_rectangle_w1051_s3_0 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-441245317/2000000000 : ℝ)*x 0 + (2719659297/5000000000 : ℝ)*x 1 + (5222708371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (441245317/2000000000 : ℝ)^2061 ≤ (13387607134917/100000000000000 : ℝ)^1549 := by
    have hnat : (441245317 : ℕ)^2061*100000000000000^1549 ≤ 13387607134917^1549*2000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441245317 2000000000 13387607134917 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2719659297/5000000000 : ℝ)^2061 ≤ (2223834597803/5000000000000 : ℝ)^1549 := by
    have hnat : (2719659297 : ℕ)^2061*5000000000000^1549 ≤ 2223834597803^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719659297 5000000000 2223834597803 5000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5222708371/10000000000 : ℝ)^2061 ≤ (8427140178031/20000000000000 : ℝ)^1549 := by
    have hnat : (5222708371 : ℕ)^2061*20000000000000^1549 ≤ 8427140178031^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5222708371 10000000000 8427140178031 20000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-441245317/2000000000 : ℝ), (2719659297/5000000000 : ℝ), (5222708371/10000000000 : ℝ)] ![(13387607134917/100000000000000 : ℝ), (2223834597803/5000000000000 : ℝ), (8427140178031/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-441245317/2000000000 : ℝ)|^2061 ≤ (13387607134917/100000000000000 : ℝ)^1549
        have hw : |(-441245317/2000000000 : ℝ)|=(441245317/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2719659297/5000000000 : ℝ)|^2061 ≤ (2223834597803/5000000000000 : ℝ)^1549
        have hw : |(2719659297/5000000000 : ℝ)|=(2719659297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5222708371/10000000000 : ℝ)|^2061 ≤ (8427140178031/20000000000000 : ℝ)^1549
        have hw : |(5222708371/10000000000 : ℝ)|=(5222708371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s3_1 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (669510417/1250000000 : ℝ)*x 0 + (-579297697/2500000000 : ℝ)*x 1 + (130567711/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669510417/1250000000 : ℝ)^2061 ≤ (43573420321511/100000000000000 : ℝ)^1549 := by
    have hnat : (669510417 : ℕ)^2061*100000000000000^1549 ≤ 43573420321511^1549*1250000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669510417 1250000000 43573420321511 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (579297697/2500000000 : ℝ)^2061 ≤ (14290878037011/100000000000000 : ℝ)^1549 := by
    have hnat : (579297697 : ℕ)^2061*100000000000000^1549 ≤ 14290878037011^1549*2500000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      579297697 2500000000 14290878037011 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130567711/250000000 : ℝ)^2061 ≤ (21067850815417/50000000000000 : ℝ)^1549 := by
    have hnat : (130567711 : ℕ)^2061*50000000000000^1549 ≤ 21067850815417^1549*250000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130567711 250000000 21067850815417 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669510417/1250000000 : ℝ), (-579297697/2500000000 : ℝ), (130567711/250000000 : ℝ)] ![(43573420321511/100000000000000 : ℝ), (14290878037011/100000000000000 : ℝ), (21067850815417/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669510417/1250000000 : ℝ)|^2061 ≤ (43573420321511/100000000000000 : ℝ)^1549
        have hw : |(669510417/1250000000 : ℝ)|=(669510417/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-579297697/2500000000 : ℝ)|^2061 ≤ (14290878037011/100000000000000 : ℝ)^1549
        have hw : |(-579297697/2500000000 : ℝ)|=(579297697/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(130567711/250000000 : ℝ)|^2061 ≤ (21067850815417/50000000000000 : ℝ)^1549
        have hw : |(130567711/250000000 : ℝ)|=(130567711/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s3_2 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5356083329/10000000000 : ℝ)*x 0 + (2611354269/5000000000 : ℝ)*x 1 + (-2317190669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356083329/10000000000 : ℝ)^2061 ≤ (43573420245741/100000000000000 : ℝ)^1549 := by
    have hnat : (5356083329 : ℕ)^2061*100000000000000^1549 ≤ 43573420245741^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356083329 10000000000 43573420245741 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2611354269/5000000000 : ℝ)^2061 ≤ (42135702682813/100000000000000 : ℝ)^1549 := by
    have hnat : (2611354269 : ℕ)^2061*100000000000000^1549 ≤ 42135702682813^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2611354269 5000000000 42135702682813 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2317190669/10000000000 : ℝ)^2061 ≤ (7145438530257/50000000000000 : ℝ)^1549 := by
    have hnat : (2317190669 : ℕ)^2061*50000000000000^1549 ≤ 7145438530257^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2317190669 10000000000 7145438530257 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356083329/10000000000 : ℝ), (2611354269/5000000000 : ℝ), (-2317190669/10000000000 : ℝ)] ![(43573420245741/100000000000000 : ℝ), (42135702682813/100000000000000 : ℝ), (7145438530257/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356083329/10000000000 : ℝ)|^2061 ≤ (43573420245741/100000000000000 : ℝ)^1549
        have hw : |(5356083329/10000000000 : ℝ)|=(5356083329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2611354269/5000000000 : ℝ)|^2061 ≤ (42135702682813/100000000000000 : ℝ)^1549
        have hw : |(2611354269/5000000000 : ℝ)|=(2611354269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2317190669/10000000000 : ℝ)|^2061 ≤ (7145438530257/50000000000000 : ℝ)^1549
        have hw : |(-2317190669/10000000000 : ℝ)|=(2317190669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s3_3 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1093682219/2500000000 : ℝ)*x 0 + (4168293977/10000000000 : ℝ)*x 1 + (2295777801/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093682219/2500000000 : ℝ)^2061 ≤ (8321711195767/25000000000000 : ℝ)^1549 := by
    have hnat : (1093682219 : ℕ)^2061*25000000000000^1549 ≤ 8321711195767^1549*2500000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093682219 2500000000 8321711195767 25000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4168293977/10000000000 : ℝ)^2061 ≤ (1560669561079/5000000000000 : ℝ)^1549 := by
    have hnat : (4168293977 : ℕ)^2061*5000000000000^1549 ≤ 1560669561079^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4168293977 10000000000 1560669561079 5000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2295777801/5000000000 : ℝ)^2061 ≤ (17749881991669/50000000000000 : ℝ)^1549 := by
    have hnat : (2295777801 : ℕ)^2061*50000000000000^1549 ≤ 17749881991669^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2295777801 5000000000 17749881991669 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1093682219/2500000000 : ℝ), (4168293977/10000000000 : ℝ), (2295777801/5000000000 : ℝ)] ![(8321711195767/25000000000000 : ℝ), (1560669561079/5000000000000 : ℝ), (17749881991669/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1093682219/2500000000 : ℝ)|^2061 ≤ (8321711195767/25000000000000 : ℝ)^1549
        have hw : |(1093682219/2500000000 : ℝ)|=(1093682219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4168293977/10000000000 : ℝ)|^2061 ≤ (1560669561079/5000000000000 : ℝ)^1549
        have hw : |(4168293977/10000000000 : ℝ)|=(4168293977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2295777801/5000000000 : ℝ)|^2061 ≤ (17749881991669/50000000000000 : ℝ)^1549
        have hw : |(2295777801/5000000000 : ℝ)|=(2295777801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s3_4 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2206249997/10000000000 : ℝ)*x 0 + (1305901453/2500000000 : ℝ)*x 1 + (5438415703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2206249997/10000000000 : ℝ)^2061 ≤ (6693898079839/50000000000000 : ℝ)^1549 := by
    have hnat : (2206249997 : ℕ)^2061*50000000000000^1549 ≤ 6693898079839^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2206249997 10000000000 6693898079839 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1305901453/2500000000 : ℝ)^2061 ≤ (8429066945279/20000000000000 : ℝ)^1549 := by
    have hnat : (1305901453 : ℕ)^2061*20000000000000^1549 ≤ 8429066945279^1549*2500000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305901453 2500000000 8429066945279 20000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5438415703/10000000000 : ℝ)^2061 ≤ (8893373819167/20000000000000 : ℝ)^1549 := by
    have hnat : (5438415703 : ℕ)^2061*20000000000000^1549 ≤ 8893373819167^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438415703 10000000000 8893373819167 20000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2206249997/10000000000 : ℝ), (1305901453/2500000000 : ℝ), (5438415703/10000000000 : ℝ)] ![(6693898079839/50000000000000 : ℝ), (8429066945279/20000000000000 : ℝ), (8893373819167/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2206249997/10000000000 : ℝ)|^2061 ≤ (6693898079839/50000000000000 : ℝ)^1549
        have hw : |(-2206249997/10000000000 : ℝ)|=(2206249997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1305901453/2500000000 : ℝ)|^2061 ≤ (8429066945279/20000000000000 : ℝ)^1549
        have hw : |(1305901453/2500000000 : ℝ)|=(1305901453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5438415703/10000000000 : ℝ)|^2061 ≤ (8893373819167/20000000000000 : ℝ)^1549
        have hw : |(5438415703/10000000000 : ℝ)|=(5438415703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s3_5 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5301583949/10000000000 : ℝ)*x 0 + (-2101484191/10000000000 : ℝ)*x 1 + (1359603769/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301583949/10000000000 : ℝ)^2061 ≤ (21492247716991/50000000000000 : ℝ)^1549 := by
    have hnat : (5301583949 : ℕ)^2061*50000000000000^1549 ≤ 21492247716991^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301583949 10000000000 21492247716991 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2101484191/10000000000 : ℝ)^2061 ≤ (12548642266313/100000000000000 : ℝ)^1549 := by
    have hnat : (2101484191 : ℕ)^2061*100000000000000^1549 ≤ 12548642266313^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101484191 10000000000 12548642266313 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1359603769/2500000000 : ℝ)^2061 ≤ (1778674490987/4000000000000 : ℝ)^1549 := by
    have hnat : (1359603769 : ℕ)^2061*4000000000000^1549 ≤ 1778674490987^1549*2500000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359603769 2500000000 1778674490987 4000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301583949/10000000000 : ℝ), (-2101484191/10000000000 : ℝ), (1359603769/2500000000 : ℝ)] ![(21492247716991/50000000000000 : ℝ), (12548642266313/100000000000000 : ℝ), (1778674490987/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301583949/10000000000 : ℝ)|^2061 ≤ (21492247716991/50000000000000 : ℝ)^1549
        have hw : |(5301583949/10000000000 : ℝ)|=(5301583949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2101484191/10000000000 : ℝ)|^2061 ≤ (12548642266313/100000000000000 : ℝ)^1549
        have hw : |(-2101484191/10000000000 : ℝ)|=(2101484191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1359603769/2500000000 : ℝ)|^2061 ≤ (1778674490987/4000000000000 : ℝ)^1549
        have hw : |(1359603769/2500000000 : ℝ)|=(1359603769/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s3_6 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5301583623/10000000000 : ℝ)*x 0 + (5438415551/10000000000 : ℝ)*x 1 + (-131342749/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301583623/10000000000 : ℝ)^2061 ≤ (1074612297929/2500000000000 : ℝ)^1549 := by
    have hnat : (5301583623 : ℕ)^2061*2500000000000^1549 ≤ 1074612297929^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301583623 10000000000 1074612297929 2500000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438415551/10000000000 : ℝ)^2061 ≤ (44466867442221/100000000000000 : ℝ)^1549 := by
    have hnat : (5438415551 : ℕ)^2061*100000000000000^1549 ≤ 44466867442221^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438415551 10000000000 44466867442221 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131342749/625000000 : ℝ)^2061 ≤ (6274320310843/50000000000000 : ℝ)^1549 := by
    have hnat : (131342749 : ℕ)^2061*50000000000000^1549 ≤ 6274320310843^1549*625000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131342749 625000000 6274320310843 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301583623/10000000000 : ℝ), (5438415551/10000000000 : ℝ), (-131342749/625000000 : ℝ)] ![(1074612297929/2500000000000 : ℝ), (44466867442221/100000000000000 : ℝ), (6274320310843/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301583623/10000000000 : ℝ)|^2061 ≤ (1074612297929/2500000000000 : ℝ)^1549
        have hw : |(5301583623/10000000000 : ℝ)|=(5301583623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438415551/10000000000 : ℝ)|^2061 ≤ (44466867442221/100000000000000 : ℝ)^1549
        have hw : |(5438415551/10000000000 : ℝ)|=(5438415551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-131342749/625000000 : ℝ)|^2061 ≤ (6274320310843/50000000000000 : ℝ)^1549
        have hw : |(-131342749/625000000 : ℝ)|=(131342749/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s3_7 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1093693559/2500000000 : ℝ)*x 0 + (917960261/2000000000 : ℝ)*x 1 + (417005893/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093693559/2500000000 : ℝ)^2061 ≤ (16643652002093/50000000000000 : ℝ)^1549 := by
    have hnat : (1093693559 : ℕ)^2061*50000000000000^1549 ≤ 16643652002093^1549*2500000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093693559 2500000000 16643652002093 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (917960261/2000000000 : ℝ)^2061 ≤ (8870429631571/25000000000000 : ℝ)^1549 := by
    have hnat : (917960261 : ℕ)^2061*25000000000000^1549 ≤ 8870429631571^1549*2000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      917960261 2000000000 8870429631571 25000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (417005893/1000000000 : ℝ)^2061 ≤ (6246195490091/20000000000000 : ℝ)^1549 := by
    have hnat : (417005893 : ℕ)^2061*20000000000000^1549 ≤ 6246195490091^1549*1000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417005893 1000000000 6246195490091 20000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1093693559/2500000000 : ℝ), (917960261/2000000000 : ℝ), (417005893/1000000000 : ℝ)] ![(16643652002093/50000000000000 : ℝ), (8870429631571/25000000000000 : ℝ), (6246195490091/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1093693559/2500000000 : ℝ)|^2061 ≤ (16643652002093/50000000000000 : ℝ)^1549
        have hw : |(1093693559/2500000000 : ℝ)|=(1093693559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(917960261/2000000000 : ℝ)|^2061 ≤ (8870429631571/25000000000000 : ℝ)^1549
        have hw : |(917960261/2000000000 : ℝ)|=(917960261/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(417005893/1000000000 : ℝ)|^2061 ≤ (6246195490091/20000000000000 : ℝ)^1549
        have hw : |(417005893/1000000000 : ℝ)|=(417005893/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1051_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147701323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16791/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8637/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2069/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (933/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16791/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8637/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16791/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8637/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16791/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8637/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16791/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8637/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16791/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8637/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16791/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8637/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8637/100000 : ℝ) ^ (8243/2048 : ℝ) ≤ (2617788928060139/50000000000000000000 : ℝ) := by
    have hpowers : (8637/100000 : ℝ)^8243 ≤ (2617788928060139/50000000000000000000 : ℝ)^2048 := by
      have hnat : (8637 : ℕ)^8243*50000000000000000000^2048 ≤ 2617788928060139^2048*100000^8243 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8637 100000 2617788928060139 50000000000000000000 8243 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8637/100000 : ℝ)) (X := (2617788928060139/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (16791/100000 : ℝ) ^ (8243/2048 : ℝ) ≤ (76034174758489279/100000000000000000000 : ℝ) := by
    have hpowers : (16791/100000 : ℝ)^8243 ≤ (76034174758489279/100000000000000000000 : ℝ)^2048 := by
      have hnat : (16791 : ℕ)^8243*100000000000000000000^2048 ≤ 76034174758489279^2048*100000^8243 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16791 100000 76034174758489279 100000000000000000000 8243 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16791/100000 : ℝ)) (X := (76034174758489279/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002617788928060139/25000000000000000000 : ℝ) ≤ (2500065037253243/2500000000000000 : ℝ) ^ (8243/2048 : ℝ) := by
    have hpowers : (25002617788928060139/25000000000000000000 : ℝ)^2048 ≤ (2500065037253243/2500000000000000 : ℝ)^8243 := by
      have hnat : (25002617788928060139 : ℕ)^2048*2500000000000000^8243 ≤ 2500065037253243^8243*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002617788928060139 25000000000000000000 2500065037253243 2500000000000000 2048 8243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500065037253243/2500000000000000 : ℝ)) (X := (25002617788928060139/25000000000000000000 : ℝ)) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100081269752614609557/100000000000000000000 : ℝ) ≤ (2000403711387099/2000000000000000 : ℝ) ^ (8243/2048 : ℝ) := by
    have hpowers : (100081269752614609557/100000000000000000000 : ℝ)^2048 ≤ (2000403711387099/2000000000000000 : ℝ)^8243 := by
      have hnat : (100081269752614609557 : ℕ)^2048*2000000000000000^8243 ≤ 2000403711387099^8243*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100081269752614609557 100000000000000000000 2000403711387099 2000000000000000 2048 8243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000403711387099/2000000000000000 : ℝ)) (X := (100081269752614609557/100000000000000000000 : ℝ)) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50076034174758489279/50000000000000000000 : ℝ) ≤ (5001888482429009/5000000000000000 : ℝ) ^ (8243/2048 : ℝ) := by
    have hpowers : (50076034174758489279/50000000000000000000 : ℝ)^2048 ≤ (5001888482429009/5000000000000000 : ℝ)^8243 := by
      have hnat : (50076034174758489279 : ℕ)^2048*5000000000000000^8243 ≤ 5001888482429009^8243*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50076034174758489279 50000000000000000000 5001888482429009 5000000000000000 2048 8243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001888482429009/5000000000000000 : ℝ)) (X := (50076034174758489279/50000000000000000000 : ℝ)) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2617788928060139/50000000000000000000 : ℝ) ≤ ((13585291086099685231/13590000000000000000 : ℝ)+2*(1758407922523/815400000000000 : ℝ)*(8637/100000 : ℝ))^(8243/2048 : ℝ) := by
    rw [show (13585291086099685231/13590000000000000000 : ℝ)+2*(1758407922523/815400000000000 : ℝ)*(8637/100000 : ℝ)=(2500065037253243/2500000000000000 : ℝ) by norm_num, show 1+2*(2617788928060139/50000000000000000000 : ℝ)=(25002617788928060139/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(76034174758489279/100000000000000000000 : ℝ)+(2617788928060139/50000000000000000000 : ℝ) ≤ ((13585291086099685231/13590000000000000000 : ℝ)+(1758407922523/815400000000000 : ℝ)*((16791/100000 : ℝ)+(8637/100000 : ℝ)))^(8243/2048 : ℝ) := by
    rw [show (13585291086099685231/13590000000000000000 : ℝ)+(1758407922523/815400000000000 : ℝ)*((16791/100000 : ℝ)+(8637/100000 : ℝ))=(2000403711387099/2000000000000000 : ℝ) by norm_num, show 1+(76034174758489279/100000000000000000000 : ℝ)+(2617788928060139/50000000000000000000 : ℝ)=(100081269752614609557/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(76034174758489279/100000000000000000000 : ℝ) ≤ ((13585291086099685231/13590000000000000000 : ℝ)+2*(1758407922523/815400000000000 : ℝ)*(16791/100000 : ℝ))^(8243/2048 : ℝ) := by
    rw [show (13585291086099685231/13590000000000000000 : ℝ)+2*(1758407922523/815400000000000 : ℝ)*(16791/100000 : ℝ)=(5001888482429009/5000000000000000 : ℝ) by norm_num, show 1+2*(76034174758489279/100000000000000000000 : ℝ)=(50076034174758489279/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13585291086099685231/13590000000000000000 : ℝ)*(X 1 0+X 2 0)+(1758407922523/815400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8243/2048 : ℝ)) (lo := (8637/100000 : ℝ)) (hi := (16791/100000 : ℝ)) (c := (13585291086099685231/13590000000000000000 : ℝ)) (alpha := (1758407922523/815400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13585291086099685231/13590000000000000000 : ℝ)*(X 0 1+X 2 1)+(1758407922523/815400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8243/2048 : ℝ)) (lo := (8637/100000 : ℝ)) (hi := (16791/100000 : ℝ)) (c := (13585291086099685231/13590000000000000000 : ℝ)) (alpha := (1758407922523/815400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13585291086099685231/13590000000000000000 : ℝ)*(X 0 2+X 1 2)+(1758407922523/815400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8243/2048 : ℝ)) (lo := (8637/100000 : ℝ)) (hi := (16791/100000 : ℝ)) (c := (13585291086099685231/13590000000000000000 : ℝ)) (alpha := (1758407922523/815400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-441245317/2000000000 : ℝ)*X 0 0+(2719659297/5000000000 : ℝ)*X 0 1+(5222708371/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((669510417/1250000000 : ℝ)*X 1 0+(-579297697/2500000000 : ℝ)*X 1 1+(130567711/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5356083329/10000000000 : ℝ)*X 2 0+(2611354269/5000000000 : ℝ)*X 2 1+(-2317190669/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1093682219/2500000000 : ℝ)*X 0 0+(4168293977/10000000000 : ℝ)*X 0 1+(2295777801/5000000000 : ℝ)*X 0 2+(1093682219/2500000000 : ℝ)*X 1 0+(4168293977/10000000000 : ℝ)*X 1 1+(2295777801/5000000000 : ℝ)*X 1 2+(1093682219/2500000000 : ℝ)*X 2 0+(4168293977/10000000000 : ℝ)*X 2 1+(2295777801/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2206249997/10000000000 : ℝ)*X 0 0+(1305901453/2500000000 : ℝ)*X 0 1+(5438415703/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5301583949/10000000000 : ℝ)*X 1 0+(-2101484191/10000000000 : ℝ)*X 1 1+(1359603769/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5301583623/10000000000 : ℝ)*X 2 0+(5438415551/10000000000 : ℝ)*X 2 1+(-131342749/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1093693559/2500000000 : ℝ)*X 0 0+(917960261/2000000000 : ℝ)*X 0 1+(417005893/1000000000 : ℝ)*X 0 2+(1093693559/2500000000 : ℝ)*X 1 0+(917960261/2000000000 : ℝ)*X 1 1+(417005893/1000000000 : ℝ)*X 1 2+(1093693559/2500000000 : ℝ)*X 2 0+(917960261/2000000000 : ℝ)*X 2 1+(417005893/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4130826645719141284279/453000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2102964513/100000000000000 : ℝ)*(base19) + (930631451/50000000000000 : ℝ)*(base23) + (25245147/20000000000000 : ℝ)*(lower2) + (233005717/100000000000000 : ℝ)*(upper3) + (80214027/50000000000000 : ℝ)*(upper5) + (87241278661201/2500000000000 : ℝ)*(major0) + (87241278661201/2500000000000 : ℝ)*(major1) + (87241278661201/2500000000000 : ℝ)*(major2) + (2308312163706571/50000000000000 : ℝ)*(sp0) + (2308329736920613/50000000000000 : ℝ)*(sp1) + (1154164928885709/25000000000000 : ℝ)*(sp2) + (1181310873238951/50000000000000 : ℝ)*(sp3) + (9312348149/25000000000000 : ℝ)*(sp4) + (18665651677/100000000000000 : ℝ)*(sp7) + (1181320206064789/50000000000000 : ℝ)*(f.failure) + (2308330788402869/50000000000000 : ℝ)*(f.sum) + (16079016374971/2038500000000000000000000000 : ℝ)*base66 + (292612434483342293/101925000000000000000000000000000 : ℝ)*base67 + (42253412438282707/101925000000000000000000000000000 : ℝ)*base70 + (81710880997082707/101925000000000000000000000000000 : ℝ)*base72 + (4188375109927/815400000000000000000000000 : ℝ)*base74 + (801900515920532707/101925000000000000000000000000000 : ℝ)*base76 + (163258608820017293/101925000000000000000000000000000 : ℝ)*base77 + (726201031007442293/101925000000000000000000000000000 : ℝ)*base79 + (12536400359959/2038500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (40984153/5000000000000000000000 : ℝ)*base90 + (40984153/5000000000000000000000 : ℝ)*base92 + (40984153/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (311911340541463291977124793/56625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (546454969/50000000000000 : ℝ)*(base19) + (200257807/25000000000000 : ℝ)*(base23) + (7821637/100000000000000 : ℝ)*(lower4) + (62444433/25000000000000 : ℝ)*(upper5) + (879712638941103/25000000000000 : ℝ)*(major0) + (879712638941103/25000000000000 : ℝ)*(major1) + (879712638941103/25000000000000 : ℝ)*(major2) + (1650319181/50000000000000 : ℝ)*(sp0) + (6440473527/50000000000000 : ℝ)*(sp1) + (10899004937/100000000000000 : ℝ)*(sp2) + (4655287988493563/100000000000000 : ℝ)*(sp4) + (2327638657637467/50000000000000 : ℝ)*(sp5) + (4655279589095761/100000000000000 : ℝ)*(sp6) + (19059277110277/800000000000 : ℝ)*(sp7) + (19059277110277/800000000000 : ℝ)*(f.failure) + (2327645644565963/50000000000000 : ℝ)*(f.sum) + (10254035518141/6795000000000000000000000000 : ℝ)*base65 + (2655269067528650207/339750000000000000000000000000000 : ℝ)*base68 + (1641966214724349793/339750000000000000000000000000000 : ℝ)*base69 + (786787170568400207/339750000000000000000000000000000 : ℝ)*base72 + (36566438098559/6795000000000000000000000000 : ℝ)*base74 + (1276839385867599793/339750000000000000000000000000000 : ℝ)*base75 + (1196726417291900207/339750000000000000000000000000000 : ℝ)*base78 + (1811649511690400207/339750000000000000000000000000000 : ℝ)*base80 + (9848483788289/6795000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (196471/80000000000000000000 : ℝ)*base89 + (196471/80000000000000000000 : ℝ)*base91 + (196471/80000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1051_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147701323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16791/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8637/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2069/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (933/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1051_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1051_s4_0 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-552513933/2500000000 : ℝ)*x 0 + (5406662979/10000000000 : ℝ)*x 1 + (1313215771/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (552513933/2500000000 : ℝ)^2061 ≤ (13418531868447/100000000000000 : ℝ)^1549 := by
    have hnat : (552513933 : ℕ)^2061*100000000000000^1549 ≤ 13418531868447^1549*2500000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552513933 2500000000 13418531868447 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406662979/10000000000 : ℝ)^2061 ≤ (44121763582199/100000000000000 : ℝ)^1549 := by
    have hnat : (5406662979 : ℕ)^2061*100000000000000^1549 ≤ 44121763582199^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406662979 10000000000 44121763582199 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313215771/2500000000 : ℝ)^2061 ≤ (42459704539601/100000000000000 : ℝ)^1549 := by
    have hnat : (1313215771 : ℕ)^2061*100000000000000^1549 ≤ 42459704539601^1549*2500000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313215771 2500000000 42459704539601 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-552513933/2500000000 : ℝ), (5406662979/10000000000 : ℝ), (1313215771/2500000000 : ℝ)] ![(13418531868447/100000000000000 : ℝ), (44121763582199/100000000000000 : ℝ), (42459704539601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-552513933/2500000000 : ℝ)|^2061 ≤ (13418531868447/100000000000000 : ℝ)^1549
        have hw : |(-552513933/2500000000 : ℝ)|=(552513933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406662979/10000000000 : ℝ)|^2061 ≤ (44121763582199/100000000000000 : ℝ)^1549
        have hw : |(5406662979/10000000000 : ℝ)|=(5406662979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313215771/2500000000 : ℝ)|^2061 ≤ (42459704539601/100000000000000 : ℝ)^1549
        have hw : |(1313215771/2500000000 : ℝ)|=(1313215771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s4_1 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674003653/5000000000 : ℝ)*x 0 + (-2288297163/10000000000 : ℝ)*x 1 + (5252863059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674003653/5000000000 : ℝ)^2061 ≤ (8697204904811/20000000000000 : ℝ)^1549 := by
    have hnat : (2674003653 : ℕ)^2061*20000000000000^1549 ≤ 8697204904811^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674003653 5000000000 8697204904811 20000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2288297163/10000000000 : ℝ)^2061 ≤ (43919597459/312500000000 : ℝ)^1549 := by
    have hnat : (2288297163 : ℕ)^2061*312500000000^1549 ≤ 43919597459^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2288297163 10000000000 43919597459 312500000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5252863059/10000000000 : ℝ)^2061 ≤ (42459704270727/100000000000000 : ℝ)^1549 := by
    have hnat : (5252863059 : ℕ)^2061*100000000000000^1549 ≤ 42459704270727^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252863059 10000000000 42459704270727 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674003653/5000000000 : ℝ), (-2288297163/10000000000 : ℝ), (5252863059/10000000000 : ℝ)] ![(8697204904811/20000000000000 : ℝ), (43919597459/312500000000 : ℝ), (42459704270727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674003653/5000000000 : ℝ)|^2061 ≤ (8697204904811/20000000000000 : ℝ)^1549
        have hw : |(2674003653/5000000000 : ℝ)|=(2674003653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2288297163/10000000000 : ℝ)|^2061 ≤ (43919597459/312500000000 : ℝ)^1549
        have hw : |(-2288297163/10000000000 : ℝ)|=(2288297163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5252863059/10000000000 : ℝ)|^2061 ≤ (42459704270727/100000000000000 : ℝ)^1549
        have hw : |(5252863059/10000000000 : ℝ)|=(5252863059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s4_2 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (534800731/1000000000 : ℝ)*x 0 + (5252863053/10000000000 : ℝ)*x 1 + (-1144148583/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534800731/1000000000 : ℝ)^2061 ≤ (43486024567331/100000000000000 : ℝ)^1549 := by
    have hnat : (534800731 : ℕ)^2061*100000000000000^1549 ≤ 43486024567331^1549*1000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534800731 1000000000 43486024567331 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5252863053/10000000000 : ℝ)^2061 ≤ (21229852103099/50000000000000 : ℝ)^1549 := by
    have hnat : (5252863053 : ℕ)^2061*50000000000000^1549 ≤ 21229852103099^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252863053 10000000000 21229852103099 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1144148583/5000000000 : ℝ)^2061 ≤ (3513567802849/25000000000000 : ℝ)^1549 := by
    have hnat : (1144148583 : ℕ)^2061*25000000000000^1549 ≤ 3513567802849^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1144148583 5000000000 3513567802849 25000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534800731/1000000000 : ℝ), (5252863053/10000000000 : ℝ), (-1144148583/5000000000 : ℝ)] ![(43486024567331/100000000000000 : ℝ), (21229852103099/50000000000000 : ℝ), (3513567802849/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534800731/1000000000 : ℝ)|^2061 ≤ (43486024567331/100000000000000 : ℝ)^1549
        have hw : |(534800731/1000000000 : ℝ)|=(534800731/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5252863053/10000000000 : ℝ)|^2061 ≤ (21229852103099/50000000000000 : ℝ)^1549
        have hw : |(5252863053/10000000000 : ℝ)|=(5252863053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1144148583/5000000000 : ℝ)|^2061 ≤ (3513567802849/25000000000000 : ℝ)^1549
        have hw : |(-1144148583/5000000000 : ℝ)|=(1144148583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s4_3 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (875400877/2000000000 : ℝ)*x 0 + (2114680529/5000000000 : ℝ)*x 1 + (4529890137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (875400877/2000000000 : ℝ)^2061 ≤ (33309883800183/100000000000000 : ℝ)^1549 := by
    have hnat : (875400877 : ℕ)^2061*100000000000000^1549 ≤ 33309883800183^1549*2000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875400877 2000000000 33309883800183 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2114680529/5000000000 : ℝ)^2061 ≤ (7955824408903/25000000000000 : ℝ)^1549 := by
    have hnat : (2114680529 : ℕ)^2061*25000000000000^1549 ≤ 7955824408903^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114680529 5000000000 7955824408903 25000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4529890137/10000000000 : ℝ)^2061 ≤ (34866818553567/100000000000000 : ℝ)^1549 := by
    have hnat : (4529890137 : ℕ)^2061*100000000000000^1549 ≤ 34866818553567^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4529890137 10000000000 34866818553567 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(875400877/2000000000 : ℝ), (2114680529/5000000000 : ℝ), (4529890137/10000000000 : ℝ)] ![(33309883800183/100000000000000 : ℝ), (7955824408903/25000000000000 : ℝ), (34866818553567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(875400877/2000000000 : ℝ)|^2061 ≤ (33309883800183/100000000000000 : ℝ)^1549
        have hw : |(875400877/2000000000 : ℝ)|=(875400877/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2114680529/5000000000 : ℝ)|^2061 ≤ (7955824408903/25000000000000 : ℝ)^1549
        have hw : |(2114680529/5000000000 : ℝ)|=(2114680529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4529890137/10000000000 : ℝ)|^2061 ≤ (34866818553567/100000000000000 : ℝ)^1549
        have hw : |(4529890137/10000000000 : ℝ)|=(4529890137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s4_4 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2210064131/10000000000 : ℝ)*x 0 + (656664581/1250000000 : ℝ)*x 1 + (270310373/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2210064131/10000000000 : ℝ)^2061 ≤ (13418599719439/100000000000000 : ℝ)^1549 := by
    have hnat : (2210064131 : ℕ)^2061*100000000000000^1549 ≤ 13418599719439^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210064131 10000000000 13418599719439 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (656664581/1250000000 : ℝ)^2061 ≤ (849291653137/2000000000000 : ℝ)^1549 := by
    have hnat : (656664581 : ℕ)^2061*2000000000000^1549 ≤ 849291653137^1549*1250000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656664581 1250000000 849291653137 2000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270310373/500000000 : ℝ)^2061 ≤ (2205840881117/5000000000000 : ℝ)^1549 := by
    have hnat : (270310373 : ℕ)^2061*5000000000000^1549 ≤ 2205840881117^1549*500000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270310373 500000000 2205840881117 5000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2210064131/10000000000 : ℝ), (656664581/1250000000 : ℝ), (270310373/500000000 : ℝ)] ![(13418599719439/100000000000000 : ℝ), (849291653137/2000000000000 : ℝ), (2205840881117/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2210064131/10000000000 : ℝ)|^2061 ≤ (13418599719439/100000000000000 : ℝ)^1549
        have hw : |(-2210064131/10000000000 : ℝ)|=(2210064131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(656664581/1250000000 : ℝ)|^2061 ≤ (849291653137/2000000000000 : ℝ)^1549
        have hw : |(656664581/1250000000 : ℝ)|=(656664581/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270310373/500000000 : ℝ)|^2061 ≤ (2205840881117/5000000000000 : ℝ)^1549
        have hw : |(270310373/500000000 : ℝ)|=(270310373/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s4_5 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2654658231/5000000000 : ℝ)*x 0 + (-2134952767/10000000000 : ℝ)*x 1 + (5406207507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2654658231/5000000000 : ℝ)^2061 ≤ (21533966157623/50000000000000 : ℝ)^1549 := by
    have hnat : (2654658231 : ℕ)^2061*50000000000000^1549 ≤ 21533966157623^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2654658231 5000000000 21533966157623 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2134952767/10000000000 : ℝ)^2061 ≤ (6407624769593/50000000000000 : ℝ)^1549 := by
    have hnat : (2134952767 : ℕ)^2061*50000000000000^1549 ≤ 6407624769593^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134952767 10000000000 6407624769593 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406207507/10000000000 : ℝ)^2061 ≤ (11029204533163/25000000000000 : ℝ)^1549 := by
    have hnat : (5406207507 : ℕ)^2061*25000000000000^1549 ≤ 11029204533163^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406207507 10000000000 11029204533163 25000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2654658231/5000000000 : ℝ), (-2134952767/10000000000 : ℝ), (5406207507/10000000000 : ℝ)] ![(21533966157623/50000000000000 : ℝ), (6407624769593/50000000000000 : ℝ), (11029204533163/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2654658231/5000000000 : ℝ)|^2061 ≤ (21533966157623/50000000000000 : ℝ)^1549
        have hw : |(2654658231/5000000000 : ℝ)|=(2654658231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2134952767/10000000000 : ℝ)|^2061 ≤ (6407624769593/50000000000000 : ℝ)^1549
        have hw : |(-2134952767/10000000000 : ℝ)|=(2134952767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406207507/10000000000 : ℝ)|^2061 ≤ (11029204533163/25000000000000 : ℝ)^1549
        have hw : |(5406207507/10000000000 : ℝ)|=(5406207507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s4_6 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5309316473/10000000000 : ℝ)*x 0 + (2703103747/5000000000 : ℝ)*x 1 + (-2134952769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309316473/10000000000 : ℝ)^2061 ≤ (43067932433969/100000000000000 : ℝ)^1549 := by
    have hnat : (5309316473 : ℕ)^2061*100000000000000^1549 ≤ 43067932433969^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309316473 10000000000 43067932433969 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703103747/5000000000 : ℝ)^2061 ≤ (22058408995751/50000000000000 : ℝ)^1549 := by
    have hnat : (2703103747 : ℕ)^2061*50000000000000^1549 ≤ 22058408995751^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703103747 5000000000 22058408995751 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2134952769/10000000000 : ℝ)^2061 ≤ (12815249555159/100000000000000 : ℝ)^1549 := by
    have hnat : (2134952769 : ℕ)^2061*100000000000000^1549 ≤ 12815249555159^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134952769 10000000000 12815249555159 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309316473/10000000000 : ℝ), (2703103747/5000000000 : ℝ), (-2134952769/10000000000 : ℝ)] ![(43067932433969/100000000000000 : ℝ), (22058408995751/50000000000000 : ℝ), (12815249555159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309316473/10000000000 : ℝ)|^2061 ≤ (43067932433969/100000000000000 : ℝ)^1549
        have hw : |(5309316473/10000000000 : ℝ)|=(5309316473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703103747/5000000000 : ℝ)|^2061 ≤ (22058408995751/50000000000000 : ℝ)^1549
        have hw : |(2703103747/5000000000 : ℝ)|=(2703103747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2134952769/10000000000 : ℝ)|^2061 ≤ (12815249555159/100000000000000 : ℝ)^1549
        have hw : |(-2134952769/10000000000 : ℝ)|=(2134952769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s4_7 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4377020569/10000000000 : ℝ)*x 0 + (4529003993/10000000000 : ℝ)*x 1 + (4230251109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4377020569/10000000000 : ℝ)^2061 ≤ (33310047673727/100000000000000 : ℝ)^1549 := by
    have hnat : (4377020569 : ℕ)^2061*100000000000000^1549 ≤ 33310047673727^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4377020569 10000000000 33310047673727 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4529003993/10000000000 : ℝ)^2061 ≤ (34857743661129/100000000000000 : ℝ)^1549 := by
    have hnat : (4529003993 : ℕ)^2061*100000000000000^1549 ≤ 34857743661129^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4529003993 10000000000 34857743661129 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4230251109/10000000000 : ℝ)^2061 ≤ (6366441729359/20000000000000 : ℝ)^1549 := by
    have hnat : (4230251109 : ℕ)^2061*20000000000000^1549 ≤ 6366441729359^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230251109 10000000000 6366441729359 20000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4377020569/10000000000 : ℝ), (4529003993/10000000000 : ℝ), (4230251109/10000000000 : ℝ)] ![(33310047673727/100000000000000 : ℝ), (34857743661129/100000000000000 : ℝ), (6366441729359/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4377020569/10000000000 : ℝ)|^2061 ≤ (33310047673727/100000000000000 : ℝ)^1549
        have hw : |(4377020569/10000000000 : ℝ)|=(4377020569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4529003993/10000000000 : ℝ)|^2061 ≤ (34857743661129/100000000000000 : ℝ)^1549
        have hw : |(4529003993/10000000000 : ℝ)|=(4529003993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4230251109/10000000000 : ℝ)|^2061 ≤ (6366441729359/20000000000000 : ℝ)^1549
        have hw : |(4230251109/10000000000 : ℝ)|=(4230251109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1051_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147701323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (933/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2069/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (10989/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7123/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (933/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2069/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (933/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2069/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (933/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2069/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (933/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2069/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (933/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2069/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (933/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2069/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2069/20000 : ℝ) ^ (8243/2048 : ℝ) ≤ (10823967014658503/100000000000000000000 : ℝ) := by
    have hpowers : (2069/20000 : ℝ)^8243 ≤ (10823967014658503/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2069 : ℕ)^8243*100000000000000000000^2048 ≤ 10823967014658503^2048*20000^8243 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2069 20000 10823967014658503 100000000000000000000 8243 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2069/20000 : ℝ)) (X := (10823967014658503/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (933/6250 : ℝ) ^ (8243/2048 : ℝ) ≤ (740043479101941/1562500000000000000 : ℝ) := by
    have hpowers : (933/6250 : ℝ)^8243 ≤ (740043479101941/1562500000000000000 : ℝ)^2048 := by
      have hnat : (933 : ℕ)^8243*1562500000000000000^2048 ≤ 740043479101941^2048*6250^8243 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        933 6250 740043479101941 1562500000000000000 8243 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (933/6250 : ℝ)) (X := (740043479101941/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010823967014658503/50000000000000000000 : ℝ) ≤ (5000268903086397/5000000000000000 : ℝ) ^ (8243/2048 : ℝ) := by
    have hpowers : (50010823967014658503/50000000000000000000 : ℝ)^2048 ≤ (5000268903086397/5000000000000000 : ℝ)^8243 := by
      have hnat : (50010823967014658503 : ℕ)^2048*5000000000000000^8243 ≤ 5000268903086397^8243*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010823967014658503 50000000000000000000 5000268903086397 5000000000000000 2048 8243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000268903086397/5000000000000000 : ℝ)) (X := (50010823967014658503/50000000000000000000 : ℝ)) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100058186749677182727/100000000000000000000 : ℝ) ≤ (625090334538701/625000000000000 : ℝ) ^ (8243/2048 : ℝ) := by
    have hpowers : (100058186749677182727/100000000000000000000 : ℝ)^2048 ≤ (625090334538701/625000000000000 : ℝ)^8243 := by
      have hnat : (100058186749677182727 : ℕ)^2048*625000000000000^8243 ≤ 625090334538701^8243*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100058186749677182727 100000000000000000000 625090334538701 625000000000000 2048 8243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625090334538701/625000000000000 : ℝ)) (X := (100058186749677182727/100000000000000000000 : ℝ)) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (781990043479101941/781250000000000000 : ℝ) ≤ (5001176449532819/5000000000000000 : ℝ) ^ (8243/2048 : ℝ) := by
    have hpowers : (781990043479101941/781250000000000000 : ℝ)^2048 ≤ (5001176449532819/5000000000000000 : ℝ)^8243 := by
      have hnat : (781990043479101941 : ℕ)^2048*5000000000000000^8243 ≤ 5001176449532819^8243*781250000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781990043479101941 781250000000000000 5001176449532819 5000000000000000 2048 8243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001176449532819/5000000000000000 : ℝ)) (X := (781990043479101941/781250000000000000 : ℝ)) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10823967014658503/100000000000000000000 : ℝ) ≤ ((22906843814856721861/22915000000000000000 : ℝ)+2*(453773223211/229150000000000 : ℝ)*(2069/20000 : ℝ))^(8243/2048 : ℝ) := by
    rw [show (22906843814856721861/22915000000000000000 : ℝ)+2*(453773223211/229150000000000 : ℝ)*(2069/20000 : ℝ)=(5000268903086397/5000000000000000 : ℝ) by norm_num, show 1+2*(10823967014658503/100000000000000000000 : ℝ)=(50010823967014658503/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(740043479101941/1562500000000000000 : ℝ)+(10823967014658503/100000000000000000000 : ℝ) ≤ ((22906843814856721861/22915000000000000000 : ℝ)+(453773223211/229150000000000 : ℝ)*((933/6250 : ℝ)+(2069/20000 : ℝ)))^(8243/2048 : ℝ) := by
    rw [show (22906843814856721861/22915000000000000000 : ℝ)+(453773223211/229150000000000 : ℝ)*((933/6250 : ℝ)+(2069/20000 : ℝ))=(625090334538701/625000000000000 : ℝ) by norm_num, show 1+(740043479101941/1562500000000000000 : ℝ)+(10823967014658503/100000000000000000000 : ℝ)=(100058186749677182727/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(740043479101941/1562500000000000000 : ℝ) ≤ ((22906843814856721861/22915000000000000000 : ℝ)+2*(453773223211/229150000000000 : ℝ)*(933/6250 : ℝ))^(8243/2048 : ℝ) := by
    rw [show (22906843814856721861/22915000000000000000 : ℝ)+2*(453773223211/229150000000000 : ℝ)*(933/6250 : ℝ)=(5001176449532819/5000000000000000 : ℝ) by norm_num, show 1+2*(740043479101941/1562500000000000000 : ℝ)=(781990043479101941/781250000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22906843814856721861/22915000000000000000 : ℝ)*(X 1 0+X 2 0)+(453773223211/229150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8243/2048 : ℝ)) (lo := (2069/20000 : ℝ)) (hi := (933/6250 : ℝ)) (c := (22906843814856721861/22915000000000000000 : ℝ)) (alpha := (453773223211/229150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22906843814856721861/22915000000000000000 : ℝ)*(X 0 1+X 2 1)+(453773223211/229150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8243/2048 : ℝ)) (lo := (2069/20000 : ℝ)) (hi := (933/6250 : ℝ)) (c := (22906843814856721861/22915000000000000000 : ℝ)) (alpha := (453773223211/229150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22906843814856721861/22915000000000000000 : ℝ)*(X 0 2+X 1 2)+(453773223211/229150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8243/2048 : ℝ)) (lo := (2069/20000 : ℝ)) (hi := (933/6250 : ℝ)) (c := (22906843814856721861/22915000000000000000 : ℝ)) (alpha := (453773223211/229150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-552513933/2500000000 : ℝ)*X 0 0+(5406662979/10000000000 : ℝ)*X 0 1+(1313215771/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674003653/5000000000 : ℝ)*X 1 0+(-2288297163/10000000000 : ℝ)*X 1 1+(5252863059/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534800731/1000000000 : ℝ)*X 2 0+(5252863053/10000000000 : ℝ)*X 2 1+(-1144148583/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((875400877/2000000000 : ℝ)*X 0 0+(2114680529/5000000000 : ℝ)*X 0 1+(4529890137/10000000000 : ℝ)*X 0 2+(875400877/2000000000 : ℝ)*X 1 0+(2114680529/5000000000 : ℝ)*X 1 1+(4529890137/10000000000 : ℝ)*X 1 2+(875400877/2000000000 : ℝ)*X 2 0+(2114680529/5000000000 : ℝ)*X 2 1+(4529890137/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2210064131/10000000000 : ℝ)*X 0 0+(656664581/1250000000 : ℝ)*X 0 1+(270310373/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2654658231/5000000000 : ℝ)*X 1 0+(-2134952767/10000000000 : ℝ)*X 1 1+(5406207507/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5309316473/10000000000 : ℝ)*X 2 0+(2703103747/5000000000 : ℝ)*X 2 1+(-2134952769/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4377020569/10000000000 : ℝ)*X 0 0+(4529003993/10000000000 : ℝ)*X 0 1+(4230251109/10000000000 : ℝ)*X 0 2+(4377020569/10000000000 : ℝ)*X 1 0+(4529003993/10000000000 : ℝ)*X 1 1+(4230251109/10000000000 : ℝ)*X 1 2+(4377020569/10000000000 : ℝ)*X 2 0+(4529003993/10000000000 : ℝ)*X 2 1+(4230251109/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11163760298870840407692832311/1145750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1048751473/50000000000000 : ℝ)*(base19) + (389295031/20000000000000 : ℝ)*(base23) + (83370593/100000000000000 : ℝ)*(lower2) + (272688507/100000000000000 : ℝ)*(upper3) + (151048293/100000000000000 : ℝ)*(upper5) + (4914782086802183/100000000000000 : ℝ)*(major0) + (4914782086802183/100000000000000 : ℝ)*(major1) + (4914782086802183/100000000000000 : ℝ)*(major2) + (3251001917890519/50000000000000 : ℝ)*(sp0) + (1300409565727499/20000000000000 : ℝ)*(sp1) + (3251023989832643/50000000000000 : ℝ)*(sp2) + (3327487981897081/100000000000000 : ℝ)*(sp3) + (11522589851/25000000000000 : ℝ)*(sp4) + (324259741/1250000000000 : ℝ)*(sp7) + (1663756961338181/50000000000000 : ℝ)*(f.failure) + (6502049926140441/100000000000000 : ℝ)*(f.sum) + (100138920379251/22915000000000000000000000000 : ℝ)*base65 + (7717001697658077437/2291500000000000000000000000000000 : ℝ)*base68 + (12485567177463577437/2291500000000000000000000000000000 : ℝ)*base70 + (2266921172507422563/2291500000000000000000000000000000 : ℝ)*base71 + (126810896774731/22915000000000000000000000000 : ℝ)*base73 + (3590583583106922563/2291500000000000000000000000000000 : ℝ)*base75 + (21525369604122422563/2291500000000000000000000000000000 : ℝ)*base77 + (8106428714535922563/2291500000000000000000000000000000 : ℝ)*base79 + (3800526371789/22915000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (34113463/5000000000000000000000 : ℝ)*base89 + (34113463/5000000000000000000000 : ℝ)*base91 + (34113463/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2046520054536408242529532743/286437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (82422041/6250000000000 : ℝ)*(base19) + (343074739/25000000000000 : ℝ)*(base23) + (11982579/100000000000000 : ℝ)*(upper2) + (175449549/100000000000000 : ℝ)*(upper3) + (58979321/50000000000000 : ℝ)*(upper5) + (2471965571158521/50000000000000 : ℝ)*(major0) + (2471965571158521/50000000000000 : ℝ)*(major1) + (2471965571158521/50000000000000 : ℝ)*(major2) + (15034745121/50000000000000 : ℝ)*(sp1) + (16230402391/50000000000000 : ℝ)*(sp2) + (1635153247195903/25000000000000 : ℝ)*(sp4) + (6540581600540713/100000000000000 : ℝ)*(sp5) + (6540579155679873/100000000000000 : ℝ)*(sp6) + (1673624528846313/50000000000000 : ℝ)*(sp7) + (1673624528846313/50000000000000 : ℝ)*(f.failure) + (1635153247195903/25000000000000 : ℝ)*(f.sum) + (3802647862703/11457500000000000000000000000 : ℝ)*base66 + (13900959140145272419/1145750000000000000000000000000000 : ℝ)*base68 + (24016487491015272419/1145750000000000000000000000000000 : ℝ)*base70 + (6103009225648772419/1145750000000000000000000000000000 : ℝ)*base72 + (49669227991309/22915000000000000000000000000 : ℝ)*base73 + (5137228309057022419/1145750000000000000000000000000000 : ℝ)*base76 + (24788563490012022419/1145750000000000000000000000000000 : ℝ)*base78 + (2251921597365727581/1145750000000000000000000000000000 : ℝ)*base79 + (107678853335949/22915000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (6227901/5000000000000000000000 : ℝ)*base90 + (6227901/5000000000000000000000 : ℝ)*base92 + (6227901/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1051_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147701323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (933/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2069/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10989/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7123/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1051_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1051_s5_0 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2210928479/10000000000 : ℝ)*x 0 + (5397437671/10000000000 : ℝ)*x 1 + (657689529/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2210928479/10000000000 : ℝ)^2061 ≤ (2685116555313/20000000000000 : ℝ)^1549 := by
    have hnat : (2210928479 : ℕ)^2061*20000000000000^1549 ≤ 2685116555313^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210928479 10000000000 2685116555313 20000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397437671/10000000000 : ℝ)^2061 ≤ (44021623376203/100000000000000 : ℝ)^1549 := by
    have hnat : (5397437671 : ℕ)^2061*100000000000000^1549 ≤ 44021623376203^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397437671 10000000000 44021623376203 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (657689529/1250000000 : ℝ)^2061 ≤ (5319099230077/12500000000000 : ℝ)^1549 := by
    have hnat : (657689529 : ℕ)^2061*12500000000000^1549 ≤ 5319099230077^1549*1250000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657689529 1250000000 5319099230077 12500000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2210928479/10000000000 : ℝ), (5397437671/10000000000 : ℝ), (657689529/1250000000 : ℝ)] ![(2685116555313/20000000000000 : ℝ), (44021623376203/100000000000000 : ℝ), (5319099230077/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2210928479/10000000000 : ℝ)|^2061 ≤ (2685116555313/20000000000000 : ℝ)^1549
        have hw : |(-2210928479/10000000000 : ℝ)|=(2210928479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397437671/10000000000 : ℝ)|^2061 ≤ (44021623376203/100000000000000 : ℝ)^1549
        have hw : |(5397437671/10000000000 : ℝ)|=(5397437671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(657689529/1250000000 : ℝ)|^2061 ≤ (5319099230077/12500000000000 : ℝ)^1549
        have hw : |(657689529/1250000000 : ℝ)|=(657689529/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s5_1 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5345713931/10000000000 : ℝ)*x 0 + (-2279937351/10000000000 : ℝ)*x 1 + (5261515741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345713931/10000000000 : ℝ)^2061 ≤ (43461214420361/100000000000000 : ℝ)^1549 := by
    have hnat : (5345713931 : ℕ)^2061*100000000000000^1549 ≤ 43461214420361^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345713931 10000000000 43461214420361 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2279937351/10000000000 : ℝ)^2061 ≤ (2797199401653/20000000000000 : ℝ)^1549 := by
    have hnat : (2279937351 : ℕ)^2061*20000000000000^1549 ≤ 2797199401653^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2279937351 10000000000 2797199401653 20000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261515741/10000000000 : ℝ)^2061 ≤ (42552788557073/100000000000000 : ℝ)^1549 := by
    have hnat : (5261515741 : ℕ)^2061*100000000000000^1549 ≤ 42552788557073^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261515741 10000000000 42552788557073 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345713931/10000000000 : ℝ), (-2279937351/10000000000 : ℝ), (5261515741/10000000000 : ℝ)] ![(43461214420361/100000000000000 : ℝ), (2797199401653/20000000000000 : ℝ), (42552788557073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345713931/10000000000 : ℝ)|^2061 ≤ (43461214420361/100000000000000 : ℝ)^1549
        have hw : |(5345713931/10000000000 : ℝ)|=(5345713931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2279937351/10000000000 : ℝ)|^2061 ≤ (2797199401653/20000000000000 : ℝ)^1549
        have hw : |(-2279937351/10000000000 : ℝ)|=(2279937351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261515741/10000000000 : ℝ)|^2061 ≤ (42552788557073/100000000000000 : ℝ)^1549
        have hw : |(5261515741/10000000000 : ℝ)|=(5261515741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s5_2 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5345713623/10000000000 : ℝ)*x 0 + (5261516129/10000000000 : ℝ)*x 1 + (-2279937247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345713623/10000000000 : ℝ)^2061 ≤ (43461211088603/100000000000000 : ℝ)^1549 := by
    have hnat : (5345713623 : ℕ)^2061*100000000000000^1549 ≤ 43461211088603^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345713623 10000000000 43461211088603 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5261516129/10000000000 : ℝ)^2061 ≤ (1329774772883/3125000000000 : ℝ)^1549 := by
    have hnat : (5261516129 : ℕ)^2061*3125000000000^1549 ≤ 1329774772883^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261516129 10000000000 1329774772883 3125000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2279937247/10000000000 : ℝ)^2061 ≤ (1748249519927/12500000000000 : ℝ)^1549 := by
    have hnat : (2279937247 : ℕ)^2061*12500000000000^1549 ≤ 1748249519927^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2279937247 10000000000 1748249519927 12500000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345713623/10000000000 : ℝ), (5261516129/10000000000 : ℝ), (-2279937247/10000000000 : ℝ)] ![(43461211088603/100000000000000 : ℝ), (1329774772883/3125000000000 : ℝ), (1748249519927/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345713623/10000000000 : ℝ)|^2061 ≤ (43461211088603/100000000000000 : ℝ)^1549
        have hw : |(5345713623/10000000000 : ℝ)|=(5345713623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5261516129/10000000000 : ℝ)|^2061 ≤ (1329774772883/3125000000000 : ℝ)^1549
        have hw : |(5261516129/10000000000 : ℝ)|=(5261516129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2279937247/10000000000 : ℝ)|^2061 ≤ (1748249519927/12500000000000 : ℝ)^1549
        have hw : |(-2279937247/10000000000 : ℝ)|=(2279937247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s5_3 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (875502179/2000000000 : ℝ)*x 0 + (4246761831/10000000000 : ℝ)*x 1 + (4512356159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (875502179/2000000000 : ℝ)^2061 ≤ (8328753159717/25000000000000 : ℝ)^1549 := by
    have hnat : (875502179 : ℕ)^2061*25000000000000^1549 ≤ 8328753159717^1549*2000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875502179 2000000000 8328753159717 25000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4246761831/10000000000 : ℝ)^2061 ≤ (31997622953313/100000000000000 : ℝ)^1549 := by
    have hnat : (4246761831 : ℕ)^2061*100000000000000^1549 ≤ 31997622953313^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4246761831 10000000000 31997622953313 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4512356159/10000000000 : ℝ)^2061 ≤ (4335920549059/12500000000000 : ℝ)^1549 := by
    have hnat : (4512356159 : ℕ)^2061*12500000000000^1549 ≤ 4335920549059^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4512356159 10000000000 4335920549059 12500000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(875502179/2000000000 : ℝ), (4246761831/10000000000 : ℝ), (4512356159/10000000000 : ℝ)] ![(8328753159717/25000000000000 : ℝ), (31997622953313/100000000000000 : ℝ), (4335920549059/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(875502179/2000000000 : ℝ)|^2061 ≤ (8328753159717/25000000000000 : ℝ)^1549
        have hw : |(875502179/2000000000 : ℝ)|=(875502179/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4246761831/10000000000 : ℝ)|^2061 ≤ (31997622953313/100000000000000 : ℝ)^1549
        have hw : |(4246761831/10000000000 : ℝ)|=(4246761831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4512356159/10000000000 : ℝ)|^2061 ≤ (4335920549059/12500000000000 : ℝ)^1549
        have hw : |(4512356159/10000000000 : ℝ)|=(4512356159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s5_4 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1105467327/5000000000 : ℝ)*x 0 + (657733813/1250000000 : ℝ)*x 1 + (674635221/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1105467327/5000000000 : ℝ)^2061 ≤ (13425632667563/100000000000000 : ℝ)^1549 := by
    have hnat : (1105467327 : ℕ)^2061*100000000000000^1549 ≤ 13425632667563^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105467327 5000000000 13425632667563 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (657733813/1250000000 : ℝ)^2061 ≤ (4255660612597/10000000000000 : ℝ)^1549 := by
    have hnat : (657733813 : ℕ)^2061*10000000000000^1549 ≤ 4255660612597^1549*1250000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657733813 1250000000 4255660612597 10000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674635221/1250000000 : ℝ)^2061 ≤ (44017761201561/100000000000000 : ℝ)^1549 := by
    have hnat : (674635221 : ℕ)^2061*100000000000000^1549 ≤ 44017761201561^1549*1250000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674635221 1250000000 44017761201561 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1105467327/5000000000 : ℝ), (657733813/1250000000 : ℝ), (674635221/1250000000 : ℝ)] ![(13425632667563/100000000000000 : ℝ), (4255660612597/10000000000000 : ℝ), (44017761201561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1105467327/5000000000 : ℝ)|^2061 ≤ (13425632667563/100000000000000 : ℝ)^1549
        have hw : |(-1105467327/5000000000 : ℝ)|=(1105467327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(657733813/1250000000 : ℝ)|^2061 ≤ (4255660612597/10000000000000 : ℝ)^1549
        have hw : |(657733813/1250000000 : ℝ)|=(657733813/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674635221/1250000000 : ℝ)|^2061 ≤ (44017761201561/100000000000000 : ℝ)^1549
        have hw : |(674635221/1250000000 : ℝ)|=(674635221/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s5_5 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5311519207/10000000000 : ℝ)*x 0 + (-428874337/2000000000 : ℝ)*x 1 + (269854091/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311519207/10000000000 : ℝ)^2061 ≤ (21545854080707/50000000000000 : ℝ)^1549 := by
    have hnat : (5311519207 : ℕ)^2061*50000000000000^1549 ≤ 21545854080707^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311519207 10000000000 21545854080707 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (428874337/2000000000 : ℝ)^2061 ≤ (3222632514959/25000000000000 : ℝ)^1549 := by
    have hnat : (428874337 : ℕ)^2061*25000000000000^1549 ≤ 3222632514959^1549*2000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428874337 2000000000 3222632514959 25000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269854091/500000000 : ℝ)^2061 ≤ (44017761765847/100000000000000 : ℝ)^1549 := by
    have hnat : (269854091 : ℕ)^2061*100000000000000^1549 ≤ 44017761765847^1549*500000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269854091 500000000 44017761765847 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311519207/10000000000 : ℝ), (-428874337/2000000000 : ℝ), (269854091/500000000 : ℝ)] ![(21545854080707/50000000000000 : ℝ), (3222632514959/25000000000000 : ℝ), (44017761765847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311519207/10000000000 : ℝ)|^2061 ≤ (21545854080707/50000000000000 : ℝ)^1549
        have hw : |(5311519207/10000000000 : ℝ)|=(5311519207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-428874337/2000000000 : ℝ)|^2061 ≤ (3222632514959/25000000000000 : ℝ)^1549
        have hw : |(-428874337/2000000000 : ℝ)|=(428874337/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269854091/500000000 : ℝ)|^2061 ≤ (44017761765847/100000000000000 : ℝ)^1549
        have hw : |(269854091/500000000 : ℝ)|=(269854091/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s5_6 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2655759611/5000000000 : ℝ)*x 0 + (2698540869/5000000000 : ℝ)*x 1 + (-85774871/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655759611/5000000000 : ℝ)^2061 ≤ (43091708323331/100000000000000 : ℝ)^1549 := by
    have hnat : (2655759611 : ℕ)^2061*100000000000000^1549 ≤ 43091708323331^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655759611 5000000000 43091708323331 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698540869/5000000000 : ℝ)^2061 ≤ (11004440219003/25000000000000 : ℝ)^1549 := by
    have hnat : (2698540869 : ℕ)^2061*25000000000000^1549 ≤ 11004440219003^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698540869 5000000000 11004440219003 25000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (85774871/400000000 : ℝ)^2061 ≤ (6445265389841/50000000000000 : ℝ)^1549 := by
    have hnat : (85774871 : ℕ)^2061*50000000000000^1549 ≤ 6445265389841^1549*400000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85774871 400000000 6445265389841 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655759611/5000000000 : ℝ), (2698540869/5000000000 : ℝ), (-85774871/400000000 : ℝ)] ![(43091708323331/100000000000000 : ℝ), (11004440219003/25000000000000 : ℝ), (6445265389841/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655759611/5000000000 : ℝ)|^2061 ≤ (43091708323331/100000000000000 : ℝ)^1549
        have hw : |(2655759611/5000000000 : ℝ)|=(2655759611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2698540869/5000000000 : ℝ)|^2061 ≤ (11004440219003/25000000000000 : ℝ)^1549
        have hw : |(2698540869/5000000000 : ℝ)|=(2698540869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-85774871/400000000 : ℝ)|^2061 ≤ (6445265389841/50000000000000 : ℝ)^1549
        have hw : |(-85774871/400000000 : ℝ)|=(85774871/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s5_7 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4377522507/10000000000 : ℝ)*x 0 + (281978953/625000000 : ℝ)*x 1 + (424745701/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4377522507/10000000000 : ℝ)^2061 ≤ (3331513022241/10000000000000 : ℝ)^1549 := by
    have hnat : (4377522507 : ℕ)^2061*10000000000000^1549 ≤ 3331513022241^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4377522507 10000000000 3331513022241 10000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (281978953/625000000 : ℝ)^2061 ≤ (8670069354211/25000000000000 : ℝ)^1549 := by
    have hnat : (281978953 : ℕ)^2061*25000000000000^1549 ≤ 8670069354211^1549*625000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281978953 625000000 8670069354211 25000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (424745701/1000000000 : ℝ)^2061 ≤ (16002296171741/50000000000000 : ℝ)^1549 := by
    have hnat : (424745701 : ℕ)^2061*50000000000000^1549 ≤ 16002296171741^1549*1000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424745701 1000000000 16002296171741 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4377522507/10000000000 : ℝ), (281978953/625000000 : ℝ), (424745701/1000000000 : ℝ)] ![(3331513022241/10000000000000 : ℝ), (8670069354211/25000000000000 : ℝ), (16002296171741/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4377522507/10000000000 : ℝ)|^2061 ≤ (3331513022241/10000000000000 : ℝ)^1549
        have hw : |(4377522507/10000000000 : ℝ)|=(4377522507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(281978953/625000000 : ℝ)|^2061 ≤ (8670069354211/25000000000000 : ℝ)^1549
        have hw : |(281978953/625000000 : ℝ)|=(281978953/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(424745701/1000000000 : ℝ)|^2061 ≤ (16002296171741/50000000000000 : ℝ)^1549
        have hw : |(424745701/1000000000 : ℝ)|=(424745701/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1051_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147701323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7123/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10989/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5587/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14053/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7123/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10989/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7123/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10989/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7123/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10989/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7123/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10989/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7123/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10989/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7123/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10989/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10989/100000 : ℝ) ^ (8243/2048 : ℝ) ≤ (2760452636461517/20000000000000000000 : ℝ) := by
    have hpowers : (10989/100000 : ℝ)^8243 ≤ (2760452636461517/20000000000000000000 : ℝ)^2048 := by
      have hnat : (10989 : ℕ)^8243*20000000000000000000^2048 ≤ 2760452636461517^2048*100000^8243 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10989 100000 2760452636461517 20000000000000000000 8243 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10989/100000 : ℝ)) (X := (2760452636461517/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7123/50000 : ℝ) ^ (8243/2048 : ℝ) ≤ (4904635572945943/12500000000000000000 : ℝ) := by
    have hpowers : (7123/50000 : ℝ)^8243 ≤ (4904635572945943/12500000000000000000 : ℝ)^2048 := by
      have hnat : (7123 : ℕ)^8243*12500000000000000000^2048 ≤ 4904635572945943^2048*50000^8243 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7123 50000 4904635572945943 12500000000000000000 8243 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7123/50000 : ℝ)) (X := (4904635572945943/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002760452636461517/10000000000000000000 : ℝ) ≤ (10000685772250813/10000000000000000 : ℝ) ^ (8243/2048 : ℝ) := by
    have hpowers : (10002760452636461517/10000000000000000000 : ℝ)^2048 ≤ (10000685772250813/10000000000000000 : ℝ)^8243 := by
      have hnat : (10002760452636461517 : ℕ)^2048*10000000000000000^8243 ≤ 10000685772250813^8243*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002760452636461517 10000000000000000000 10000685772250813 10000000000000000 2048 8243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000685772250813/10000000000000000 : ℝ)) (X := (10002760452636461517/10000000000000000000 : ℝ)) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100053039347765875129/100000000000000000000 : ℝ) ≤ (2000263503436139/2000000000000000 : ℝ) ^ (8243/2048 : ℝ) := by
    have hpowers : (100053039347765875129/100000000000000000000 : ℝ)^2048 ≤ (2000263503436139/2000000000000000 : ℝ)^8243 := by
      have hnat : (100053039347765875129 : ℕ)^2048*2000000000000000^8243 ≤ 2000263503436139^8243*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100053039347765875129 100000000000000000000 2000263503436139 2000000000000000 2048 8243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000263503436139/2000000000000000 : ℝ)) (X := (100053039347765875129/100000000000000000000 : ℝ)) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254904635572945943/6250000000000000000 : ℝ) ≤ (10001949262110577/10000000000000000 : ℝ) ^ (8243/2048 : ℝ) := by
    have hpowers : (6254904635572945943/6250000000000000000 : ℝ)^2048 ≤ (10001949262110577/10000000000000000 : ℝ)^8243 := by
      have hnat : (6254904635572945943 : ℕ)^2048*10000000000000000^8243 ≤ 10001949262110577^8243*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254904635572945943 6250000000000000000 10001949262110577 10000000000000000 2048 8243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001949262110577/10000000000000000 : ℝ)) (X := (6254904635572945943/6250000000000000000 : ℝ)) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2760452636461517/20000000000000000000 : ℝ) ≤ ((6511669814030390269/6514000000000000000 : ℝ)+2*(315872464941/162850000000000 : ℝ)*(10989/100000 : ℝ))^(8243/2048 : ℝ) := by
    rw [show (6511669814030390269/6514000000000000000 : ℝ)+2*(315872464941/162850000000000 : ℝ)*(10989/100000 : ℝ)=(10000685772250813/10000000000000000 : ℝ) by norm_num, show 1+2*(2760452636461517/20000000000000000000 : ℝ)=(10002760452636461517/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4904635572945943/12500000000000000000 : ℝ)+(2760452636461517/20000000000000000000 : ℝ) ≤ ((6511669814030390269/6514000000000000000 : ℝ)+(315872464941/162850000000000 : ℝ)*((7123/50000 : ℝ)+(10989/100000 : ℝ)))^(8243/2048 : ℝ) := by
    rw [show (6511669814030390269/6514000000000000000 : ℝ)+(315872464941/162850000000000 : ℝ)*((7123/50000 : ℝ)+(10989/100000 : ℝ))=(2000263503436139/2000000000000000 : ℝ) by norm_num, show 1+(4904635572945943/12500000000000000000 : ℝ)+(2760452636461517/20000000000000000000 : ℝ)=(100053039347765875129/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4904635572945943/12500000000000000000 : ℝ) ≤ ((6511669814030390269/6514000000000000000 : ℝ)+2*(315872464941/162850000000000 : ℝ)*(7123/50000 : ℝ))^(8243/2048 : ℝ) := by
    rw [show (6511669814030390269/6514000000000000000 : ℝ)+2*(315872464941/162850000000000 : ℝ)*(7123/50000 : ℝ)=(10001949262110577/10000000000000000 : ℝ) by norm_num, show 1+2*(4904635572945943/12500000000000000000 : ℝ)=(6254904635572945943/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6511669814030390269/6514000000000000000 : ℝ)*(X 1 0+X 2 0)+(315872464941/162850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8243/2048 : ℝ)) (lo := (10989/100000 : ℝ)) (hi := (7123/50000 : ℝ)) (c := (6511669814030390269/6514000000000000000 : ℝ)) (alpha := (315872464941/162850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6511669814030390269/6514000000000000000 : ℝ)*(X 0 1+X 2 1)+(315872464941/162850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8243/2048 : ℝ)) (lo := (10989/100000 : ℝ)) (hi := (7123/50000 : ℝ)) (c := (6511669814030390269/6514000000000000000 : ℝ)) (alpha := (315872464941/162850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6511669814030390269/6514000000000000000 : ℝ)*(X 0 2+X 1 2)+(315872464941/162850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8243/2048 : ℝ)) (lo := (10989/100000 : ℝ)) (hi := (7123/50000 : ℝ)) (c := (6511669814030390269/6514000000000000000 : ℝ)) (alpha := (315872464941/162850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2210928479/10000000000 : ℝ)*X 0 0+(5397437671/10000000000 : ℝ)*X 0 1+(657689529/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345713931/10000000000 : ℝ)*X 1 0+(-2279937351/10000000000 : ℝ)*X 1 1+(5261515741/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345713623/10000000000 : ℝ)*X 2 0+(5261516129/10000000000 : ℝ)*X 2 1+(-2279937247/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((875502179/2000000000 : ℝ)*X 0 0+(4246761831/10000000000 : ℝ)*X 0 1+(4512356159/10000000000 : ℝ)*X 0 2+(875502179/2000000000 : ℝ)*X 1 0+(4246761831/10000000000 : ℝ)*X 1 1+(4512356159/10000000000 : ℝ)*X 1 2+(875502179/2000000000 : ℝ)*X 2 0+(4246761831/10000000000 : ℝ)*X 2 1+(4512356159/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1105467327/5000000000 : ℝ)*X 0 0+(657733813/1250000000 : ℝ)*X 0 1+(674635221/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311519207/10000000000 : ℝ)*X 1 0+(-428874337/2000000000 : ℝ)*X 1 1+(269854091/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2655759611/5000000000 : ℝ)*X 2 0+(2698540869/5000000000 : ℝ)*X 2 1+(-85774871/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4377522507/10000000000 : ℝ)*X 0 0+(281978953/625000000 : ℝ)*X 0 1+(424745701/1000000000 : ℝ)*X 0 2+(4377522507/10000000000 : ℝ)*X 1 0+(281978953/625000000 : ℝ)*X 1 1+(424745701/1000000000 : ℝ)*X 1 2+(4377522507/10000000000 : ℝ)*X 2 0+(281978953/625000000 : ℝ)*X 2 1+(424745701/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (78117068517718733384796543/16285000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (194176643/12500000000000 : ℝ)*(base19) + (450984509/50000000000000 : ℝ)*(base23) + (132669123/100000000000000 : ℝ)*(lower2) + (11029043/100000000000000 : ℝ)*(lower4) + (91974253/100000000000000 : ℝ)*(lower5) + (278060660168951/5000000000000 : ℝ)*(major0) + (278060660168951/5000000000000 : ℝ)*(major1) + (278060660168951/5000000000000 : ℝ)*(major2) + (7357223654140299/100000000000000 : ℝ)*(sp0) + (3678624875460339/50000000000000 : ℝ)*(sp1) + (1839312600591201/25000000000000 : ℝ)*(sp2) + (3765157373071839/100000000000000 : ℝ)*(sp3) + (27650193523/100000000000000 : ℝ)*(sp4) + (17569456617/100000000000000 : ℝ)*(sp7) + (470646867816057/12500000000000 : ℝ)*(f.failure) + (3678625652166911/50000000000000 : ℝ)*(f.sum) + (18332702422651/3257000000000000000000000000 : ℝ)*base65 + (459158808695757819/32570000000000000000000000000000 : ℝ)*base67 + (298122138332267819/32570000000000000000000000000000 : ℝ)*base69 + (202807129671037819/32570000000000000000000000000000 : ℝ)*base71 + (16590201605649/3257000000000000000000000000 : ℝ)*base73 + (831749738488352181/32570000000000000000000000000000 : ℝ)*base76 + (308475416911142181/32570000000000000000000000000000 : ℝ)*base78 + (52666497393607819/32570000000000000000000000000000 : ℝ)*base79 + (14042765971497/3257000000000000000000000000 : ℝ)*base81 + (10456589/1250000000000000000000 : ℝ)*base90 + (10456589/1250000000000000000000 : ℝ)*base92 + (10456589/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1358092681014844903190261817/162850000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2119147121/100000000000000 : ℝ)*(base19) + (1050052249/50000000000000 : ℝ)*(base23) + (1506577/100000000000000 : ℝ)*(upper2) + (106928717/50000000000000 : ℝ)*(upper3) + (260299289/100000000000000 : ℝ)*(upper5) + (5590378341542431/100000000000000 : ℝ)*(major0) + (5590378341542431/100000000000000 : ℝ)*(major1) + (5590378341542431/100000000000000 : ℝ)*(major2) + (59013803223/100000000000000 : ℝ)*(sp1) + (52371503071/100000000000000 : ℝ)*(sp2) + (7395835438927119/100000000000000 : ℝ)*(sp4) + (295830972239071/4000000000000 : ℝ)*(sp5) + (147915619346391/2000000000000 : ℝ)*(sp6) + (3784920966173357/100000000000000 : ℝ)*(sp7) + (3784920966173357/100000000000000 : ℝ)*(f.failure) + (7395835438927119/100000000000000 : ℝ)*(f.sum) + (11757226734163/16285000000000000000000000000 : ℝ)*base66 + (5598272278100956061/651400000000000000000000000000000 : ℝ)*base68 + (2742708895030956061/651400000000000000000000000000000 : ℝ)*base70 + (2307778283485956061/651400000000000000000000000000000 : ℝ)*base72 + (28355343110219/8142500000000000000000000000 : ℝ)*base74 + (4273562309472356061/651400000000000000000000000000000 : ℝ)*base76 + (3242013381751043939/651400000000000000000000000000000 : ℝ)*base77 + (15553691488967156061/651400000000000000000000000000000 : ℝ)*base80 + (121479557503013/16285000000000000000000000000 : ℝ)*base82 + (23748689/10000000000000000000000 : ℝ)*base90 + (23748689/10000000000000000000000 : ℝ)*base92 + (23748689/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1051_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147701323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7123/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10989/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5587/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14053/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1051_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1051_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147701323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16791/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8637/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5587/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14053/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1051_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1051_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1051_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147701323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16791/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8637/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5587/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14053/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1051_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

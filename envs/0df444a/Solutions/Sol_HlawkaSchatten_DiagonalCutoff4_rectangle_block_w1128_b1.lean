-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1128_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:25:53.352704+00:00
-- url     : https://prove2.me/submissions/bc7b257a-278c-403c-84fa-4af1d0125e0d

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
theorem support_rectangle_w1128_s3_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1084819337/5000000000 : ℝ)*x 0 + (5430648441/10000000000 : ℝ)*x 1 + (5230740159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1084819337/5000000000 : ℝ)^8321 ≤ (3293609763359/25000000000000 : ℝ)^6273 := by
    have hnat : (1084819337 : ℕ)^8321*25000000000000^6273 ≤ 3293609763359^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084819337 5000000000 3293609763359 25000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5430648441/10000000000 : ℝ)^8321 ≤ (44492463287233/100000000000000 : ℝ)^6273 := by
    have hnat : (5430648441 : ℕ)^8321*100000000000000^6273 ≤ 44492463287233^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430648441 10000000000 44492463287233 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5230740159/10000000000 : ℝ)^8321 ≤ (2645818603001/6250000000000 : ℝ)^6273 := by
    have hnat : (5230740159 : ℕ)^8321*6250000000000^6273 ≤ 2645818603001^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230740159 10000000000 2645818603001 6250000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1084819337/5000000000 : ℝ), (5430648441/10000000000 : ℝ), (5230740159/10000000000 : ℝ)] ![(3293609763359/25000000000000 : ℝ), (44492463287233/100000000000000 : ℝ), (2645818603001/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1084819337/5000000000 : ℝ)|^8321 ≤ (3293609763359/25000000000000 : ℝ)^6273
        have hw : |(-1084819337/5000000000 : ℝ)|=(1084819337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5430648441/10000000000 : ℝ)|^8321 ≤ (44492463287233/100000000000000 : ℝ)^6273
        have hw : |(5430648441/10000000000 : ℝ)|=(5430648441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5230740159/10000000000 : ℝ)|^8321 ≤ (2645818603001/6250000000000 : ℝ)^6273
        have hw : |(5230740159/10000000000 : ℝ)|=(5230740159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s3_1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2677067837/5000000000 : ℝ)*x 0 + (-1135928467/5000000000 : ℝ)*x 1 + (2615370029/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677067837/5000000000 : ℝ)^8321 ≤ (43662869026063/100000000000000 : ℝ)^6273 := by
    have hnat : (2677067837 : ℕ)^8321*100000000000000^6273 ≤ 43662869026063^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677067837 5000000000 43662869026063 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1135928467/5000000000 : ℝ)^8321 ≤ (3501008597089/25000000000000 : ℝ)^6273 := by
    have hnat : (1135928467 : ℕ)^8321*25000000000000^6273 ≤ 3501008597089^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135928467 5000000000 3501008597089 25000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2615370029/5000000000 : ℝ)^8321 ≤ (1322909267617/3125000000000 : ℝ)^6273 := by
    have hnat : (2615370029 : ℕ)^8321*3125000000000^6273 ≤ 1322909267617^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615370029 5000000000 1322909267617 3125000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677067837/5000000000 : ℝ), (-1135928467/5000000000 : ℝ), (2615370029/5000000000 : ℝ)] ![(43662869026063/100000000000000 : ℝ), (3501008597089/25000000000000 : ℝ), (1322909267617/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677067837/5000000000 : ℝ)|^8321 ≤ (43662869026063/100000000000000 : ℝ)^6273
        have hw : |(2677067837/5000000000 : ℝ)|=(2677067837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1135928467/5000000000 : ℝ)|^8321 ≤ (3501008597089/25000000000000 : ℝ)^6273
        have hw : |(-1135928467/5000000000 : ℝ)|=(1135928467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2615370029/5000000000 : ℝ)|^8321 ≤ (1322909267617/3125000000000 : ℝ)^6273
        have hw : |(2615370029/5000000000 : ℝ)|=(2615370029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s3_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5354135769/10000000000 : ℝ)*x 0 + (5230740159/10000000000 : ℝ)*x 1 + (-2271856677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354135769/10000000000 : ℝ)^8321 ≤ (10915717513429/25000000000000 : ℝ)^6273 := by
    have hnat : (5354135769 : ℕ)^8321*25000000000000^6273 ≤ 10915717513429^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354135769 10000000000 10915717513429 25000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5230740159/10000000000 : ℝ)^8321 ≤ (2645818603001/6250000000000 : ℝ)^6273 := by
    have hnat : (5230740159 : ℕ)^8321*6250000000000^6273 ≤ 2645818603001^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230740159 10000000000 2645818603001 6250000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2271856677/10000000000 : ℝ)^8321 ≤ (14004032286971/100000000000000 : ℝ)^6273 := by
    have hnat : (2271856677 : ℕ)^8321*100000000000000^6273 ≤ 14004032286971^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2271856677 10000000000 14004032286971 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354135769/10000000000 : ℝ), (5230740159/10000000000 : ℝ), (-2271856677/10000000000 : ℝ)] ![(10915717513429/25000000000000 : ℝ), (2645818603001/6250000000000 : ℝ), (14004032286971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354135769/10000000000 : ℝ)|^8321 ≤ (10915717513429/25000000000000 : ℝ)^6273
        have hw : |(5354135769/10000000000 : ℝ)|=(5354135769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5230740159/10000000000 : ℝ)|^8321 ≤ (2645818603001/6250000000000 : ℝ)^6273
        have hw : |(5230740159/10000000000 : ℝ)|=(5230740159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2271856677/10000000000 : ℝ)|^8321 ≤ (14004032286971/100000000000000 : ℝ)^6273
        have hw : |(-2271856677/10000000000 : ℝ)|=(2271856677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s3_3 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4364299367/10000000000 : ℝ)*x 0 + (521310133/1250000000 : ℝ)*x 1 + (4567101123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364299367/10000000000 : ℝ)^8321 ≤ (8323277177643/25000000000000 : ℝ)^6273 := by
    have hnat : (4364299367 : ℕ)^8321*25000000000000^6273 ≤ 8323277177643^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364299367 10000000000 8323277177643 25000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521310133/1250000000 : ℝ)^8321 ≤ (1567310635857/5000000000000 : ℝ)^6273 := by
    have hnat : (521310133 : ℕ)^8321*5000000000000^6273 ≤ 1567310635857^6273*1250000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521310133 1250000000 1567310635857 5000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4567101123/10000000000 : ℝ)^8321 ≤ (35360678553817/100000000000000 : ℝ)^6273 := by
    have hnat : (4567101123 : ℕ)^8321*100000000000000^6273 ≤ 35360678553817^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4567101123 10000000000 35360678553817 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364299367/10000000000 : ℝ), (521310133/1250000000 : ℝ), (4567101123/10000000000 : ℝ)] ![(8323277177643/25000000000000 : ℝ), (1567310635857/5000000000000 : ℝ), (35360678553817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364299367/10000000000 : ℝ)|^8321 ≤ (8323277177643/25000000000000 : ℝ)^6273
        have hw : |(4364299367/10000000000 : ℝ)|=(4364299367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521310133/1250000000 : ℝ)|^8321 ≤ (1567310635857/5000000000000 : ℝ)^6273
        have hw : |(521310133/1250000000 : ℝ)|=(521310133/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4567101123/10000000000 : ℝ)|^8321 ≤ (35360678553817/100000000000000 : ℝ)^6273
        have hw : |(4567101123/10000000000 : ℝ)|=(4567101123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s3_4 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-542414361/2500000000 : ℝ)*x 0 + (653940399/1250000000 : ℝ)*x 1 + (1357465247/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542414361/2500000000 : ℝ)^8321 ≤ (823411889927/6250000000000 : ℝ)^6273 := by
    have hnat : (542414361 : ℕ)^8321*6250000000000^6273 ≤ 823411889927^6273*2500000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542414361 2500000000 823411889927 6250000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (653940399/1250000000 : ℝ)^8321 ≤ (42341504004707/100000000000000 : ℝ)^6273 := by
    have hnat : (653940399 : ℕ)^8321*100000000000000^6273 ≤ 42341504004707^6273*1250000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653940399 1250000000 42341504004707 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357465247/2500000000 : ℝ)^8321 ≤ (22241952869479/50000000000000 : ℝ)^6273 := by
    have hnat : (1357465247 : ℕ)^8321*50000000000000^6273 ≤ 22241952869479^6273*2500000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357465247 2500000000 22241952869479 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-542414361/2500000000 : ℝ), (653940399/1250000000 : ℝ), (1357465247/2500000000 : ℝ)] ![(823411889927/6250000000000 : ℝ), (42341504004707/100000000000000 : ℝ), (22241952869479/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-542414361/2500000000 : ℝ)|^8321 ≤ (823411889927/6250000000000 : ℝ)^6273
        have hw : |(-542414361/2500000000 : ℝ)|=(542414361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(653940399/1250000000 : ℝ)|^8321 ≤ (42341504004707/100000000000000 : ℝ)^6273
        have hw : |(653940399/1250000000 : ℝ)|=(653940399/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357465247/2500000000 : ℝ)|^8321 ≤ (22241952869479/50000000000000 : ℝ)^6273
        have hw : |(1357465247/2500000000 : ℝ)|=(1357465247/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s3_5 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (530354167/1000000000 : ℝ)*x 0 + (-1036368433/5000000000 : ℝ)*x 1 + (2714930241/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530354167/1000000000 : ℝ)^8321 ≤ (43116419161421/100000000000000 : ℝ)^6273 := by
    have hnat : (530354167 : ℕ)^8321*100000000000000^6273 ≤ 43116419161421^6273*1000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530354167 1000000000 43116419161421 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036368433/5000000000 : ℝ)^8321 ≤ (6199840294737/50000000000000 : ℝ)^6273 := by
    have hnat : (1036368433 : ℕ)^8321*50000000000000^6273 ≤ 6199840294737^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036368433 5000000000 6199840294737 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2714930241/5000000000 : ℝ)^8321 ≤ (11120975060049/25000000000000 : ℝ)^6273 := by
    have hnat : (2714930241 : ℕ)^8321*25000000000000^6273 ≤ 11120975060049^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714930241 5000000000 11120975060049 25000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530354167/1000000000 : ℝ), (-1036368433/5000000000 : ℝ), (2714930241/5000000000 : ℝ)] ![(43116419161421/100000000000000 : ℝ), (6199840294737/50000000000000 : ℝ), (11120975060049/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530354167/1000000000 : ℝ)|^8321 ≤ (43116419161421/100000000000000 : ℝ)^6273
        have hw : |(530354167/1000000000 : ℝ)|=(530354167/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1036368433/5000000000 : ℝ)|^8321 ≤ (6199840294737/50000000000000 : ℝ)^6273
        have hw : |(-1036368433/5000000000 : ℝ)|=(1036368433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2714930241/5000000000 : ℝ)|^8321 ≤ (11120975060049/25000000000000 : ℝ)^6273
        have hw : |(2714930241/5000000000 : ℝ)|=(2714930241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s3_6 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (212141713/400000000 : ℝ)*x 0 + (2714929879/5000000000 : ℝ)*x 1 + (-2072736287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212141713/400000000 : ℝ)^8321 ≤ (43116431616857/100000000000000 : ℝ)^6273 := by
    have hnat : (212141713 : ℕ)^8321*100000000000000^6273 ≤ 43116431616857^6273*400000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212141713 400000000 43116431616857 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2714929879/5000000000 : ℝ)^8321 ≤ (22241946186201/50000000000000 : ℝ)^6273 := by
    have hnat : (2714929879 : ℕ)^8321*50000000000000^6273 ≤ 22241946186201^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714929879 5000000000 22241946186201 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2072736287/10000000000 : ℝ)^8321 ≤ (12399675994901/100000000000000 : ℝ)^6273 := by
    have hnat : (2072736287 : ℕ)^8321*100000000000000^6273 ≤ 12399675994901^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072736287 10000000000 12399675994901 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212141713/400000000 : ℝ), (2714929879/5000000000 : ℝ), (-2072736287/10000000000 : ℝ)] ![(43116431616857/100000000000000 : ℝ), (22241946186201/50000000000000 : ℝ), (12399675994901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212141713/400000000 : ℝ)|^8321 ≤ (43116431616857/100000000000000 : ℝ)^6273
        have hw : |(212141713/400000000 : ℝ)|=(212141713/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2714929879/5000000000 : ℝ)|^8321 ≤ (22241946186201/50000000000000 : ℝ)^6273
        have hw : |(2714929879/5000000000 : ℝ)|=(2714929879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2072736287/10000000000 : ℝ)|^8321 ≤ (12399675994901/100000000000000 : ℝ)^6273
        have hw : |(-2072736287/10000000000 : ℝ)|=(2072736287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s3_7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (436433633/1000000000 : ℝ)*x 0 + (182621899/400000000 : ℝ)*x 1 + (4172043783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436433633/1000000000 : ℝ)^8321 ≤ (166467413709/500000000000 : ℝ)^6273 := by
    have hnat : (436433633 : ℕ)^8321*500000000000^6273 ≤ 166467413709^6273*1000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436433633 1000000000 166467413709 500000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (182621899/400000000 : ℝ)^8321 ≤ (35344723116651/100000000000000 : ℝ)^6273 := by
    have hnat : (182621899 : ℕ)^8321*100000000000000^6273 ≤ 35344723116651^6273*400000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182621899 400000000 35344723116651 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172043783/10000000000 : ℝ)^8321 ≤ (31361794121967/100000000000000 : ℝ)^6273 := by
    have hnat : (4172043783 : ℕ)^8321*100000000000000^6273 ≤ 31361794121967^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172043783 10000000000 31361794121967 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(436433633/1000000000 : ℝ), (182621899/400000000 : ℝ), (4172043783/10000000000 : ℝ)] ![(166467413709/500000000000 : ℝ), (35344723116651/100000000000000 : ℝ), (31361794121967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(436433633/1000000000 : ℝ)|^8321 ≤ (166467413709/500000000000 : ℝ)^6273
        have hw : |(436433633/1000000000 : ℝ)|=(436433633/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(182621899/400000000 : ℝ)|^8321 ≤ (35344723116651/100000000000000 : ℝ)^6273
        have hw : |(182621899/400000000 : ℝ)|=(182621899/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172043783/10000000000 : ℝ)|^8321 ≤ (31361794121967/100000000000000 : ℝ)^6273
        have hw : |(4172043783/10000000000 : ℝ)|=(4172043783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1128_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9325039/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3309/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4503/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10593/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14823/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3309/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4503/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3309/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4503/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3309/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4503/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3309/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4503/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3309/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4503/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3309/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4503/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4503/50000 : ℝ) ^ (65/16 : ℝ) ≤ (226384145437941/4000000000000000000 : ℝ) := by
    have hpowers : (4503/50000 : ℝ)^65 ≤ (226384145437941/4000000000000000000 : ℝ)^16 := by
      have hnat : (4503 : ℕ)^65*4000000000000000000^16 ≤ 226384145437941^16*50000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4503 50000 226384145437941 4000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4503/50000 : ℝ)) (X := (226384145437941/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hpowhi : (3309/20000 : ℝ) ^ (65/16 : ℝ) ≤ (16740705941396767/25000000000000000000 : ℝ) := by
    have hpowers : (3309/20000 : ℝ)^65 ≤ (16740705941396767/25000000000000000000 : ℝ)^16 := by
      have hnat : (3309 : ℕ)^65*25000000000000000000^16 ≤ 16740705941396767^16*20000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3309 20000 16740705941396767 25000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3309/20000 : ℝ)) (X := (16740705941396767/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000226384145437941/2000000000000000000 : ℝ) ≤ (10000278614753803/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (2000226384145437941/2000000000000000000 : ℝ)^16 ≤ (10000278614753803/10000000000000000 : ℝ)^65 := by
      have hnat : (2000226384145437941 : ℕ)^16*10000000000000000^65 ≤ 10000278614753803^65*2000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000226384145437941 2000000000000000000 10000278614753803 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000278614753803/10000000000000000 : ℝ)) (X := (2000226384145437941/2000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hcorner10 : (100072622427401535593/100000000000000000000 : ℝ) ≤ (156277924060327/156250000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (100072622427401535593/100000000000000000000 : ℝ)^16 ≤ (156277924060327/156250000000000 : ℝ)^65 := by
      have hnat : (100072622427401535593 : ℕ)^16*156250000000000^65 ≤ 156277924060327^65*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100072622427401535593 100000000000000000000 156277924060327 156250000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156277924060327/156250000000000 : ℝ)) (X := (100072622427401535593/100000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hcorner11 : (12516740705941396767/12500000000000000000 : ℝ) ≤ (10003295664968053/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (12516740705941396767/12500000000000000000 : ℝ)^16 ≤ (10003295664968053/10000000000000000 : ℝ)^65 := by
      have hnat : (12516740705941396767 : ℕ)^16*10000000000000000^65 ≤ 10003295664968053^65*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12516740705941396767 12500000000000000000 10003295664968053 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003295664968053/10000000000000000 : ℝ)) (X := (12516740705941396767/12500000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(226384145437941/4000000000000000000 : ℝ) ≤ ((25121642974133128439/25130000000000000000 : ℝ)+2*(4022733619/2010400000000 : ℝ)*(4503/50000 : ℝ))^(65/16 : ℝ) := by
    rw [show (25121642974133128439/25130000000000000000 : ℝ)+2*(4022733619/2010400000000 : ℝ)*(4503/50000 : ℝ)=(10000278614753803/10000000000000000 : ℝ) by norm_num, show 1+2*(226384145437941/4000000000000000000 : ℝ)=(2000226384145437941/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16740705941396767/25000000000000000000 : ℝ)+(226384145437941/4000000000000000000 : ℝ) ≤ ((25121642974133128439/25130000000000000000 : ℝ)+(4022733619/2010400000000 : ℝ)*((3309/20000 : ℝ)+(4503/50000 : ℝ)))^(65/16 : ℝ) := by
    rw [show (25121642974133128439/25130000000000000000 : ℝ)+(4022733619/2010400000000 : ℝ)*((3309/20000 : ℝ)+(4503/50000 : ℝ))=(156277924060327/156250000000000 : ℝ) by norm_num, show 1+(16740705941396767/25000000000000000000 : ℝ)+(226384145437941/4000000000000000000 : ℝ)=(100072622427401535593/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16740705941396767/25000000000000000000 : ℝ) ≤ ((25121642974133128439/25130000000000000000 : ℝ)+2*(4022733619/2010400000000 : ℝ)*(3309/20000 : ℝ))^(65/16 : ℝ) := by
    rw [show (25121642974133128439/25130000000000000000 : ℝ)+2*(4022733619/2010400000000 : ℝ)*(3309/20000 : ℝ)=(10003295664968053/10000000000000000 : ℝ) by norm_num, show 1+2*(16740705941396767/25000000000000000000 : ℝ)=(12516740705941396767/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (25121642974133128439/25130000000000000000 : ℝ)*(X 1 0+X 2 0)+(4022733619/2010400000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (65/16 : ℝ)) (lo := (4503/50000 : ℝ)) (hi := (3309/20000 : ℝ)) (c := (25121642974133128439/25130000000000000000 : ℝ)) (alpha := (4022733619/2010400000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (25121642974133128439/25130000000000000000 : ℝ)*(X 0 1+X 2 1)+(4022733619/2010400000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (65/16 : ℝ)) (lo := (4503/50000 : ℝ)) (hi := (3309/20000 : ℝ)) (c := (25121642974133128439/25130000000000000000 : ℝ)) (alpha := (4022733619/2010400000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (25121642974133128439/25130000000000000000 : ℝ)*(X 0 2+X 1 2)+(4022733619/2010400000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (65/16 : ℝ)) (lo := (4503/50000 : ℝ)) (hi := (3309/20000 : ℝ)) (c := (25121642974133128439/25130000000000000000 : ℝ)) (alpha := (4022733619/2010400000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1084819337/5000000000 : ℝ)*X 0 0+(5430648441/10000000000 : ℝ)*X 0 1+(5230740159/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677067837/5000000000 : ℝ)*X 1 0+(-1135928467/5000000000 : ℝ)*X 1 1+(2615370029/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354135769/10000000000 : ℝ)*X 2 0+(5230740159/10000000000 : ℝ)*X 2 1+(-2271856677/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4364299367/10000000000 : ℝ)*X 0 0+(521310133/1250000000 : ℝ)*X 0 1+(4567101123/10000000000 : ℝ)*X 0 2+(4364299367/10000000000 : ℝ)*X 1 0+(521310133/1250000000 : ℝ)*X 1 1+(4567101123/10000000000 : ℝ)*X 1 2+(4364299367/10000000000 : ℝ)*X 2 0+(521310133/1250000000 : ℝ)*X 2 1+(4567101123/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-542414361/2500000000 : ℝ)*X 0 0+(653940399/1250000000 : ℝ)*X 0 1+(1357465247/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((530354167/1000000000 : ℝ)*X 1 0+(-1036368433/5000000000 : ℝ)*X 1 1+(2714930241/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((212141713/400000000 : ℝ)*X 2 0+(2714929879/5000000000 : ℝ)*X 2 1+(-2072736287/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((436433633/1000000000 : ℝ)*X 0 0+(182621899/400000000 : ℝ)*X 0 1+(4172043783/10000000000 : ℝ)*X 0 2+(436433633/1000000000 : ℝ)*X 1 0+(182621899/400000000 : ℝ)*X 1 1+(4172043783/10000000000 : ℝ)*X 1 2+(436433633/1000000000 : ℝ)*X 2 0+(182621899/400000000 : ℝ)*X 2 1+(4172043783/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (815735207482222663809/251300000000000000000000000 : ℝ) := by norm_num
    linear_combination (1065188851/100000000000000 : ℝ)*(base19) + (1012065781/100000000000000 : ℝ)*(base23) + (15312893/20000000000000 : ℝ)*(lower2) + (4309371/2500000000000 : ℝ)*(upper5) + (1880913447650537/50000000000000 : ℝ)*(major0) + (1880913447650537/50000000000000 : ℝ)*(major1) + (1880913447650537/50000000000000 : ℝ)*(major2) + (62528867924343/1250000000000 : ℝ)*(sp0) + (1250582836097631/25000000000000 : ℝ)*(sp1) + (2501165758003261/50000000000000 : ℝ)*(sp2) + (78791050249087/3125000000000 : ℝ)*(sp3) + (11547062431/50000000000000 : ℝ)*(sp4) + (118492927/100000000000000 : ℝ)*(sp5) + (1886589253/25000000000000 : ℝ)*(sp7) + (630330288581949/25000000000000 : ℝ)*(f.failure) + (5002332528072303/100000000000000 : ℝ)*(f.sum) + (167080199421/50260000000000000000000000 : ℝ)*base66 + (1731908103515821743/1256500000000000000000000000000000 : ℝ)*base67 + (1281510622359821743/1256500000000000000000000000000000 : ℝ)*base69 + (779303266044821743/1256500000000000000000000000000000 : ℝ)*base71 + (842449295479/157062500000000000000000000 : ℝ)*base74 + (7160026529975178257/1256500000000000000000000000000000 : ℝ)*base76 + (5750430890943178257/1256500000000000000000000000000000 : ℝ)*base78 + (3196809210935178257/1256500000000000000000000000000000 : ℝ)*base80 + (1295926098127/628250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (996011/156250000000000000000 : ℝ)*base89 + (996011/156250000000000000000 : ℝ)*base91 + (996011/156250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16973558394861754636131/2513000000000000000000000000 : ℝ) := by norm_num
    linear_combination (666459601/50000000000000 : ℝ)*(base19) + (2638846331/100000000000000 : ℝ)*(base23) + (12392293/100000000000000 : ℝ)*(upper3) + (6400227/20000000000000 : ℝ)*(lower4) + (111328139/50000000000000 : ℝ)*(upper5) + (1895797843364529/50000000000000 : ℝ)*(major0) + (1895797843364529/50000000000000 : ℝ)*(major1) + (1895797843364529/50000000000000 : ℝ)*(major2) + (1072370339/6250000000000 : ℝ)*(sp1) + (32627153187/100000000000000 : ℝ)*(sp2) + (100838356087161/2000000000000 : ℝ)*(sp4) + (315118707094589/6250000000000 : ℝ)*(sp5) + (1260470634589633/25000000000000 : ℝ)*(sp6) + (2541273343956697/100000000000000 : ℝ)*(sp7) + (2541273343956697/100000000000000 : ℝ)*(f.failure) + (100838356087161/2000000000000 : ℝ)*(f.sum) + (121795224301/125650000000000000000000000 : ℝ)*base65 + (607230712746259769/1256500000000000000000000000000000 : ℝ)*base68 + (2316980931159740231/1256500000000000000000000000000000 : ℝ)*base69 + (1345156442262240231/1256500000000000000000000000000000 : ℝ)*base71 + (20939496253/100520000000000000000000000 : ℝ)*base74 + (8638694336019740231/1256500000000000000000000000000000 : ℝ)*base75 + (6277808977993259769/1256500000000000000000000000000000 : ℝ)*base78 + (8299016575524759769/1256500000000000000000000000000000 : ℝ)*base80 + (690528002233/1256500000000000000000000000 : ℝ)*base81 + (1336183/625000000000000000000 : ℝ)*base89 + (1336183/625000000000000000000 : ℝ)*base91 + (1336183/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1128_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9325039/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3309/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4503/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10593/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14823/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1128_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1128_s4_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2172754559/10000000000 : ℝ)*x 0 + (675321979/1250000000 : ℝ)*x 1 + (5256775129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2172754559/10000000000 : ℝ)^8321 ≤ (13199542198879/100000000000000 : ℝ)^6273 := by
    have hnat : (2172754559 : ℕ)^8321*100000000000000^6273 ≤ 13199542198879^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172754559 10000000000 13199542198879 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (675321979/1250000000 : ℝ)^8321 ≤ (86303980841/195312500000 : ℝ)^6273 := by
    have hnat : (675321979 : ℕ)^8321*195312500000^6273 ≤ 86303980841^6273*1250000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675321979 1250000000 86303980841 195312500000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5256775129/10000000000 : ℝ)^8321 ≤ (1065320489863/2500000000000 : ℝ)^6273 := by
    have hnat : (5256775129 : ℕ)^8321*2500000000000^6273 ≤ 1065320489863^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256775129 10000000000 1065320489863 2500000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2172754559/10000000000 : ℝ), (675321979/1250000000 : ℝ), (5256775129/10000000000 : ℝ)] ![(13199542198879/100000000000000 : ℝ), (86303980841/195312500000 : ℝ), (1065320489863/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2172754559/10000000000 : ℝ)|^8321 ≤ (13199542198879/100000000000000 : ℝ)^6273
        have hw : |(-2172754559/10000000000 : ℝ)|=(2172754559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(675321979/1250000000 : ℝ)|^8321 ≤ (86303980841/195312500000 : ℝ)^6273
        have hw : |(675321979/1250000000 : ℝ)|=(675321979/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5256775129/10000000000 : ℝ)|^8321 ≤ (1065320489863/2500000000000 : ℝ)^6273
        have hw : |(5256775129/10000000000 : ℝ)|=(5256775129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s4_1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2673567651/5000000000 : ℝ)*x 0 + (-2246860841/10000000000 : ℝ)*x 1 + (1314193819/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673567651/5000000000 : ℝ)^8321 ≤ (681049364479/1562500000000 : ℝ)^6273 := by
    have hnat : (2673567651 : ℕ)^8321*1562500000000^6273 ≤ 681049364479^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673567651 5000000000 681049364479 1562500000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2246860841/10000000000 : ℝ)^8321 ≤ (6900009739793/50000000000000 : ℝ)^6273 := by
    have hnat : (2246860841 : ℕ)^8321*50000000000000^6273 ≤ 6900009739793^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246860841 10000000000 6900009739793 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1314193819/2500000000 : ℝ)^8321 ≤ (2130641058759/5000000000000 : ℝ)^6273 := by
    have hnat : (1314193819 : ℕ)^8321*5000000000000^6273 ≤ 2130641058759^6273*2500000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314193819 2500000000 2130641058759 5000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673567651/5000000000 : ℝ), (-2246860841/10000000000 : ℝ), (1314193819/2500000000 : ℝ)] ![(681049364479/1562500000000 : ℝ), (6900009739793/50000000000000 : ℝ), (2130641058759/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673567651/5000000000 : ℝ)|^8321 ≤ (681049364479/1562500000000 : ℝ)^6273
        have hw : |(2673567651/5000000000 : ℝ)|=(2673567651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2246860841/10000000000 : ℝ)|^8321 ≤ (6900009739793/50000000000000 : ℝ)^6273
        have hw : |(-2246860841/10000000000 : ℝ)|=(2246860841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1314193819/2500000000 : ℝ)|^8321 ≤ (2130641058759/5000000000000 : ℝ)^6273
        have hw : |(1314193819/2500000000 : ℝ)|=(1314193819/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s4_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2673567933/5000000000 : ℝ)*x 0 + (2628387311/5000000000 : ℝ)*x 1 + (-561715239/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673567933/5000000000 : ℝ)^8321 ≤ (43587165425067/100000000000000 : ℝ)^6273 := by
    have hnat : (2673567933 : ℕ)^8321*100000000000000^6273 ≤ 43587165425067^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673567933 5000000000 43587165425067 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2628387311/5000000000 : ℝ)^8321 ≤ (42612814142857/100000000000000 : ℝ)^6273 := by
    have hnat : (2628387311 : ℕ)^8321*100000000000000^6273 ≤ 42612814142857^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628387311 5000000000 42612814142857 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (561715239/2500000000 : ℝ)^8321 ≤ (1725002552063/12500000000000 : ℝ)^6273 := by
    have hnat : (561715239 : ℕ)^8321*12500000000000^6273 ≤ 1725002552063^6273*2500000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561715239 2500000000 1725002552063 12500000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673567933/5000000000 : ℝ), (2628387311/5000000000 : ℝ), (-561715239/2500000000 : ℝ)] ![(43587165425067/100000000000000 : ℝ), (42612814142857/100000000000000 : ℝ), (1725002552063/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673567933/5000000000 : ℝ)|^8321 ≤ (43587165425067/100000000000000 : ℝ)^6273
        have hw : |(2673567933/5000000000 : ℝ)|=(2673567933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2628387311/5000000000 : ℝ)|^8321 ≤ (42612814142857/100000000000000 : ℝ)^6273
        have hw : |(2628387311/5000000000 : ℝ)|=(2628387311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-561715239/2500000000 : ℝ)|^8321 ≤ (1725002552063/12500000000000 : ℝ)^6273
        have hw : |(-561715239/2500000000 : ℝ)|=(561715239/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s4_3 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (545769879/1250000000 : ℝ)*x 0 + (844782717/2000000000 : ℝ)*x 1 + (4513185353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545769879/1250000000 : ℝ)^8321 ≤ (6662385615173/20000000000000 : ℝ)^6273 := by
    have hnat : (545769879 : ℕ)^8321*20000000000000^6273 ≤ 6662385615173^6273*1250000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545769879 1250000000 6662385615173 20000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (844782717/2000000000 : ℝ)^8321 ≤ (15940025416383/50000000000000 : ℝ)^6273 := by
    have hnat : (844782717 : ℕ)^8321*50000000000000^6273 ≤ 15940025416383^6273*2000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844782717 2000000000 15940025416383 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4513185353/10000000000 : ℝ)^8321 ≤ (34808021079759/100000000000000 : ℝ)^6273 := by
    have hnat : (4513185353 : ℕ)^8321*100000000000000^6273 ≤ 34808021079759^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4513185353 10000000000 34808021079759 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(545769879/1250000000 : ℝ), (844782717/2000000000 : ℝ), (4513185353/10000000000 : ℝ)] ![(6662385615173/20000000000000 : ℝ), (15940025416383/50000000000000 : ℝ), (34808021079759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(545769879/1250000000 : ℝ)|^8321 ≤ (6662385615173/20000000000000 : ℝ)^6273
        have hw : |(545769879/1250000000 : ℝ)|=(545769879/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(844782717/2000000000 : ℝ)|^8321 ≤ (15940025416383/50000000000000 : ℝ)^6273
        have hw : |(844782717/2000000000 : ℝ)|=(844782717/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4513185353/10000000000 : ℝ)|^8321 ≤ (34808021079759/100000000000000 : ℝ)^6273
        have hw : |(4513185353/10000000000 : ℝ)|=(4513185353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s4_4 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2172762301/10000000000 : ℝ)*x 0 + (5257192199/10000000000 : ℝ)*x 1 + (5402156709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2172762301/10000000000 : ℝ)^8321 ≤ (13199604586993/100000000000000 : ℝ)^6273 := by
    have hnat : (2172762301 : ℕ)^8321*100000000000000^6273 ≤ 13199604586993^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172762301 10000000000 13199604586993 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5257192199/10000000000 : ℝ)^8321 ≤ (42617304318131/100000000000000 : ℝ)^6273 := by
    have hnat : (5257192199 : ℕ)^8321*100000000000000^6273 ≤ 42617304318131^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257192199 10000000000 42617304318131 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5402156709/10000000000 : ℝ)^8321 ≤ (44183091073409/100000000000000 : ℝ)^6273 := by
    have hnat : (5402156709 : ℕ)^8321*100000000000000^6273 ≤ 44183091073409^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402156709 10000000000 44183091073409 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2172762301/10000000000 : ℝ), (5257192199/10000000000 : ℝ), (5402156709/10000000000 : ℝ)] ![(13199604586993/100000000000000 : ℝ), (42617304318131/100000000000000 : ℝ), (44183091073409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2172762301/10000000000 : ℝ)|^8321 ≤ (13199604586993/100000000000000 : ℝ)^6273
        have hw : |(-2172762301/10000000000 : ℝ)|=(2172762301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5257192199/10000000000 : ℝ)|^8321 ≤ (42617304318131/100000000000000 : ℝ)^6273
        have hw : |(5257192199/10000000000 : ℝ)|=(5257192199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5402156709/10000000000 : ℝ)|^8321 ≤ (44183091073409/100000000000000 : ℝ)^6273
        have hw : |(5402156709/10000000000 : ℝ)|=(5402156709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s4_5 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (132755927/250000000 : ℝ)*x 0 + (-2101478689/10000000000 : ℝ)*x 1 + (5402156721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132755927/250000000 : ℝ)^8321 ≤ (1349644901519/3125000000000 : ℝ)^6273 := by
    have hnat : (132755927 : ℕ)^8321*3125000000000^6273 ≤ 1349644901519^6273*250000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132755927 250000000 1349644901519 3125000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2101478689/10000000000 : ℝ)^8321 ≤ (12628271934111/100000000000000 : ℝ)^6273 := by
    have hnat : (2101478689 : ℕ)^8321*100000000000000^6273 ≤ 12628271934111^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101478689 10000000000 12628271934111 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5402156721/10000000000 : ℝ)^8321 ≤ (44183091203597/100000000000000 : ℝ)^6273 := by
    have hnat : (5402156721 : ℕ)^8321*100000000000000^6273 ≤ 44183091203597^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402156721 10000000000 44183091203597 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132755927/250000000 : ℝ), (-2101478689/10000000000 : ℝ), (5402156721/10000000000 : ℝ)] ![(1349644901519/3125000000000 : ℝ), (12628271934111/100000000000000 : ℝ), (44183091203597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132755927/250000000 : ℝ)|^8321 ≤ (1349644901519/3125000000000 : ℝ)^6273
        have hw : |(132755927/250000000 : ℝ)|=(132755927/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2101478689/10000000000 : ℝ)|^8321 ≤ (12628271934111/100000000000000 : ℝ)^6273
        have hw : |(-2101478689/10000000000 : ℝ)|=(2101478689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5402156721/10000000000 : ℝ)|^8321 ≤ (44183091203597/100000000000000 : ℝ)^6273
        have hw : |(5402156721/10000000000 : ℝ)|=(5402156721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s4_6 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062047421/2000000000 : ℝ)*x 0 + (5402156673/10000000000 : ℝ)*x 1 + (-6567121/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062047421/2000000000 : ℝ)^8321 ≤ (21594318559159/50000000000000 : ℝ)^6273 := by
    have hnat : (1062047421 : ℕ)^8321*50000000000000^6273 ≤ 21594318559159^6273*2000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062047421 2000000000 21594318559159 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5402156673/10000000000 : ℝ)^8321 ≤ (22091545341423/50000000000000 : ℝ)^6273 := by
    have hnat : (5402156673 : ℕ)^8321*50000000000000^6273 ≤ 22091545341423^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402156673 10000000000 22091545341423 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6567121/31250000 : ℝ)^8321 ≤ (394633505663/3125000000000 : ℝ)^6273 := by
    have hnat : (6567121 : ℕ)^8321*3125000000000^6273 ≤ 394633505663^6273*31250000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6567121 31250000 394633505663 3125000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062047421/2000000000 : ℝ), (5402156673/10000000000 : ℝ), (-6567121/31250000 : ℝ)] ![(21594318559159/50000000000000 : ℝ), (22091545341423/50000000000000 : ℝ), (394633505663/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062047421/2000000000 : ℝ)|^8321 ≤ (21594318559159/50000000000000 : ℝ)^6273
        have hw : |(1062047421/2000000000 : ℝ)|=(1062047421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5402156673/10000000000 : ℝ)|^8321 ≤ (22091545341423/50000000000000 : ℝ)^6273
        have hw : |(5402156673/10000000000 : ℝ)|=(5402156673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6567121/31250000 : ℝ)|^8321 ≤ (394633505663/3125000000000 : ℝ)^6273
        have hw : |(-6567121/31250000 : ℝ)|=(6567121/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s4_7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4366173139/10000000000 : ℝ)*x 0 + (4512357043/10000000000 : ℝ)*x 1 + (422474569/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4366173139/10000000000 : ℝ)^8321 ≤ (4164008855667/12500000000000 : ℝ)^6273 := by
    have hnat : (4366173139 : ℕ)^8321*12500000000000^6273 ≤ 4164008855667^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4366173139 10000000000 4164008855667 12500000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4512357043/10000000000 : ℝ)^8321 ≤ (17399773658603/50000000000000 : ℝ)^6273 := by
    have hnat : (4512357043 : ℕ)^8321*50000000000000^6273 ≤ 17399773658603^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4512357043 10000000000 17399773658603 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (422474569/1000000000 : ℝ)^8321 ≤ (31888381816987/100000000000000 : ℝ)^6273 := by
    have hnat : (422474569 : ℕ)^8321*100000000000000^6273 ≤ 31888381816987^6273*1000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422474569 1000000000 31888381816987 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4366173139/10000000000 : ℝ), (4512357043/10000000000 : ℝ), (422474569/1000000000 : ℝ)] ![(4164008855667/12500000000000 : ℝ), (17399773658603/50000000000000 : ℝ), (31888381816987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4366173139/10000000000 : ℝ)|^8321 ≤ (4164008855667/12500000000000 : ℝ)^6273
        have hw : |(4366173139/10000000000 : ℝ)|=(4366173139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4512357043/10000000000 : ℝ)|^8321 ≤ (17399773658603/50000000000000 : ℝ)^6273
        have hw : |(4512357043/10000000000 : ℝ)|=(4512357043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(422474569/1000000000 : ℝ)|^8321 ≤ (31888381816987/100000000000000 : ℝ)^6273
        have hw : |(422474569/1000000000 : ℝ)|=(422474569/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1128_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9325039/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14823/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10593/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2787/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3559/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14823/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10593/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14823/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10593/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14823/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10593/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14823/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10593/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14823/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10593/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14823/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10593/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10593/100000 : ℝ) ^ (65/16 : ℝ) ≤ (10943080018415401/100000000000000000000 : ℝ) := by
    have hpowers : (10593/100000 : ℝ)^65 ≤ (10943080018415401/100000000000000000000 : ℝ)^16 := by
      have hnat : (10593 : ℕ)^65*100000000000000000000^16 ≤ 10943080018415401^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10593 100000 10943080018415401 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10593/100000 : ℝ)) (X := (10943080018415401/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hpowhi : (14823/100000 : ℝ) ^ (65/16 : ℝ) ≤ (42847742089879019/100000000000000000000 : ℝ) := by
    have hpowers : (14823/100000 : ℝ)^65 ≤ (42847742089879019/100000000000000000000 : ℝ)^16 := by
      have hnat : (14823 : ℕ)^65*100000000000000000000^16 ≤ 42847742089879019^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14823 100000 42847742089879019 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14823/100000 : ℝ)) (X := (42847742089879019/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010943080018415401/50000000000000000000 : ℝ) ≤ (2000107738362049/2000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (50010943080018415401/50000000000000000000 : ℝ)^16 ≤ (2000107738362049/2000000000000000 : ℝ)^65 := by
      have hnat : (50010943080018415401 : ℕ)^16*2000000000000000^65 ≤ 2000107738362049^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010943080018415401 50000000000000000000 2000107738362049 2000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000107738362049/2000000000000000 : ℝ)) (X := (50010943080018415401/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hcorner10 : (5002689541105414721/5000000000000000000 : ℝ) ≤ (2500330953350439/2500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (5002689541105414721/5000000000000000000 : ℝ)^16 ≤ (2500330953350439/2500000000000000 : ℝ)^65 := by
      have hnat : (5002689541105414721 : ℕ)^16*2500000000000000^65 ≤ 2500330953350439^65*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002689541105414721 5000000000000000000 2500330953350439 2500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500330953350439/2500000000000000 : ℝ)) (X := (5002689541105414721/5000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hcorner11 : (50042847742089879019/50000000000000000000 : ℝ) ≤ (10002108934993267/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (50042847742089879019/50000000000000000000 : ℝ)^16 ≤ (10002108934993267/10000000000000000 : ℝ)^65 := by
      have hnat : (50042847742089879019 : ℕ)^16*10000000000000000^65 ≤ 10002108934993267^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50042847742089879019 50000000000000000000 10002108934993267 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002108934993267/10000000000000000 : ℝ)) (X := (50042847742089879019/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10943080018415401/100000000000000000000 : ℝ) ≤ ((6247879001229253/6250000000000000 : ℝ)+2*(16704714713/9000000000000 : ℝ)*(10593/100000 : ℝ))^(65/16 : ℝ) := by
    rw [show (6247879001229253/6250000000000000 : ℝ)+2*(16704714713/9000000000000 : ℝ)*(10593/100000 : ℝ)=(2000107738362049/2000000000000000 : ℝ) by norm_num, show 1+2*(10943080018415401/100000000000000000000 : ℝ)=(50010943080018415401/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(42847742089879019/100000000000000000000 : ℝ)+(10943080018415401/100000000000000000000 : ℝ) ≤ ((6247879001229253/6250000000000000 : ℝ)+(16704714713/9000000000000 : ℝ)*((14823/100000 : ℝ)+(10593/100000 : ℝ)))^(65/16 : ℝ) := by
    rw [show (6247879001229253/6250000000000000 : ℝ)+(16704714713/9000000000000 : ℝ)*((14823/100000 : ℝ)+(10593/100000 : ℝ))=(2500330953350439/2500000000000000 : ℝ) by norm_num, show 1+(42847742089879019/100000000000000000000 : ℝ)+(10943080018415401/100000000000000000000 : ℝ)=(5002689541105414721/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(42847742089879019/100000000000000000000 : ℝ) ≤ ((6247879001229253/6250000000000000 : ℝ)+2*(16704714713/9000000000000 : ℝ)*(14823/100000 : ℝ))^(65/16 : ℝ) := by
    rw [show (6247879001229253/6250000000000000 : ℝ)+2*(16704714713/9000000000000 : ℝ)*(14823/100000 : ℝ)=(10002108934993267/10000000000000000 : ℝ) by norm_num, show 1+2*(42847742089879019/100000000000000000000 : ℝ)=(50042847742089879019/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6247879001229253/6250000000000000 : ℝ)*(X 1 0+X 2 0)+(16704714713/9000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (65/16 : ℝ)) (lo := (10593/100000 : ℝ)) (hi := (14823/100000 : ℝ)) (c := (6247879001229253/6250000000000000 : ℝ)) (alpha := (16704714713/9000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6247879001229253/6250000000000000 : ℝ)*(X 0 1+X 2 1)+(16704714713/9000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (65/16 : ℝ)) (lo := (10593/100000 : ℝ)) (hi := (14823/100000 : ℝ)) (c := (6247879001229253/6250000000000000 : ℝ)) (alpha := (16704714713/9000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6247879001229253/6250000000000000 : ℝ)*(X 0 2+X 1 2)+(16704714713/9000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (65/16 : ℝ)) (lo := (10593/100000 : ℝ)) (hi := (14823/100000 : ℝ)) (c := (6247879001229253/6250000000000000 : ℝ)) (alpha := (16704714713/9000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2172754559/10000000000 : ℝ)*X 0 0+(675321979/1250000000 : ℝ)*X 0 1+(5256775129/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673567651/5000000000 : ℝ)*X 1 0+(-2246860841/10000000000 : ℝ)*X 1 1+(1314193819/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673567933/5000000000 : ℝ)*X 2 0+(2628387311/5000000000 : ℝ)*X 2 1+(-561715239/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((545769879/1250000000 : ℝ)*X 0 0+(844782717/2000000000 : ℝ)*X 0 1+(4513185353/10000000000 : ℝ)*X 0 2+(545769879/1250000000 : ℝ)*X 1 0+(844782717/2000000000 : ℝ)*X 1 1+(4513185353/10000000000 : ℝ)*X 1 2+(545769879/1250000000 : ℝ)*X 2 0+(844782717/2000000000 : ℝ)*X 2 1+(4513185353/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2172762301/10000000000 : ℝ)*X 0 0+(5257192199/10000000000 : ℝ)*X 0 1+(5402156709/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((132755927/250000000 : ℝ)*X 1 0+(-2101478689/10000000000 : ℝ)*X 1 1+(5402156721/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062047421/2000000000 : ℝ)*X 2 0+(5402156673/10000000000 : ℝ)*X 2 1+(-6567121/31250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4366173139/10000000000 : ℝ)*X 0 0+(4512357043/10000000000 : ℝ)*X 0 1+(422474569/1000000000 : ℝ)*X 0 2+(4366173139/10000000000 : ℝ)*X 1 0+(4512357043/10000000000 : ℝ)*X 1 1+(422474569/1000000000 : ℝ)*X 1 2+(4366173139/10000000000 : ℝ)*X 2 0+(4512357043/10000000000 : ℝ)*X 2 1+(422474569/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1115387991718970200666501/78125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (438395783/50000000000000 : ℝ)*(base19) + (565573589/50000000000000 : ℝ)*(base23) + (194834039/50000000000000 : ℝ)*(lower2) + (47411197/12500000000000 : ℝ)*(upper3) + (27768971/20000000000000 : ℝ)*(lower4) + (5157842408369903/100000000000000 : ℝ)*(major0) + (5157842408369903/100000000000000 : ℝ)*(major1) + (5157842408369903/100000000000000 : ℝ)*(major2) + (6858690413742367/100000000000000 : ℝ)*(sp0) + (857337373623899/12500000000000 : ℝ)*(sp1) + (342934936731779/5000000000000 : ℝ)*(sp2) + (1728482195030637/50000000000000 : ℝ)*(sp3) + (9452040391/100000000000000 : ℝ)*(sp4) + (20084996889/100000000000000 : ℝ)*(sp7) + (3456984475058163/100000000000000 : ℝ)*(f.failure) + (3429349932891379/50000000000000 : ℝ)*(f.sum) + (2738350239911/450000000000000000000000000 : ℝ)*base66 + (77470830645654119/5625000000000000000000000000000 : ℝ)*base68 + (79187417655654119/5625000000000000000000000000000 : ℝ)*base70 + (54850009318779119/5625000000000000000000000000000 : ℝ)*base72 + (577950162589/450000000000000000000000000 : ℝ)*base73 + (9710485699404119/5625000000000000000000000000000 : ℝ)*base76 + (34320571516220881/5625000000000000000000000000000 : ℝ)*base77 + (125482830310029119/5625000000000000000000000000000 : ℝ)*base80 + (2086288160561/450000000000000000000000000 : ℝ)*base82 + (3493357/625000000000000000000 : ℝ)*base89 + (3493357/625000000000000000000 : ℝ)*base91 + (3493357/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (291379487481402869723489/39062500000000000000000000000 : ℝ) := by norm_num
    linear_combination (332881287/25000000000000 : ℝ)*(base19) + (363143089/25000000000000 : ℝ)*(base23) + (31650271/25000000000000 : ℝ)*(upper3) + (22915197/50000000000000 : ℝ)*(lower4) + (141012627/100000000000000 : ℝ)*(upper5) + (5187576913354741/100000000000000 : ℝ)*(major0) + (5187576913354741/100000000000000 : ℝ)*(major1) + (5187576913354741/100000000000000 : ℝ)*(major2) + (16986046583/50000000000000 : ℝ)*(sp1) + (8574402427/25000000000000 : ℝ)*(sp2) + (1724559973368061/25000000000000 : ℝ)*(sp4) + (689820458985393/10000000000000 : ℝ)*(sp5) + (6898204143290181/100000000000000 : ℝ)*(sp6) + (3476913684593397/100000000000000 : ℝ)*(sp7) + (3476913684593397/100000000000000 : ℝ)*(f.failure) + (1724559973368061/25000000000000 : ℝ)*(f.sum) + (1903880621783/450000000000000000000000000 : ℝ)*base65 + (67002726624152507/5625000000000000000000000000000 : ℝ)*base67 + (10419027442277507/5625000000000000000000000000000 : ℝ)*base69 + (73592053629152507/5625000000000000000000000000000 : ℝ)*base71 + (26415391583/450000000000000000000000000 : ℝ)*base73 + (26589539223527507/5625000000000000000000000000000 : ℝ)*base75 + (62208838998527507/5625000000000000000000000000000 : ℝ)*base77 + (76771900061472493/5625000000000000000000000000000 : ℝ)*base80 + (2517328888567/450000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (5082517/625000000000000000000 : ℝ)*base90 + (5082517/625000000000000000000 : ℝ)*base92 + (5082517/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1128_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9325039/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14823/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10593/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2787/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1128_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1128_s5_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2173426453/10000000000 : ℝ)*x 0 + (2697643383/5000000000 : ℝ)*x 1 + (5263622957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173426453/10000000000 : ℝ)^8321 ≤ (6602478428977/50000000000000 : ℝ)^6273 := by
    have hnat : (2173426453 : ℕ)^8321*50000000000000^6273 ≤ 6602478428977^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173426453 10000000000 6602478428977 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697643383/5000000000 : ℝ)^8321 ≤ (8821714926807/20000000000000 : ℝ)^6273 := by
    have hnat : (2697643383 : ℕ)^8321*20000000000000^6273 ≤ 8821714926807^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697643383 5000000000 8821714926807 20000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263622957/10000000000 : ℝ)^8321 ≤ (8537293698889/20000000000000 : ℝ)^6273 := by
    have hnat : (5263622957 : ℕ)^8321*20000000000000^6273 ≤ 8537293698889^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263622957 10000000000 8537293698889 20000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2173426453/10000000000 : ℝ), (2697643383/5000000000 : ℝ), (5263622957/10000000000 : ℝ)] ![(6602478428977/50000000000000 : ℝ), (8821714926807/20000000000000 : ℝ), (8537293698889/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2173426453/10000000000 : ℝ)|^8321 ≤ (6602478428977/50000000000000 : ℝ)^6273
        have hw : |(-2173426453/10000000000 : ℝ)|=(2173426453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697643383/5000000000 : ℝ)|^8321 ≤ (8821714926807/20000000000000 : ℝ)^6273
        have hw : |(2697643383/5000000000 : ℝ)|=(2697643383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263622957/10000000000 : ℝ)|^8321 ≤ (8537293698889/20000000000000 : ℝ)^6273
        have hw : |(5263622957/10000000000 : ℝ)|=(5263622957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s5_1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (267265479/500000000 : ℝ)*x 0 + (-1120120551/5000000000 : ℝ)*x 1 + (5263622821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267265479/500000000 : ℝ)^8321 ≤ (10891854821221/25000000000000 : ℝ)^6273 := by
    have hnat : (267265479 : ℕ)^8321*25000000000000^6273 ≤ 10891854821221^6273*500000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267265479 500000000 10891854821221 25000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1120120551/5000000000 : ℝ)^8321 ≤ (6873056835319/50000000000000 : ℝ)^6273 := by
    have hnat : (1120120551 : ℕ)^8321*50000000000000^6273 ≤ 6873056835319^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120120551 5000000000 6873056835319 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263622821/10000000000 : ℝ)^8321 ≤ (10671616757861/25000000000000 : ℝ)^6273 := by
    have hnat : (5263622821 : ℕ)^8321*25000000000000^6273 ≤ 10671616757861^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263622821 10000000000 10671616757861 25000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267265479/500000000 : ℝ), (-1120120551/5000000000 : ℝ), (5263622821/10000000000 : ℝ)] ![(10891854821221/25000000000000 : ℝ), (6873056835319/50000000000000 : ℝ), (10671616757861/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267265479/500000000 : ℝ)|^8321 ≤ (10891854821221/25000000000000 : ℝ)^6273
        have hw : |(267265479/500000000 : ℝ)|=(267265479/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1120120551/5000000000 : ℝ)|^8321 ≤ (6873056835319/50000000000000 : ℝ)^6273
        have hw : |(-1120120551/5000000000 : ℝ)|=(1120120551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263622821/10000000000 : ℝ)|^8321 ≤ (10671616757861/25000000000000 : ℝ)^6273
        have hw : |(5263622821/10000000000 : ℝ)|=(5263622821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s5_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345309317/10000000000 : ℝ)*x 0 + (1052724607/2000000000 : ℝ)*x 1 + (-2240241169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345309317/10000000000 : ℝ)^8321 ≤ (21783708220719/50000000000000 : ℝ)^6273 := by
    have hnat : (5345309317 : ℕ)^8321*50000000000000^6273 ≤ 21783708220719^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345309317 10000000000 21783708220719 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052724607/2000000000 : ℝ)^8321 ≤ (42686469333519/100000000000000 : ℝ)^6273 := by
    have hnat : (1052724607 : ℕ)^8321*100000000000000^6273 ≤ 42686469333519^6273*2000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052724607 2000000000 42686469333519 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2240241169/10000000000 : ℝ)^8321 ≤ (13746114215969/100000000000000 : ℝ)^6273 := by
    have hnat : (2240241169 : ℕ)^8321*100000000000000^6273 ≤ 13746114215969^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240241169 10000000000 13746114215969 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345309317/10000000000 : ℝ), (1052724607/2000000000 : ℝ), (-2240241169/10000000000 : ℝ)] ![(21783708220719/50000000000000 : ℝ), (42686469333519/100000000000000 : ℝ), (13746114215969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345309317/10000000000 : ℝ)|^8321 ≤ (21783708220719/50000000000000 : ℝ)^6273
        have hw : |(5345309317/10000000000 : ℝ)|=(5345309317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052724607/2000000000 : ℝ)|^8321 ≤ (42686469333519/100000000000000 : ℝ)^6273
        have hw : |(1052724607/2000000000 : ℝ)|=(1052724607/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2240241169/10000000000 : ℝ)|^8321 ≤ (13746114215969/100000000000000 : ℝ)^6273
        have hw : |(-2240241169/10000000000 : ℝ)|=(2240241169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s5_3 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (27290929/62500000 : ℝ)*x 0 + (847577527/2000000000 : ℝ)*x 1 + (1124777573/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (27290929/62500000 : ℝ)^8321 ≤ (33315871147309/100000000000000 : ℝ)^6273 := by
    have hnat : (27290929 : ℕ)^8321*100000000000000^6273 ≤ 33315871147309^6273*62500000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27290929 62500000 33315871147309 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (847577527/2000000000 : ℝ)^8321 ≤ (32020029163573/100000000000000 : ℝ)^6273 := by
    have hnat : (847577527 : ℕ)^8321*100000000000000^6273 ≤ 32020029163573^6273*2000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847577527 2000000000 32020029163573 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1124777573/2500000000 : ℝ)^8321 ≤ (17332049839291/50000000000000 : ℝ)^6273 := by
    have hnat : (1124777573 : ℕ)^8321*50000000000000^6273 ≤ 17332049839291^6273*2500000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124777573 2500000000 17332049839291 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(27290929/62500000 : ℝ), (847577527/2000000000 : ℝ), (1124777573/2500000000 : ℝ)] ![(33315871147309/100000000000000 : ℝ), (32020029163573/100000000000000 : ℝ), (17332049839291/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(27290929/62500000 : ℝ)|^8321 ≤ (33315871147309/100000000000000 : ℝ)^6273
        have hw : |(27290929/62500000 : ℝ)|=(27290929/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(847577527/2000000000 : ℝ)|^8321 ≤ (32020029163573/100000000000000 : ℝ)^6273
        have hw : |(847577527/2000000000 : ℝ)|=(847577527/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1124777573/2500000000 : ℝ)|^8321 ≤ (17332049839291/50000000000000 : ℝ)^6273
        have hw : |(1124777573/2500000000 : ℝ)|=(1124777573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s5_4 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-543357783/2500000000 : ℝ)*x 0 + (210558557/400000000 : ℝ)*x 1 + (5394945053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543357783/2500000000 : ℝ)^8321 ≤ (13204994566993/100000000000000 : ℝ)^6273 := by
    have hnat : (543357783 : ℕ)^8321*100000000000000^6273 ≤ 13204994566993^6273*2500000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543357783 2500000000 13204994566993 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210558557/400000000 : ℝ)^8321 ≤ (8538027289727/20000000000000 : ℝ)^6273 := by
    have hnat : (210558557 : ℕ)^8321*20000000000000^6273 ≤ 8538027289727^6273*400000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210558557 400000000 8538027289727 20000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394945053/10000000000 : ℝ)^8321 ≤ (44104868972611/100000000000000 : ℝ)^6273 := by
    have hnat : (5394945053 : ℕ)^8321*100000000000000^6273 ≤ 44104868972611^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394945053 10000000000 44104868972611 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-543357783/2500000000 : ℝ), (210558557/400000000 : ℝ), (5394945053/10000000000 : ℝ)] ![(13204994566993/100000000000000 : ℝ), (8538027289727/20000000000000 : ℝ), (44104868972611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-543357783/2500000000 : ℝ)|^8321 ≤ (13204994566993/100000000000000 : ℝ)^6273
        have hw : |(-543357783/2500000000 : ℝ)|=(543357783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210558557/400000000 : ℝ)|^8321 ≤ (8538027289727/20000000000000 : ℝ)^6273
        have hw : |(210558557/400000000 : ℝ)|=(210558557/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394945053/10000000000 : ℝ)|^8321 ≤ (44104868972611/100000000000000 : ℝ)^6273
        have hw : |(5394945053/10000000000 : ℝ)|=(5394945053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s5_5 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062397419/2000000000 : ℝ)*x 0 + (-105445953/500000000 : ℝ)*x 1 + (5394944969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062397419/2000000000 : ℝ)^8321 ≤ (43207517672983/100000000000000 : ℝ)^6273 := by
    have hnat : (1062397419 : ℕ)^8321*100000000000000^6273 ≤ 43207517672983^6273*2000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062397419 2000000000 43207517672983 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105445953/500000000 : ℝ)^8321 ≤ (12687614250147/100000000000000 : ℝ)^6273 := by
    have hnat : (105445953 : ℕ)^8321*100000000000000^6273 ≤ 12687614250147^6273*500000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105445953 500000000 12687614250147 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394944969/10000000000 : ℝ)^8321 ≤ (22052434030847/50000000000000 : ℝ)^6273 := by
    have hnat : (5394944969 : ℕ)^8321*50000000000000^6273 ≤ 22052434030847^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394944969 10000000000 22052434030847 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062397419/2000000000 : ℝ), (-105445953/500000000 : ℝ), (5394944969/10000000000 : ℝ)] ![(43207517672983/100000000000000 : ℝ), (12687614250147/100000000000000 : ℝ), (22052434030847/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062397419/2000000000 : ℝ)|^8321 ≤ (43207517672983/100000000000000 : ℝ)^6273
        have hw : |(1062397419/2000000000 : ℝ)|=(1062397419/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-105445953/500000000 : ℝ)|^8321 ≤ (12687614250147/100000000000000 : ℝ)^6273
        have hw : |(-105445953/500000000 : ℝ)|=(105445953/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394944969/10000000000 : ℝ)|^8321 ≤ (22052434030847/50000000000000 : ℝ)^6273
        have hw : |(5394944969/10000000000 : ℝ)|=(5394944969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s5_6 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (663998343/1250000000 : ℝ)*x 0 + (5394945231/10000000000 : ℝ)*x 1 + (-1054459589/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663998343/1250000000 : ℝ)^8321 ≤ (21603756942929/50000000000000 : ℝ)^6273 := by
    have hnat : (663998343 : ℕ)^8321*50000000000000^6273 ≤ 21603756942929^6273*1250000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663998343 1250000000 21603756942929 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394945231/10000000000 : ℝ)^8321 ≤ (44104870902889/100000000000000 : ℝ)^6273 := by
    have hnat : (5394945231 : ℕ)^8321*100000000000000^6273 ≤ 44104870902889^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394945231 10000000000 44104870902889 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054459589/5000000000 : ℝ)^8321 ≤ (507504607673/4000000000000 : ℝ)^6273 := by
    have hnat : (1054459589 : ℕ)^8321*4000000000000^6273 ≤ 507504607673^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054459589 5000000000 507504607673 4000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663998343/1250000000 : ℝ), (5394945231/10000000000 : ℝ), (-1054459589/5000000000 : ℝ)] ![(21603756942929/50000000000000 : ℝ), (44104870902889/100000000000000 : ℝ), (507504607673/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663998343/1250000000 : ℝ)|^8321 ≤ (21603756942929/50000000000000 : ℝ)^6273
        have hw : |(663998343/1250000000 : ℝ)|=(663998343/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394945231/10000000000 : ℝ)|^8321 ≤ (44104870902889/100000000000000 : ℝ)^6273
        have hw : |(5394945231/10000000000 : ℝ)|=(5394945231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1054459589/5000000000 : ℝ)|^8321 ≤ (507504607673/4000000000000 : ℝ)^6273
        have hw : |(-1054459589/5000000000 : ℝ)|=(1054459589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s5_7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2183279401/5000000000 : ℝ)*x 0 + (112460869/250000000 : ℝ)*x 1 + (4238566191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183279401/5000000000 : ℝ)^8321 ≤ (33315973994507/100000000000000 : ℝ)^6273 := by
    have hnat : (2183279401 : ℕ)^8321*100000000000000^6273 ≤ 33315973994507^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183279401 5000000000 33315973994507 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (112460869/250000000 : ℝ)^8321 ≤ (34657195869053/100000000000000 : ℝ)^6273 := by
    have hnat : (112460869 : ℕ)^8321*100000000000000^6273 ≤ 34657195869053^6273*250000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112460869 250000000 34657195869053 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4238566191/10000000000 : ℝ)^8321 ≤ (16013415056661/50000000000000 : ℝ)^6273 := by
    have hnat : (4238566191 : ℕ)^8321*50000000000000^6273 ≤ 16013415056661^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238566191 10000000000 16013415056661 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2183279401/5000000000 : ℝ), (112460869/250000000 : ℝ), (4238566191/10000000000 : ℝ)] ![(33315973994507/100000000000000 : ℝ), (34657195869053/100000000000000 : ℝ), (16013415056661/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2183279401/5000000000 : ℝ)|^8321 ≤ (33315973994507/100000000000000 : ℝ)^6273
        have hw : |(2183279401/5000000000 : ℝ)|=(2183279401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(112460869/250000000 : ℝ)|^8321 ≤ (34657195869053/100000000000000 : ℝ)^6273
        have hw : |(112460869/250000000 : ℝ)|=(112460869/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4238566191/10000000000 : ℝ)|^8321 ≤ (16013415056661/50000000000000 : ℝ)^6273
        have hw : |(4238566191/10000000000 : ℝ)|=(4238566191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1128_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9325039/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2787/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5647/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14083/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2787/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2787/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2787/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2787/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2787/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2787/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
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
  have hpowlo : (2787/25000 : ℝ) ^ (65/16 : ℝ) ≤ (1683246279349249/12500000000000000000 : ℝ) := by
    have hpowers : (2787/25000 : ℝ)^65 ≤ (1683246279349249/12500000000000000000 : ℝ)^16 := by
      have hnat : (2787 : ℕ)^65*12500000000000000000^16 ≤ 1683246279349249^16*25000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2787 25000 1683246279349249 12500000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2787/25000 : ℝ)) (X := (1683246279349249/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hpowhi : (3559/25000 : ℝ) ^ (65/16 : ℝ) ≤ (909030959843809/2500000000000000000 : ℝ) := by
    have hpowers : (3559/25000 : ℝ)^65 ≤ (909030959843809/2500000000000000000 : ℝ)^16 := by
      have hnat : (3559 : ℕ)^65*2500000000000000000^16 ≤ 909030959843809^16*25000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3559 25000 909030959843809 2500000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3559/25000 : ℝ)) (X := (909030959843809/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251683246279349249/6250000000000000000 : ℝ) ≤ (1250082859098357/1250000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (6251683246279349249/6250000000000000000 : ℝ)^16 ≤ (1250082859098357/1250000000000000 : ℝ)^65 := by
      have hnat : (6251683246279349249 : ℕ)^16*1250000000000000^65 ≤ 1250082859098357^65*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251683246279349249 6250000000000000000 1250082859098357 1250000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250082859098357/1250000000000000 : ℝ)) (X := (6251683246279349249/6250000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hcorner10 : (6253114200539284147/6250000000000000000 : ℝ) ≤ (400049051424781/400000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (6253114200539284147/6250000000000000000 : ℝ)^16 ≤ (400049051424781/400000000000000 : ℝ)^65 := by
      have hnat : (6253114200539284147 : ℕ)^16*400000000000000^65 ≤ 400049051424781^65*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253114200539284147 6250000000000000000 400049051424781 400000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400049051424781/400000000000000 : ℝ)) (X := (6253114200539284147/6250000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hcorner11 : (1250909030959843809/1250000000000000000 : ℝ) ≤ (5000894849226097/5000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (1250909030959843809/1250000000000000000 : ℝ)^16 ≤ (5000894849226097/5000000000000000 : ℝ)^65 := by
      have hnat : (1250909030959843809 : ℕ)^16*5000000000000000^65 ≤ 5000894849226097^65*1250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250909030959843809 1250000000000000000 5000894849226097 5000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000894849226097/5000000000000000 : ℝ)) (X := (1250909030959843809/1250000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1683246279349249/12500000000000000000 : ℝ) ≤ ((3858685637331077913/3860000000000000000 : ℝ)+2*(563412832669/308800000000000 : ℝ)*(2787/25000 : ℝ))^(65/16 : ℝ) := by
    rw [show (3858685637331077913/3860000000000000000 : ℝ)+2*(563412832669/308800000000000 : ℝ)*(2787/25000 : ℝ)=(1250082859098357/1250000000000000 : ℝ) by norm_num, show 1+2*(1683246279349249/12500000000000000000 : ℝ)=(6251683246279349249/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(909030959843809/2500000000000000000 : ℝ)+(1683246279349249/12500000000000000000 : ℝ) ≤ ((3858685637331077913/3860000000000000000 : ℝ)+(563412832669/308800000000000 : ℝ)*((3559/25000 : ℝ)+(2787/25000 : ℝ)))^(65/16 : ℝ) := by
    rw [show (3858685637331077913/3860000000000000000 : ℝ)+(563412832669/308800000000000 : ℝ)*((3559/25000 : ℝ)+(2787/25000 : ℝ))=(400049051424781/400000000000000 : ℝ) by norm_num, show 1+(909030959843809/2500000000000000000 : ℝ)+(1683246279349249/12500000000000000000 : ℝ)=(6253114200539284147/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(909030959843809/2500000000000000000 : ℝ) ≤ ((3858685637331077913/3860000000000000000 : ℝ)+2*(563412832669/308800000000000 : ℝ)*(3559/25000 : ℝ))^(65/16 : ℝ) := by
    rw [show (3858685637331077913/3860000000000000000 : ℝ)+2*(563412832669/308800000000000 : ℝ)*(3559/25000 : ℝ)=(5000894849226097/5000000000000000 : ℝ) by norm_num, show 1+2*(909030959843809/2500000000000000000 : ℝ)=(1250909030959843809/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3858685637331077913/3860000000000000000 : ℝ)*(X 1 0+X 2 0)+(563412832669/308800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (65/16 : ℝ)) (lo := (2787/25000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (3858685637331077913/3860000000000000000 : ℝ)) (alpha := (563412832669/308800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3858685637331077913/3860000000000000000 : ℝ)*(X 0 1+X 2 1)+(563412832669/308800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (65/16 : ℝ)) (lo := (2787/25000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (3858685637331077913/3860000000000000000 : ℝ)) (alpha := (563412832669/308800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3858685637331077913/3860000000000000000 : ℝ)*(X 0 2+X 1 2)+(563412832669/308800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (65/16 : ℝ)) (lo := (2787/25000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (3858685637331077913/3860000000000000000 : ℝ)) (alpha := (563412832669/308800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2173426453/10000000000 : ℝ)*X 0 0+(2697643383/5000000000 : ℝ)*X 0 1+(5263622957/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267265479/500000000 : ℝ)*X 1 0+(-1120120551/5000000000 : ℝ)*X 1 1+(5263622821/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345309317/10000000000 : ℝ)*X 2 0+(1052724607/2000000000 : ℝ)*X 2 1+(-2240241169/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((27290929/62500000 : ℝ)*X 0 0+(847577527/2000000000 : ℝ)*X 0 1+(1124777573/2500000000 : ℝ)*X 0 2+(27290929/62500000 : ℝ)*X 1 0+(847577527/2000000000 : ℝ)*X 1 1+(1124777573/2500000000 : ℝ)*X 1 2+(27290929/62500000 : ℝ)*X 2 0+(847577527/2000000000 : ℝ)*X 2 1+(1124777573/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-543357783/2500000000 : ℝ)*X 0 0+(210558557/400000000 : ℝ)*X 0 1+(5394945053/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062397419/2000000000 : ℝ)*X 1 0+(-105445953/500000000 : ℝ)*X 1 1+(5394944969/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663998343/1250000000 : ℝ)*X 2 0+(5394945231/10000000000 : ℝ)*X 2 1+(-1054459589/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2183279401/5000000000 : ℝ)*X 0 0+(112460869/250000000 : ℝ)*X 0 1+(4238566191/10000000000 : ℝ)*X 0 2+(2183279401/5000000000 : ℝ)*X 1 0+(112460869/250000000 : ℝ)*X 1 1+(4238566191/10000000000 : ℝ)*X 1 2+(2183279401/5000000000 : ℝ)*X 2 0+(112460869/250000000 : ℝ)*X 2 1+(4238566191/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (73186145406085509378507/7720000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2490966689/100000000000000 : ℝ)*(base19) + (1834884679/100000000000000 : ℝ)*(base23) + (431809351/100000000000000 : ℝ)*(upper3) + (37735497/25000000000000 : ℝ)*(upper4) + (26672823/50000000000000 : ℝ)*(upper5) + (2855856932192379/50000000000000 : ℝ)*(major0) + (2855856932192379/50000000000000 : ℝ)*(major1) + (2855856932192379/50000000000000 : ℝ)*(major2) + (75951678789463/1000000000000 : ℝ)*(sp0) + (3797607240943257/50000000000000 : ℝ)*(sp1) + (7595215137968523/100000000000000 : ℝ)*(sp2) + (3828177607572219/100000000000000 : ℝ)*(sp3) + (24546953451/50000000000000 : ℝ)*(sp4) + (32832341731/100000000000000 : ℝ)*(sp7) + (76564208798279/2000000000000 : ℝ)*(f.failure) + (7595216972853203/100000000000000 : ℝ)*(f.sum) + (28918942773791/7720000000000000000000000000 : ℝ)*base65 + (2971989358148212527/193000000000000000000000000000000 : ℝ)*base67 + (1945171130048212527/193000000000000000000000000000000 : ℝ)*base69 + (528460281882787473/193000000000000000000000000000000 : ℝ)*base72 + (19708737748711/7720000000000000000000000000 : ℝ)*base73 + (213508989935787473/193000000000000000000000000000000 : ℝ)*base76 + (2040828156614212527/193000000000000000000000000000000 : ℝ)*base77 + (678905014766787473/193000000000000000000000000000000 : ℝ)*base80 + (47641993495489/7720000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (57881/12500000000000000000 : ℝ)*base89 + (57881/12500000000000000000 : ℝ)*base91 + (57881/12500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (98409404552005152239883177/12062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19283223/20000000000000 : ℝ)*(base8) + (36141547/50000000000000 : ℝ)*(upper2) + (6440731/20000000000000 : ℝ)*(lower3) + (5416441/3125000000000 : ℝ)*(lower4) + (140218101/100000000000000 : ℝ)*(lower5) + (717672975029607/12500000000000 : ℝ)*(major0) + (717672975029607/12500000000000 : ℝ)*(major1) + (717672975029607/12500000000000 : ℝ)*(major2) + (19121281/1250000000000 : ℝ)*(sp1) + (8242192301/100000000000000 : ℝ)*(sp2) + (7634670859382929/100000000000000 : ℝ)*(sp4) + (3817334713048281/50000000000000 : ℝ)*(sp5) + (7634662713606743/100000000000000 : ℝ)*(sp6) + (1924048186365781/50000000000000 : ℝ)*(sp7) + (1924048186365781/50000000000000 : ℝ)*(f.failure) + (1908667738949761/25000000000000 : ℝ)*(f.sum) + (13404168944197/1930000000000000000000000000 : ℝ)*base66 + (38751618066057691/48250000000000000000000000000000 : ℝ)*base67 + (498907567350557691/48250000000000000000000000000000 : ℝ)*base69 + (200215269986807691/48250000000000000000000000000000 : ℝ)*base71 + (16268148718117/1930000000000000000000000000 : ℝ)*base74 + (204718033037307691/48250000000000000000000000000000 : ℝ)*base75 + (6160309975479942309/48250000000000000000000000000000 : ℝ)*base78 + (261487618141307691/48250000000000000000000000000000 : ℝ)*base79 + (110462818413/1930000000000000000000000000 : ℝ)*base81 + (1/50000000000000 : ℝ)*base86 + (1090459/312500000000000000000 : ℝ)*base89 + (1090459/312500000000000000000 : ℝ)*base91 + (1090459/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1128_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9325039/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2787/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5647/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14083/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1128_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1128_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9325039/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3309/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4503/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5647/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14083/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1128_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1128_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1128_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9325039/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3309/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4503/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5647/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14083/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1128_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

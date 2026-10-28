-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1144_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:32:43.322992+00:00
-- url     : https://prove2.me/submissions/158bf867-d766-4996-a91a-e6a810dd53b6

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
theorem support_rectangle_w1144_s0_0 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-945588961/5000000000 : ℝ)*x 0 + (756733507/1250000000 : ℝ)*x 1 + (298795323/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (945588961/5000000000 : ℝ)^8337 ≤ (10995165468767/100000000000000 : ℝ)^6289 := by
    have hnat : (945588961 : ℕ)^8337*100000000000000^6289 ≤ 10995165468767^6289*5000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      945588961 5000000000 10995165468767 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (756733507/1250000000 : ℝ)^8337 ≤ (6426321371559/12500000000000 : ℝ)^6289 := by
    have hnat : (756733507 : ℕ)^8337*12500000000000^6289 ≤ 6426321371559^6289*1250000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      756733507 1250000000 6426321371559 12500000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (298795323/625000000 : ℝ)^8337 ≤ (7518852708037/20000000000000 : ℝ)^6289 := by
    have hnat : (298795323 : ℕ)^8337*20000000000000^6289 ≤ 7518852708037^6289*625000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      298795323 625000000 7518852708037 20000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-945588961/5000000000 : ℝ), (756733507/1250000000 : ℝ), (298795323/625000000 : ℝ)] ![(10995165468767/100000000000000 : ℝ), (6426321371559/12500000000000 : ℝ), (7518852708037/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-945588961/5000000000 : ℝ)|^8337 ≤ (10995165468767/100000000000000 : ℝ)^6289
        have hw : |(-945588961/5000000000 : ℝ)|=(945588961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(756733507/1250000000 : ℝ)|^8337 ≤ (6426321371559/12500000000000 : ℝ)^6289
        have hw : |(756733507/1250000000 : ℝ)|=(756733507/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(298795323/625000000 : ℝ)|^8337 ≤ (7518852708037/20000000000000 : ℝ)^6289
        have hw : |(298795323/625000000 : ℝ)|=(298795323/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s0_1 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2758340487/5000000000 : ℝ)*x 0 + (-2621755503/10000000000 : ℝ)*x 1 + (74698831/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2758340487/5000000000 : ℝ)^8337 ≤ (1818091712457/4000000000000 : ℝ)^6289 := by
    have hnat : (2758340487 : ℕ)^8337*4000000000000^6289 ≤ 1818091712457^6289*5000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2758340487 5000000000 1818091712457 4000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621755503/10000000000 : ℝ)^8337 ≤ (16953443463293/100000000000000 : ℝ)^6289 := by
    have hnat : (2621755503 : ℕ)^8337*100000000000000^6289 ≤ 16953443463293^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621755503 10000000000 16953443463293 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (74698831/156250000 : ℝ)^8337 ≤ (37594263706977/100000000000000 : ℝ)^6289 := by
    have hnat : (74698831 : ℕ)^8337*100000000000000^6289 ≤ 37594263706977^6289*156250000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74698831 156250000 37594263706977 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2758340487/5000000000 : ℝ), (-2621755503/10000000000 : ℝ), (74698831/156250000 : ℝ)] ![(1818091712457/4000000000000 : ℝ), (16953443463293/100000000000000 : ℝ), (37594263706977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2758340487/5000000000 : ℝ)|^8337 ≤ (1818091712457/4000000000000 : ℝ)^6289
        have hw : |(2758340487/5000000000 : ℝ)|=(2758340487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2621755503/10000000000 : ℝ)|^8337 ≤ (16953443463293/100000000000000 : ℝ)^6289
        have hw : |(-2621755503/10000000000 : ℝ)|=(2621755503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(74698831/156250000 : ℝ)|^8337 ≤ (37594263706977/100000000000000 : ℝ)^6289
        have hw : |(74698831/156250000 : ℝ)|=(74698831/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s0_2 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5516681059/10000000000 : ℝ)*x 0 + (1195181287/2500000000 : ℝ)*x 1 + (-2621755439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5516681059/10000000000 : ℝ)^8337 ≤ (45452293739803/100000000000000 : ℝ)^6289 := by
    have hnat : (5516681059 : ℕ)^8337*100000000000000^6289 ≤ 45452293739803^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5516681059 10000000000 45452293739803 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1195181287/2500000000 : ℝ)^8337 ≤ (18797131665847/50000000000000 : ℝ)^6289 := by
    have hnat : (1195181287 : ℕ)^8337*50000000000000^6289 ≤ 18797131665847^6289*2500000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1195181287 2500000000 18797131665847 50000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621755439/10000000000 : ℝ)^8337 ≤ (1695344291467/10000000000000 : ℝ)^6289 := by
    have hnat : (2621755439 : ℕ)^8337*10000000000000^6289 ≤ 1695344291467^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621755439 10000000000 1695344291467 10000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5516681059/10000000000 : ℝ), (1195181287/2500000000 : ℝ), (-2621755439/10000000000 : ℝ)] ![(45452293739803/100000000000000 : ℝ), (18797131665847/50000000000000 : ℝ), (1695344291467/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5516681059/10000000000 : ℝ)|^8337 ≤ (45452293739803/100000000000000 : ℝ)^6289
        have hw : |(5516681059/10000000000 : ℝ)|=(5516681059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1195181287/2500000000 : ℝ)|^8337 ≤ (18797131665847/50000000000000 : ℝ)^6289
        have hw : |(1195181287/2500000000 : ℝ)|=(1195181287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2621755439/10000000000 : ℝ)|^8337 ≤ (1695344291467/10000000000000 : ℝ)^6289
        have hw : |(-2621755439/10000000000 : ℝ)|=(2621755439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s0_3 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (420082911/1000000000 : ℝ)*x 0 + (9753081/31250000 : ℝ)*x 1 + (5654864491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (420082911/1000000000 : ℝ)^8337 ≤ (6334390420343/20000000000000 : ℝ)^6289 := by
    have hnat : (420082911 : ℕ)^8337*20000000000000^6289 ≤ 6334390420343^6289*1000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420082911 1000000000 6334390420343 20000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9753081/31250000 : ℝ)^8337 ≤ (10680189899503/50000000000000 : ℝ)^6289 := by
    have hnat : (9753081 : ℕ)^8337*50000000000000^6289 ≤ 10680189899503^6289*31250000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9753081 31250000 10680189899503 50000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5654864491/10000000000 : ℝ)^8337 ≤ (46967668088801/100000000000000 : ℝ)^6289 := by
    have hnat : (5654864491 : ℕ)^8337*100000000000000^6289 ≤ 46967668088801^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5654864491 10000000000 46967668088801 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(420082911/1000000000 : ℝ), (9753081/31250000 : ℝ), (5654864491/10000000000 : ℝ)] ![(6334390420343/20000000000000 : ℝ), (10680189899503/50000000000000 : ℝ), (46967668088801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(420082911/1000000000 : ℝ)|^8337 ≤ (6334390420343/20000000000000 : ℝ)^6289
        have hw : |(420082911/1000000000 : ℝ)|=(420082911/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(9753081/31250000 : ℝ)|^8337 ≤ (10680189899503/50000000000000 : ℝ)^6289
        have hw : |(9753081/31250000 : ℝ)|=(9753081/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5654864491/10000000000 : ℝ)|^8337 ≤ (46967668088801/100000000000000 : ℝ)^6289
        have hw : |(5654864491/10000000000 : ℝ)|=(5654864491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s0_4 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-948158797/5000000000 : ℝ)*x 0 + (962713537/2000000000 : ℝ)*x 1 + (6019870699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (948158797/5000000000 : ℝ)^8337 ≤ (1379349444299/12500000000000 : ℝ)^6289 := by
    have hnat : (948158797 : ℕ)^8337*12500000000000^6289 ≤ 1379349444299^6289*5000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      948158797 5000000000 1379349444299 12500000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (962713537/2000000000 : ℝ)^8337 ≤ (37937013341343/100000000000000 : ℝ)^6289 := by
    have hnat : (962713537 : ℕ)^8337*100000000000000^6289 ≤ 37937013341343^6289*2000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      962713537 2000000000 37937013341343 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6019870699/10000000000 : ℝ)^8337 ≤ (199328871429/390625000000 : ℝ)^6289 := by
    have hnat : (6019870699 : ℕ)^8337*390625000000^6289 ≤ 199328871429^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6019870699 10000000000 199328871429 390625000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-948158797/5000000000 : ℝ), (962713537/2000000000 : ℝ), (6019870699/10000000000 : ℝ)] ![(1379349444299/12500000000000 : ℝ), (37937013341343/100000000000000 : ℝ), (199328871429/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-948158797/5000000000 : ℝ)|^8337 ≤ (1379349444299/12500000000000 : ℝ)^6289
        have hw : |(-948158797/5000000000 : ℝ)|=(948158797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(962713537/2000000000 : ℝ)|^8337 ≤ (37937013341343/100000000000000 : ℝ)^6289
        have hw : |(962713537/2000000000 : ℝ)|=(962713537/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6019870699/10000000000 : ℝ)|^8337 ≤ (199328871429/390625000000 : ℝ)^6289
        have hw : |(6019870699/10000000000 : ℝ)|=(6019870699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s0_5 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1034145941/2000000000 : ℝ)*x 0 + (-1382610071/10000000000 : ℝ)*x 1 + (6019870559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1034145941/2000000000 : ℝ)^8337 ≤ (5214114810339/12500000000000 : ℝ)^6289 := by
    have hnat : (1034145941 : ℕ)^8337*12500000000000^6289 ≤ 5214114810339^6289*2000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034145941 2000000000 5214114810339 12500000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1382610071/10000000000 : ℝ)^8337 ≤ (907361498681/12500000000000 : ℝ)^6289 := by
    have hnat : (1382610071 : ℕ)^8337*12500000000000^6289 ≤ 907361498681^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1382610071 10000000000 907361498681 12500000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6019870559/10000000000 : ℝ)^8337 ≤ (51028189512641/100000000000000 : ℝ)^6289 := by
    have hnat : (6019870559 : ℕ)^8337*100000000000000^6289 ≤ 51028189512641^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6019870559 10000000000 51028189512641 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1034145941/2000000000 : ℝ), (-1382610071/10000000000 : ℝ), (6019870559/10000000000 : ℝ)] ![(5214114810339/12500000000000 : ℝ), (907361498681/12500000000000 : ℝ), (51028189512641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1034145941/2000000000 : ℝ)|^8337 ≤ (5214114810339/12500000000000 : ℝ)^6289
        have hw : |(1034145941/2000000000 : ℝ)|=(1034145941/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1382610071/10000000000 : ℝ)|^8337 ≤ (907361498681/12500000000000 : ℝ)^6289
        have hw : |(-1382610071/10000000000 : ℝ)|=(1382610071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6019870559/10000000000 : ℝ)|^8337 ≤ (51028189512641/100000000000000 : ℝ)^6289
        have hw : |(6019870559/10000000000 : ℝ)|=(6019870559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s0_6 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1034145941/2000000000 : ℝ)*x 0 + (1504967647/2500000000 : ℝ)*x 1 + (-172826253/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1034145941/2000000000 : ℝ)^8337 ≤ (5214114810339/12500000000000 : ℝ)^6289 := by
    have hnat : (1034145941 : ℕ)^8337*12500000000000^6289 ≤ 5214114810339^6289*2000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034145941 2000000000 5214114810339 12500000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1504967647/2500000000 : ℝ)^8337 ≤ (10205637967703/20000000000000 : ℝ)^6289 := by
    have hnat : (1504967647 : ℕ)^8337*20000000000000^6289 ≤ 10205637967703^6289*2500000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1504967647 2500000000 10205637967703 20000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (172826253/1250000000 : ℝ)^8337 ≤ (7088761389/97656250000 : ℝ)^6289 := by
    have hnat : (172826253 : ℕ)^8337*97656250000^6289 ≤ 7088761389^6289*1250000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172826253 1250000000 7088761389 97656250000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1034145941/2000000000 : ℝ), (1504967647/2500000000 : ℝ), (-172826253/1250000000 : ℝ)] ![(5214114810339/12500000000000 : ℝ), (10205637967703/20000000000000 : ℝ), (7088761389/97656250000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1034145941/2000000000 : ℝ)|^8337 ≤ (5214114810339/12500000000000 : ℝ)^6289
        have hw : |(1034145941/2000000000 : ℝ)|=(1034145941/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1504967647/2500000000 : ℝ)|^8337 ≤ (10205637967703/20000000000000 : ℝ)^6289
        have hw : |(1504967647/2500000000 : ℝ)|=(1504967647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-172826253/1250000000 : ℝ)|^8337 ≤ (7088761389/97656250000 : ℝ)^6289
        have hw : |(-172826253/1250000000 : ℝ)|=(172826253/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s0_7 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4211058583/10000000000 : ℝ)*x 0 + (5589499331/10000000000 : ℝ)*x 1 + (1594324779/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4211058583/10000000000 : ℝ)^8337 ≤ (31774232721549/100000000000000 : ℝ)^6289 := by
    have hnat : (4211058583 : ℕ)^8337*100000000000000^6289 ≤ 31774232721549^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4211058583 10000000000 31774232721549 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5589499331/10000000000 : ℝ)^8337 ≤ (23124663227767/50000000000000 : ℝ)^6289 := by
    have hnat : (5589499331 : ℕ)^8337*50000000000000^6289 ≤ 23124663227767^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5589499331 10000000000 23124663227767 50000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1594324779/5000000000 : ℝ)^8337 ≤ (4395288160567/20000000000000 : ℝ)^6289 := by
    have hnat : (1594324779 : ℕ)^8337*20000000000000^6289 ≤ 4395288160567^6289*5000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1594324779 5000000000 4395288160567 20000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4211058583/10000000000 : ℝ), (5589499331/10000000000 : ℝ), (1594324779/5000000000 : ℝ)] ![(31774232721549/100000000000000 : ℝ), (23124663227767/50000000000000 : ℝ), (4395288160567/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4211058583/10000000000 : ℝ)|^8337 ≤ (31774232721549/100000000000000 : ℝ)^6289
        have hw : |(4211058583/10000000000 : ℝ)|=(4211058583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5589499331/10000000000 : ℝ)|^8337 ≤ (23124663227767/50000000000000 : ℝ)^6289
        have hw : |(5589499331/10000000000 : ℝ)|=(5589499331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1594324779/5000000000 : ℝ)|^8337 ≤ (4395288160567/20000000000000 : ℝ)^6289
        have hw : |(1594324779/5000000000 : ℝ)|=(1594324779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1144_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37378183/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (211/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27807/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (521/128 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^521 ≤ (0 : ℝ)^128 := by
      have hnat : (0 : ℕ)^521*1^128 ≤ 0^128*1^521 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 521 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (521/128 : ℝ) ≤ (600067101183462747/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^521 ≤ (600067101183462747/25000000000000000000 : ℝ)^128 := by
      have hnat : (2 : ℕ)^521*25000000000000000000^128 ≤ 600067101183462747^128*5^521 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 600067101183462747 25000000000000000000 521 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (600067101183462747/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (521/128 : ℝ) := by
    have hpowers : (1 : ℝ)^128 ≤ (1 : ℝ)^521 := by
      have hnat : (1 : ℕ)^128*1^521 ≤ 1^521*1^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 128 521 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (25600067101183462747/25000000000000000000 : ℝ) ≤ (5029221825247689/5000000000000000 : ℝ) ^ (521/128 : ℝ) := by
    have hpowers : (25600067101183462747/25000000000000000000 : ℝ)^128 ≤ (5029221825247689/5000000000000000 : ℝ)^521 := by
      have hnat : (25600067101183462747 : ℕ)^128*5000000000000000^521 ≤ 5029221825247689^521*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25600067101183462747 25000000000000000000 5029221825247689 5000000000000000 128 521 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5029221825247689/5000000000000000 : ℝ)) (X := (25600067101183462747/25000000000000000000 : ℝ)) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (13100067101183462747/12500000000000000000 : ℝ) ≤ (2529221825247689/2500000000000000 : ℝ) ^ (521/128 : ℝ) := by
    have hpowers : (13100067101183462747/12500000000000000000 : ℝ)^128 ≤ (2529221825247689/2500000000000000 : ℝ)^521 := by
      have hnat : (13100067101183462747 : ℕ)^128*2500000000000000^521 ≤ 2529221825247689^521*12500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13100067101183462747 12500000000000000000 2529221825247689 2500000000000000 128 521 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2529221825247689/2500000000000000 : ℝ)) (X := (13100067101183462747/12500000000000000000 : ℝ)) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(29221825247689/2000000000000000 : ℝ)*(0 : ℝ))^(521/128 : ℝ) := by
    rw [show (1 : ℝ)+2*(29221825247689/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(600067101183462747/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(29221825247689/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(521/128 : ℝ) := by
    rw [show (1 : ℝ)+(29221825247689/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5029221825247689/5000000000000000 : ℝ) by norm_num, show 1+(600067101183462747/25000000000000000000 : ℝ)+(0 : ℝ)=(25600067101183462747/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(600067101183462747/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(29221825247689/2000000000000000 : ℝ)*(2/5 : ℝ))^(521/128 : ℝ) := by
    rw [show (1 : ℝ)+2*(29221825247689/2000000000000000 : ℝ)*(2/5 : ℝ)=(2529221825247689/2500000000000000 : ℝ) by norm_num, show 1+2*(600067101183462747/25000000000000000000 : ℝ)=(13100067101183462747/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(29221825247689/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (521/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (29221825247689/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(29221825247689/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (521/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (29221825247689/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(29221825247689/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (521/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (29221825247689/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-945588961/5000000000 : ℝ)*X 0 0+(756733507/1250000000 : ℝ)*X 0 1+(298795323/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2758340487/5000000000 : ℝ)*X 1 0+(-2621755503/10000000000 : ℝ)*X 1 1+(74698831/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5516681059/10000000000 : ℝ)*X 2 0+(1195181287/2500000000 : ℝ)*X 2 1+(-2621755439/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((420082911/1000000000 : ℝ)*X 0 0+(9753081/31250000 : ℝ)*X 0 1+(5654864491/10000000000 : ℝ)*X 0 2+(420082911/1000000000 : ℝ)*X 1 0+(9753081/31250000 : ℝ)*X 1 1+(5654864491/10000000000 : ℝ)*X 1 2+(420082911/1000000000 : ℝ)*X 2 0+(9753081/31250000 : ℝ)*X 2 1+(5654864491/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-948158797/5000000000 : ℝ)*X 0 0+(962713537/2000000000 : ℝ)*X 0 1+(6019870699/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1034145941/2000000000 : ℝ)*X 1 0+(-1382610071/10000000000 : ℝ)*X 1 1+(6019870559/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1034145941/2000000000 : ℝ)*X 2 0+(1504967647/2500000000 : ℝ)*X 2 1+(-172826253/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4211058583/10000000000 : ℝ)*X 0 0+(5589499331/10000000000 : ℝ)*X 0 1+(1594324779/5000000000 : ℝ)*X 0 2+(4211058583/10000000000 : ℝ)*X 1 0+(5589499331/10000000000 : ℝ)*X 1 1+(1594324779/5000000000 : ℝ)*X 1 2+(4211058583/10000000000 : ℝ)*X 2 0+(5589499331/10000000000 : ℝ)*X 2 1+(1594324779/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (34443744040216675570467/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3522077/12500000000000 : ℝ)*(base1) + (5495493/800000000000 : ℝ)*(base19) + (645499427/100000000000000 : ℝ)*(base23) + (53539433/100000000000000 : ℝ)*(base24) + (158983627/100000000000000 : ℝ)*(upper3) + (147514437898433/25000000000000 : ℝ)*(major0) + (147514437898433/25000000000000 : ℝ)*(major1) + (147514437898433/25000000000000 : ℝ)*(major2) + (785460078709153/100000000000000 : ℝ)*(sp0) + (392730437696853/50000000000000 : ℝ)*(sp1) + (785460863291471/100000000000000 : ℝ)*(sp2) + (394652605767433/100000000000000 : ℝ)*(sp3) + (755898897/50000000000000 : ℝ)*(sp4) + (303765773/25000000000000 : ℝ)*(sp7) + (394653849007141/100000000000000 : ℝ)*(f.failure) + (785461562330331/100000000000000 : ℝ)*(f.sum) + (51909210871337/25000000000000000000000000000 : ℝ)*base65 + (302581936471337/50000000000000000000000000000 : ℝ)*base67 + (503692067521337/50000000000000000000000000000 : ℝ)*base69 + (503556704471337/50000000000000000000000000000 : ℝ)*base71 + (4327082621337/25000000000000000000000000000 : ℝ)*base73 + (274852507821337/50000000000000000000000000000 : ℝ)*base75 + (312936797221337/50000000000000000000000000000 : ℝ)*base77 + (255111473971337/50000000000000000000000000000 : ℝ)*base79 + (70826995721337/25000000000000000000000000000 : ℝ)*base81 + (15395197/2500000000000000000000 : ℝ)*base90 + (15395197/2500000000000000000000 : ℝ)*base92 + (15395197/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (25992474973175268697419/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (35157773/100000000000000 : ℝ)*(base1) + (50945711/10000000000000 : ℝ)*(base19) + (50861947/10000000000000 : ℝ)*(base23) + (48841019/100000000000000 : ℝ)*(upper3) + (63764073/100000000000000 : ℝ)*(upper5) + (311374605694643/50000000000000 : ℝ)*(major0) + (311374605694643/50000000000000 : ℝ)*(major1) + (311374605694643/50000000000000 : ℝ)*(major2) + (122220599/12500000000000 : ℝ)*(sp1) + (965244859/100000000000000 : ℝ)*(sp2) + (82897920456503/10000000000000 : ℝ)*(sp4) + (207244420546339/25000000000000 : ℝ)*(sp5) + (828977695542929/100000000000000 : ℝ)*(sp6) + (104129787225067/25000000000000 : ℝ)*(sp7) + (416519184058041/100000000000000 : ℝ)*(f.failure) + (828979169407257/100000000000000 : ℝ)*(f.sum) + (72580254230027/50000000000000000000000000000 : ℝ)*base65 + (499815749630027/100000000000000000000000000000 : ℝ)*base67 + (437759624030027/100000000000000000000000000000 : ℝ)*base69 + (602786612230027/100000000000000000000000000000 : ℝ)*base71 + (285305872630027/50000000000000000000000000000 : ℝ)*base73 + (299360352169973/100000000000000000000000000000 : ℝ)*base76 + (66110188430027/100000000000000000000000000000 : ℝ)*base77 + (49027333769973/100000000000000000000000000000 : ℝ)*base80 + (279067218080027/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (10880497/2500000000000000000000 : ℝ)*base90 + (10880497/2500000000000000000000 : ℝ)*base92 + (10880497/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1144_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37378183/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (211/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27807/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1144_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1144_s1_0 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-523925437/2500000000 : ℝ)*x 0 + (142524039/250000000 : ℝ)*x 1 + (125067417/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (523925437/2500000000 : ℝ)^8337 ≤ (1259858603411/10000000000000 : ℝ)^6289 := by
    have hnat : (523925437 : ℕ)^8337*10000000000000^6289 ≤ 1259858603411^6289*2500000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523925437 2500000000 1259858603411 10000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (142524039/250000000 : ℝ)^8337 ≤ (23737944962701/50000000000000 : ℝ)^6289 := by
    have hnat : (142524039 : ℕ)^8337*50000000000000^6289 ≤ 23737944962701^6289*250000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142524039 250000000 23737944962701 50000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (125067417/250000000 : ℝ)^8337 ≤ (9981381006583/25000000000000 : ℝ)^6289 := by
    have hnat : (125067417 : ℕ)^8337*25000000000000^6289 ≤ 9981381006583^6289*250000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125067417 250000000 9981381006583 25000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-523925437/2500000000 : ℝ), (142524039/250000000 : ℝ), (125067417/250000000 : ℝ)] ![(1259858603411/10000000000000 : ℝ), (23737944962701/50000000000000 : ℝ), (9981381006583/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-523925437/2500000000 : ℝ)|^8337 ≤ (1259858603411/10000000000000 : ℝ)^6289
        have hw : |(-523925437/2500000000 : ℝ)|=(523925437/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(142524039/250000000 : ℝ)|^8337 ≤ (23737944962701/50000000000000 : ℝ)^6289
        have hw : |(142524039/250000000 : ℝ)|=(142524039/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(125067417/250000000 : ℝ)|^8337 ≤ (9981381006583/25000000000000 : ℝ)^6289
        have hw : |(125067417/250000000 : ℝ)|=(125067417/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s1_1 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5419009887/10000000000 : ℝ)*x 0 + (-154530289/625000000 : ℝ)*x 1 + (1250673987/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5419009887/10000000000 : ℝ)^8337 ≤ (2219430351913/5000000000000 : ℝ)^6289 := by
    have hnat : (5419009887 : ℕ)^8337*5000000000000^6289 ≤ 2219430351913^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419009887 10000000000 2219430351913 5000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (154530289/625000000 : ℝ)^8337 ≤ (15685876672199/100000000000000 : ℝ)^6289 := by
    have hnat : (154530289 : ℕ)^8337*100000000000000^6289 ≤ 15685876672199^6289*625000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      154530289 625000000 15685876672199 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1250673987/2500000000 : ℝ)^8337 ≤ (39925516281969/100000000000000 : ℝ)^6289 := by
    have hnat : (1250673987 : ℕ)^8337*100000000000000^6289 ≤ 39925516281969^6289*2500000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1250673987 2500000000 39925516281969 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5419009887/10000000000 : ℝ), (-154530289/625000000 : ℝ), (1250673987/2500000000 : ℝ)] ![(2219430351913/5000000000000 : ℝ), (15685876672199/100000000000000 : ℝ), (39925516281969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5419009887/10000000000 : ℝ)|^8337 ≤ (2219430351913/5000000000000 : ℝ)^6289
        have hw : |(5419009887/10000000000 : ℝ)|=(5419009887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-154530289/625000000 : ℝ)|^8337 ≤ (15685876672199/100000000000000 : ℝ)^6289
        have hw : |(-154530289/625000000 : ℝ)|=(154530289/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1250673987/2500000000 : ℝ)|^8337 ≤ (39925516281969/100000000000000 : ℝ)^6289
        have hw : |(1250673987/2500000000 : ℝ)|=(1250673987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s1_2 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5419011853/10000000000 : ℝ)*x 0 + (5002694199/10000000000 : ℝ)*x 1 + (-618121071/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5419011853/10000000000 : ℝ)^8337 ≤ (44388628386561/100000000000000 : ℝ)^6289 := by
    have hnat : (5419011853 : ℕ)^8337*100000000000000^6289 ≤ 44388628386561^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419011853 10000000000 44388628386561 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5002694199/10000000000 : ℝ)^8337 ≤ (1996274888901/5000000000000 : ℝ)^6289 := by
    have hnat : (5002694199 : ℕ)^8337*5000000000000^6289 ≤ 1996274888901^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5002694199 10000000000 1996274888901 5000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (618121071/2500000000 : ℝ)^8337 ≤ (62743495251/400000000000 : ℝ)^6289 := by
    have hnat : (618121071 : ℕ)^8337*400000000000^6289 ≤ 62743495251^6289*2500000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      618121071 2500000000 62743495251 400000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5419011853/10000000000 : ℝ), (5002694199/10000000000 : ℝ), (-618121071/2500000000 : ℝ)] ![(44388628386561/100000000000000 : ℝ), (1996274888901/5000000000000 : ℝ), (62743495251/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5419011853/10000000000 : ℝ)|^8337 ≤ (44388628386561/100000000000000 : ℝ)^6289
        have hw : |(5419011853/10000000000 : ℝ)|=(5419011853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5002694199/10000000000 : ℝ)|^8337 ≤ (1996274888901/5000000000000 : ℝ)^6289
        have hw : |(5002694199/10000000000 : ℝ)|=(5002694199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-618121071/2500000000 : ℝ)|^8337 ≤ (62743495251/400000000000 : ℝ)^6289
        have hw : |(-618121071/2500000000 : ℝ)|=(618121071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s1_3 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (107931811/250000000 : ℝ)*x 0 + (3677436227/10000000000 : ℝ)*x 1 + (126678957/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107931811/250000000 : ℝ)^8337 ≤ (32840983913683/100000000000000 : ℝ)^6289 := by
    have hnat : (107931811 : ℕ)^8337*100000000000000^6289 ≤ 32840983913683^6289*250000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107931811 250000000 32840983913683 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3677436227/10000000000 : ℝ)^8337 ≤ (1659379930661/6250000000000 : ℝ)^6289 := by
    have hnat : (3677436227 : ℕ)^8337*6250000000000^6289 ≤ 1659379930661^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3677436227 10000000000 1659379930661 6250000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (126678957/250000000 : ℝ)^8337 ≤ (40608937185943/100000000000000 : ℝ)^6289 := by
    have hnat : (126678957 : ℕ)^8337*100000000000000^6289 ≤ 40608937185943^6289*250000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126678957 250000000 40608937185943 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107931811/250000000 : ℝ), (3677436227/10000000000 : ℝ), (126678957/250000000 : ℝ)] ![(32840983913683/100000000000000 : ℝ), (1659379930661/6250000000000 : ℝ), (40608937185943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107931811/250000000 : ℝ)|^8337 ≤ (32840983913683/100000000000000 : ℝ)^6289
        have hw : |(107931811/250000000 : ℝ)|=(107931811/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3677436227/10000000000 : ℝ)|^8337 ≤ (1659379930661/6250000000000 : ℝ)^6289
        have hw : |(3677436227/10000000000 : ℝ)|=(3677436227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(126678957/250000000 : ℝ)|^8337 ≤ (40608937185943/100000000000000 : ℝ)^6289
        have hw : |(126678957/250000000 : ℝ)|=(126678957/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s1_4 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-419301093/2000000000 : ℝ)*x 0 + (501222299/1000000000 : ℝ)*x 1 + (227649853/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (419301093/2000000000 : ℝ)^8337 ≤ (12604991501251/100000000000000 : ℝ)^6289 := by
    have hnat : (419301093 : ℕ)^8337*100000000000000^6289 ≤ 12604991501251^6289*2000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419301093 2000000000 12604991501251 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (501222299/1000000000 : ℝ)^8337 ≤ (40026341067339/100000000000000 : ℝ)^6289 := by
    have hnat : (501222299 : ℕ)^8337*100000000000000^6289 ≤ 40026341067339^6289*1000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501222299 1000000000 40026341067339 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (227649853/400000000 : ℝ)^8337 ≤ (11842166855071/25000000000000 : ℝ)^6289 := by
    have hnat : (227649853 : ℕ)^8337*25000000000000^6289 ≤ 11842166855071^6289*400000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227649853 400000000 11842166855071 25000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-419301093/2000000000 : ℝ), (501222299/1000000000 : ℝ), (227649853/400000000 : ℝ)] ![(12604991501251/100000000000000 : ℝ), (40026341067339/100000000000000 : ℝ), (11842166855071/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-419301093/2000000000 : ℝ)|^8337 ≤ (12604991501251/100000000000000 : ℝ)^6289
        have hw : |(-419301093/2000000000 : ℝ)|=(419301093/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(501222299/1000000000 : ℝ)|^8337 ≤ (40026341067339/100000000000000 : ℝ)^6289
        have hw : |(501222299/1000000000 : ℝ)|=(501222299/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(227649853/400000000 : ℝ)|^8337 ≤ (11842166855071/25000000000000 : ℝ)^6289
        have hw : |(227649853/400000000 : ℝ)|=(227649853/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s1_5 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (163749051/312500000 : ℝ)*x 0 + (-891967021/5000000000 : ℝ)*x 1 + (2845622983/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (163749051/312500000 : ℝ)^8337 ≤ (42454991425947/100000000000000 : ℝ)^6289 := by
    have hnat : (163749051 : ℕ)^8337*100000000000000^6289 ≤ 42454991425947^6289*312500000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163749051 312500000 42454991425947 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (891967021/5000000000 : ℝ)^8337 ≤ (10176345105791/100000000000000 : ℝ)^6289 := by
    have hnat : (891967021 : ℕ)^8337*100000000000000^6289 ≤ 10176345105791^6289*5000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      891967021 5000000000 10176345105791 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2845622983/5000000000 : ℝ)^8337 ≤ (4736866345927/10000000000000 : ℝ)^6289 := by
    have hnat : (2845622983 : ℕ)^8337*10000000000000^6289 ≤ 4736866345927^6289*5000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2845622983 5000000000 4736866345927 10000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(163749051/312500000 : ℝ), (-891967021/5000000000 : ℝ), (2845622983/5000000000 : ℝ)] ![(42454991425947/100000000000000 : ℝ), (10176345105791/100000000000000 : ℝ), (4736866345927/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(163749051/312500000 : ℝ)|^8337 ≤ (42454991425947/100000000000000 : ℝ)^6289
        have hw : |(163749051/312500000 : ℝ)|=(163749051/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-891967021/5000000000 : ℝ)|^8337 ≤ (10176345105791/100000000000000 : ℝ)^6289
        have hw : |(-891967021/5000000000 : ℝ)|=(891967021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2845622983/5000000000 : ℝ)|^8337 ≤ (4736866345927/10000000000000 : ℝ)^6289
        have hw : |(2845622983/5000000000 : ℝ)|=(2845622983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s1_6 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5239969701/10000000000 : ℝ)*x 0 + (569124617/1000000000 : ℝ)*x 1 + (-891966823/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5239969701/10000000000 : ℝ)^8337 ≤ (5306874020881/12500000000000 : ℝ)^6289 := by
    have hnat : (5239969701 : ℕ)^8337*12500000000000^6289 ≤ 5306874020881^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239969701 10000000000 5306874020881 12500000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (569124617/1000000000 : ℝ)^8337 ≤ (47368665710097/100000000000000 : ℝ)^6289 := by
    have hnat : (569124617 : ℕ)^8337*100000000000000^6289 ≤ 47368665710097^6289*1000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      569124617 1000000000 47368665710097 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (891966823/5000000000 : ℝ)^8337 ≤ (1272042763901/12500000000000 : ℝ)^6289 := by
    have hnat : (891966823 : ℕ)^8337*12500000000000^6289 ≤ 1272042763901^6289*5000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      891966823 5000000000 1272042763901 12500000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5239969701/10000000000 : ℝ), (569124617/1000000000 : ℝ), (-891966823/5000000000 : ℝ)] ![(5306874020881/12500000000000 : ℝ), (47368665710097/100000000000000 : ℝ), (1272042763901/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5239969701/10000000000 : ℝ)|^8337 ≤ (5306874020881/12500000000000 : ℝ)^6289
        have hw : |(5239969701/10000000000 : ℝ)|=(5239969701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(569124617/1000000000 : ℝ)|^8337 ≤ (47368665710097/100000000000000 : ℝ)^6289
        have hw : |(569124617/1000000000 : ℝ)|=(569124617/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-891966823/5000000000 : ℝ)|^8337 ≤ (1272042763901/12500000000000 : ℝ)^6289
        have hw : |(-891966823/5000000000 : ℝ)|=(891966823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s1_7 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1079716923/2500000000 : ℝ)*x 0 + (315512483/625000000 : ℝ)*x 1 + (3696770613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079716923/2500000000 : ℝ)^8337 ≤ (16428535739721/50000000000000 : ℝ)^6289 := by
    have hnat : (1079716923 : ℕ)^8337*50000000000000^6289 ≤ 16428535739721^6289*2500000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079716923 2500000000 16428535739721 50000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (315512483/625000000 : ℝ)^8337 ≤ (10101911396877/25000000000000 : ℝ)^6289 := by
    have hnat : (315512483 : ℕ)^8337*25000000000000^6289 ≤ 10101911396877^6289*625000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315512483 625000000 10101911396877 25000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3696770613/10000000000 : ℝ)^8337 ≤ (26735282924541/100000000000000 : ℝ)^6289 := by
    have hnat : (3696770613 : ℕ)^8337*100000000000000^6289 ≤ 26735282924541^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3696770613 10000000000 26735282924541 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079716923/2500000000 : ℝ), (315512483/625000000 : ℝ), (3696770613/10000000000 : ℝ)] ![(16428535739721/50000000000000 : ℝ), (10101911396877/25000000000000 : ℝ), (26735282924541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079716923/2500000000 : ℝ)|^8337 ≤ (16428535739721/50000000000000 : ℝ)^6289
        have hw : |(1079716923/2500000000 : ℝ)|=(1079716923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(315512483/625000000 : ℝ)|^8337 ≤ (10101911396877/25000000000000 : ℝ)^6289
        have hw : |(315512483/625000000 : ℝ)|=(315512483/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3696770613/10000000000 : ℝ)|^8337 ≤ (26735282924541/100000000000000 : ℝ)^6289
        have hw : |(3696770613/10000000000 : ℝ)|=(3696770613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1144_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37378183/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27807/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (211/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5661/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5107/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27807/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (211/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27807/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (211/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27807/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (211/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27807/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (211/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27807/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (211/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27807/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (211/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base37 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
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
  have hpowlo : (211/50000 : ℝ) ^ (521/128 : ℝ) ≤ (4318267893/20000000000000000000 : ℝ) := by
    have hpowers : (211/50000 : ℝ)^521 ≤ (4318267893/20000000000000000000 : ℝ)^128 := by
      have hnat : (211 : ℕ)^521*20000000000000000000^128 ≤ 4318267893^128*50000^521 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        211 50000 4318267893 20000000000000000000 521 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (211/50000 : ℝ)) (X := (4318267893/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have hpowhi : (27807/100000 : ℝ) ^ (521/128 : ℝ) ≤ (109285773619175533/20000000000000000000 : ℝ) := by
    have hpowers : (27807/100000 : ℝ)^521 ≤ (109285773619175533/20000000000000000000 : ℝ)^128 := by
      have hnat : (27807 : ℕ)^521*20000000000000000000^128 ≤ 109285773619175533^128*100000^521 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27807 100000 109285773619175533 20000000000000000000 521 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27807/100000 : ℝ)) (X := (109285773619175533/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000000004318267893/10000000000000000000 : ℝ) ≤ (10000000001060919/10000000000000000 : ℝ) ^ (521/128 : ℝ) := by
    have hpowers : (10000000004318267893/10000000000000000000 : ℝ)^128 ≤ (10000000001060919/10000000000000000 : ℝ)^521 := by
      have hnat : (10000000004318267893 : ℕ)^128*10000000000000000^521 ≤ 10000000001060919^521*10000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000000004318267893 10000000000000000000 10000000001060919 10000000000000000 128 521 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000001060919/10000000000000000 : ℝ)) (X := (10000000004318267893/10000000000000000000 : ℝ)) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (10054642888968721713/10000000000000000000 : ℝ) ≤ (2002679432280823/2000000000000000 : ℝ) ^ (521/128 : ℝ) := by
    have hpowers : (10054642888968721713/10000000000000000000 : ℝ)^128 ≤ (2002679432280823/2000000000000000 : ℝ)^521 := by
      have hnat : (10054642888968721713 : ℕ)^128*2000000000000000^521 ≤ 2002679432280823^521*10000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10054642888968721713 10000000000000000000 2002679432280823 2000000000000000 128 521 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2002679432280823/2000000000000000 : ℝ)) (X := (10054642888968721713/10000000000000000000 : ℝ)) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (10109285773619175533/10000000000000000000 : ℝ) ≤ (10026794321747311/10000000000000000 : ℝ) ^ (521/128 : ℝ) := by
    have hpowers : (10109285773619175533/10000000000000000000 : ℝ)^128 ≤ (10026794321747311/10000000000000000 : ℝ)^521 := by
      have hnat : (10109285773619175533 : ℕ)^128*10000000000000000^521 ≤ 10026794321747311^521*10000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10109285773619175533 10000000000000000000 10026794321747311 10000000000000000 128 521 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10026794321747311/10000000000000000 : ℝ)) (X := (10109285773619175533/10000000000000000000 : ℝ)) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4318267893/20000000000000000000 : ℝ) ≤ ((273838692825723609391/273850000000000000000 : ℝ)+2*(3349290085799/684625000000000 : ℝ)*(211/50000 : ℝ))^(521/128 : ℝ) := by
    rw [show (273838692825723609391/273850000000000000000 : ℝ)+2*(3349290085799/684625000000000 : ℝ)*(211/50000 : ℝ)=(10000000001060919/10000000000000000 : ℝ) by norm_num, show 1+2*(4318267893/20000000000000000000 : ℝ)=(10000000004318267893/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(109285773619175533/20000000000000000000 : ℝ)+(4318267893/20000000000000000000 : ℝ) ≤ ((273838692825723609391/273850000000000000000 : ℝ)+(3349290085799/684625000000000 : ℝ)*((27807/100000 : ℝ)+(211/50000 : ℝ)))^(521/128 : ℝ) := by
    rw [show (273838692825723609391/273850000000000000000 : ℝ)+(3349290085799/684625000000000 : ℝ)*((27807/100000 : ℝ)+(211/50000 : ℝ))=(2002679432280823/2000000000000000 : ℝ) by norm_num, show 1+(109285773619175533/20000000000000000000 : ℝ)+(4318267893/20000000000000000000 : ℝ)=(10054642888968721713/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(109285773619175533/20000000000000000000 : ℝ) ≤ ((273838692825723609391/273850000000000000000 : ℝ)+2*(3349290085799/684625000000000 : ℝ)*(27807/100000 : ℝ))^(521/128 : ℝ) := by
    rw [show (273838692825723609391/273850000000000000000 : ℝ)+2*(3349290085799/684625000000000 : ℝ)*(27807/100000 : ℝ)=(10026794321747311/10000000000000000 : ℝ) by norm_num, show 1+2*(109285773619175533/20000000000000000000 : ℝ)=(10109285773619175533/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (273838692825723609391/273850000000000000000 : ℝ)*(X 1 0+X 2 0)+(3349290085799/684625000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (521/128 : ℝ)) (lo := (211/50000 : ℝ)) (hi := (27807/100000 : ℝ)) (c := (273838692825723609391/273850000000000000000 : ℝ)) (alpha := (3349290085799/684625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (273838692825723609391/273850000000000000000 : ℝ)*(X 0 1+X 2 1)+(3349290085799/684625000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (521/128 : ℝ)) (lo := (211/50000 : ℝ)) (hi := (27807/100000 : ℝ)) (c := (273838692825723609391/273850000000000000000 : ℝ)) (alpha := (3349290085799/684625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (273838692825723609391/273850000000000000000 : ℝ)*(X 0 2+X 1 2)+(3349290085799/684625000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (521/128 : ℝ)) (lo := (211/50000 : ℝ)) (hi := (27807/100000 : ℝ)) (c := (273838692825723609391/273850000000000000000 : ℝ)) (alpha := (3349290085799/684625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-523925437/2500000000 : ℝ)*X 0 0+(142524039/250000000 : ℝ)*X 0 1+(125067417/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5419009887/10000000000 : ℝ)*X 1 0+(-154530289/625000000 : ℝ)*X 1 1+(1250673987/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5419011853/10000000000 : ℝ)*X 2 0+(5002694199/10000000000 : ℝ)*X 2 1+(-618121071/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((107931811/250000000 : ℝ)*X 0 0+(3677436227/10000000000 : ℝ)*X 0 1+(126678957/250000000 : ℝ)*X 0 2+(107931811/250000000 : ℝ)*X 1 0+(3677436227/10000000000 : ℝ)*X 1 1+(126678957/250000000 : ℝ)*X 1 2+(107931811/250000000 : ℝ)*X 2 0+(3677436227/10000000000 : ℝ)*X 2 1+(126678957/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-419301093/2000000000 : ℝ)*X 0 0+(501222299/1000000000 : ℝ)*X 0 1+(227649853/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((163749051/312500000 : ℝ)*X 1 0+(-891967021/5000000000 : ℝ)*X 1 1+(2845622983/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5239969701/10000000000 : ℝ)*X 2 0+(569124617/1000000000 : ℝ)*X 2 1+(-891966823/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1079716923/2500000000 : ℝ)*X 0 0+(315512483/625000000 : ℝ)*X 0 1+(3696770613/10000000000 : ℝ)*X 0 2+(1079716923/2500000000 : ℝ)*X 1 0+(315512483/625000000 : ℝ)*X 1 1+(3696770613/10000000000 : ℝ)*X 1 2+(1079716923/2500000000 : ℝ)*X 2 0+(315512483/625000000 : ℝ)*X 2 1+(3696770613/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (40362653996155214974083081/8557812500000000000000000000000 : ℝ) := by norm_num
    linear_combination (233671987/50000000000000 : ℝ)*(base1) + (78127037/12500000000000 : ℝ)*(base19) + (603886599/50000000000000 : ℝ)*(base23) + (1297917/1000000000000 : ℝ)*(base37) + (41348063/100000000000000 : ℝ)*(upper3) + (1344805860053/125000000000 : ℝ)*(major0) + (1344805860053/125000000000 : ℝ)*(major1) + (1344805860053/125000000000 : ℝ)*(major2) + (286424296658329/20000000000000 : ℝ)*(sp0) + (1432119408610251/100000000000000 : ℝ)*(sp1) + (1432120738362041/100000000000000 : ℝ)*(sp2) + (719566675598263/100000000000000 : ℝ)*(sp3) + (930187567/100000000000000 : ℝ)*(sp4) + (1912508691/100000000000000 : ℝ)*(sp5) + (719567272733937/100000000000000 : ℝ)*(f.failure) + (716060973067619/50000000000000 : ℝ)*(f.sum) + (11854047127169/5477000000000000000000000000 : ℝ)*base66 + (26851466432688973/34231250000000000000000000000000 : ℝ)*base67 + (257479642748513973/34231250000000000000000000000000 : ℝ)*base69 + (128782207415651473/34231250000000000000000000000000 : ℝ)*base71 + (14600825338819/5477000000000000000000000000 : ℝ)*base74 + (208872172172370223/34231250000000000000000000000000 : ℝ)*base75 + (114589952044648527/34231250000000000000000000000000 : ℝ)*base78 + (8751055301232723/34231250000000000000000000000000 : ℝ)*base79 + (11292460073581/1369250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (7496471/2500000000000000000000 : ℝ)*base89 + (7496471/2500000000000000000000 : ℝ)*base91 + (7496471/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (96095629481806988395866003111/13692500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (46153697/50000000000000 : ℝ)*(base1) + (1551252463/100000000000000 : ℝ)*(base19) + (1596670583/100000000000000 : ℝ)*(base23) + (28069427/20000000000000 : ℝ)*(upper3) + (155792269/100000000000000 : ℝ)*(upper5) + (553165337350423/50000000000000 : ℝ)*(major0) + (553165337350423/50000000000000 : ℝ)*(major1) + (1106330674700847/100000000000000 : ℝ)*(major2) + (767273461/12500000000000 : ℝ)*(sp1) + (6899804323/100000000000000 : ℝ)*(sp2) + (1472703707228633/100000000000000 : ℝ)*(sp4) + (11505436917821/781250000000 : ℝ)*(sp5) + (368173779611583/25000000000000 : ℝ)*(sp6) + (739957408235667/100000000000000 : ℝ)*(sp7) + (369978750271531/50000000000000 : ℝ)*(f.failure) + (1472703614921239/100000000000000 : ℝ)*(f.sum) + (207521929053839/136925000000000000000000000000 : ℝ)*base65 + (22818286482636222393/13692500000000000000000000000000000 : ℝ)*base67 + (189204057361926454177/27385000000000000000000000000000000 : ℝ)*base69 + (90126903943938777607/13692500000000000000000000000000000 : ℝ)*base72 + (421878793133507/68462500000000000000000000000 : ℝ)*base73 + (188810931802731454177/27385000000000000000000000000000000 : ℝ)*base75 + (46837011419443922393/13692500000000000000000000000000000 : ℝ)*base77 + (11962604456928922393/13692500000000000000000000000000000 : ℝ)*base79 + (60952118260159/136925000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (10408173/1250000000000000000000 : ℝ)*base89 + (10408173/1250000000000000000000 : ℝ)*base91 + (2091827/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1144_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37378183/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27807/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (211/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5661/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5107/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1144_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1144_s2_0 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-268602917/1250000000 : ℝ)*x 0 + (5510424513/10000000000 : ℝ)*x 1 + (5159452647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268602917/1250000000 : ℝ)^8337 ≤ (1627958205271/12500000000000 : ℝ)^6289 := by
    have hnat : (268602917 : ℕ)^8337*12500000000000^6289 ≤ 1627958205271^6289*1250000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268602917 1250000000 1627958205271 12500000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5510424513/10000000000 : ℝ)^8337 ≤ (11345992935703/25000000000000 : ℝ)^6289 := by
    have hnat : (5510424513 : ℕ)^8337*25000000000000^6289 ≤ 11345992935703^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510424513 10000000000 11345992935703 25000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5159452647/10000000000 : ℝ)^8337 ≤ (20796181295969/50000000000000 : ℝ)^6289 := by
    have hnat : (5159452647 : ℕ)^8337*50000000000000^6289 ≤ 20796181295969^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5159452647 10000000000 20796181295969 50000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-268602917/1250000000 : ℝ), (5510424513/10000000000 : ℝ), (5159452647/10000000000 : ℝ)] ![(1627958205271/12500000000000 : ℝ), (11345992935703/25000000000000 : ℝ), (20796181295969/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-268602917/1250000000 : ℝ)|^8337 ≤ (1627958205271/12500000000000 : ℝ)^6289
        have hw : |(-268602917/1250000000 : ℝ)|=(268602917/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5510424513/10000000000 : ℝ)|^8337 ≤ (11345992935703/25000000000000 : ℝ)^6289
        have hw : |(5510424513/10000000000 : ℝ)|=(5510424513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5159452647/10000000000 : ℝ)|^8337 ≤ (20796181295969/50000000000000 : ℝ)^6289
        have hw : |(5159452647/10000000000 : ℝ)|=(5159452647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s2_1 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2686888667/5000000000 : ℝ)*x 0 + (-2331279309/10000000000 : ℝ)*x 1 + (644931843/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686888667/5000000000 : ℝ)^8337 ≤ (438981069167/1000000000000 : ℝ)^6289 := by
    have hnat : (2686888667 : ℕ)^8337*1000000000000^6289 ≤ 438981069167^6289*5000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686888667 5000000000 438981069167 1000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2331279309/10000000000 : ℝ)^8337 ≤ (1450950806103/10000000000000 : ℝ)^6289 := by
    have hnat : (2331279309 : ℕ)^8337*10000000000000^6289 ≤ 1450950806103^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2331279309 10000000000 1450950806103 10000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (644931843/1250000000 : ℝ)^8337 ≤ (10398096250417/25000000000000 : ℝ)^6289 := by
    have hnat : (644931843 : ℕ)^8337*25000000000000^6289 ≤ 10398096250417^6289*1250000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      644931843 1250000000 10398096250417 25000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686888667/5000000000 : ℝ), (-2331279309/10000000000 : ℝ), (644931843/1250000000 : ℝ)] ![(438981069167/1000000000000 : ℝ), (1450950806103/10000000000000 : ℝ), (10398096250417/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686888667/5000000000 : ℝ)|^8337 ≤ (438981069167/1000000000000 : ℝ)^6289
        have hw : |(2686888667/5000000000 : ℝ)|=(2686888667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2331279309/10000000000 : ℝ)|^8337 ≤ (1450950806103/10000000000000 : ℝ)^6289
        have hw : |(-2331279309/10000000000 : ℝ)|=(2331279309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(644931843/1250000000 : ℝ)|^8337 ≤ (10398096250417/25000000000000 : ℝ)^6289
        have hw : |(644931843/1250000000 : ℝ)|=(644931843/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s2_2 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1343444339/2500000000 : ℝ)*x 0 + (2579727279/5000000000 : ℝ)*x 1 + (-2331279521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1343444339/2500000000 : ℝ)^8337 ≤ (43898107154941/100000000000000 : ℝ)^6289 := by
    have hnat : (1343444339 : ℕ)^8337*100000000000000^6289 ≤ 43898107154941^6289*2500000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343444339 2500000000 43898107154941 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2579727279/5000000000 : ℝ)^8337 ≤ (41592383013967/100000000000000 : ℝ)^6289 := by
    have hnat : (2579727279 : ℕ)^8337*100000000000000^6289 ≤ 41592383013967^6289*5000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2579727279 5000000000 41592383013967 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2331279521/10000000000 : ℝ)^8337 ≤ (14509509810161/100000000000000 : ℝ)^6289 := by
    have hnat : (2331279521 : ℕ)^8337*100000000000000^6289 ≤ 14509509810161^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2331279521 10000000000 14509509810161 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1343444339/2500000000 : ℝ), (2579727279/5000000000 : ℝ), (-2331279521/10000000000 : ℝ)] ![(43898107154941/100000000000000 : ℝ), (41592383013967/100000000000000 : ℝ), (14509509810161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1343444339/2500000000 : ℝ)|^8337 ≤ (43898107154941/100000000000000 : ℝ)^6289
        have hw : |(1343444339/2500000000 : ℝ)|=(1343444339/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2579727279/5000000000 : ℝ)|^8337 ≤ (41592383013967/100000000000000 : ℝ)^6289
        have hw : |(2579727279/5000000000 : ℝ)|=(2579727279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2331279521/10000000000 : ℝ)|^8337 ≤ (14509509810161/100000000000000 : ℝ)^6289
        have hw : |(-2331279521/10000000000 : ℝ)|=(2331279521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s2_3 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (544215097/1250000000 : ℝ)*x 0 + (1004584533/2500000000 : ℝ)*x 1 + (147401773/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544215097/1250000000 : ℝ)^8337 ≤ (16604517487861/50000000000000 : ℝ)^6289 := by
    have hnat : (544215097 : ℕ)^8337*50000000000000^6289 ≤ 16604517487861^6289*1250000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544215097 1250000000 16604517487861 50000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1004584533/2500000000 : ℝ)^8337 ≤ (3732630809321/12500000000000 : ℝ)^6289 := by
    have hnat : (1004584533 : ℕ)^8337*12500000000000^6289 ≤ 3732630809321^6289*2500000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004584533 2500000000 3732630809321 12500000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (147401773/312500000 : ℝ)^8337 ≤ (4616239816953/12500000000000 : ℝ)^6289 := by
    have hnat : (147401773 : ℕ)^8337*12500000000000^6289 ≤ 4616239816953^6289*312500000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147401773 312500000 4616239816953 12500000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(544215097/1250000000 : ℝ), (1004584533/2500000000 : ℝ), (147401773/312500000 : ℝ)] ![(16604517487861/50000000000000 : ℝ), (3732630809321/12500000000000 : ℝ), (4616239816953/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(544215097/1250000000 : ℝ)|^8337 ≤ (16604517487861/50000000000000 : ℝ)^6289
        have hw : |(544215097/1250000000 : ℝ)|=(544215097/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1004584533/2500000000 : ℝ)|^8337 ≤ (3732630809321/12500000000000 : ℝ)^6289
        have hw : |(1004584533/2500000000 : ℝ)|=(1004584533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(147401773/312500000 : ℝ)|^8337 ≤ (4616239816953/12500000000000 : ℝ)^6289
        have hw : |(147401773/312500000 : ℝ)|=(147401773/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s2_4 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2148925429/10000000000 : ℝ)*x 0 + (5161869549/10000000000 : ℝ)*x 1 + (5507983371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2148925429/10000000000 : ℝ)^8337 ≤ (13024485918269/100000000000000 : ℝ)^6289 := by
    have hnat : (2148925429 : ℕ)^8337*100000000000000^6289 ≤ 13024485918269^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148925429 10000000000 13024485918269 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5161869549/10000000000 : ℝ)^8337 ≤ (2080909647207/5000000000000 : ℝ)^6289 := by
    have hnat : (5161869549 : ℕ)^8337*5000000000000^6289 ≤ 2080909647207^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5161869549 10000000000 2080909647207 5000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5507983371/10000000000 : ℝ)^8337 ≤ (22678660560031/50000000000000 : ℝ)^6289 := by
    have hnat : (5507983371 : ℕ)^8337*50000000000000^6289 ≤ 22678660560031^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5507983371 10000000000 22678660560031 50000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2148925429/10000000000 : ℝ), (5161869549/10000000000 : ℝ), (5507983371/10000000000 : ℝ)] ![(13024485918269/100000000000000 : ℝ), (2080909647207/5000000000000 : ℝ), (22678660560031/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2148925429/10000000000 : ℝ)|^8337 ≤ (13024485918269/100000000000000 : ℝ)^6289
        have hw : |(-2148925429/10000000000 : ℝ)|=(2148925429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5161869549/10000000000 : ℝ)|^8337 ≤ (2080909647207/5000000000000 : ℝ)^6289
        have hw : |(5161869549/10000000000 : ℝ)|=(5161869549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5507983371/10000000000 : ℝ)|^8337 ≤ (22678660560031/50000000000000 : ℝ)^6289
        have hw : |(5507983371/10000000000 : ℝ)|=(5507983371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s2_5 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2642357323/5000000000 : ℝ)*x 0 + (-495687141/2500000000 : ℝ)*x 1 + (2753992033/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642357323/5000000000 : ℝ)^8337 ≤ (42936246260327/100000000000000 : ℝ)^6289 := by
    have hnat : (2642357323 : ℕ)^8337*100000000000000^6289 ≤ 42936246260327^6289*5000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642357323 5000000000 42936246260327 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (495687141/2500000000 : ℝ)^8337 ≤ (11706425029217/100000000000000 : ℝ)^6289 := by
    have hnat : (495687141 : ℕ)^8337*100000000000000^6289 ≤ 11706425029217^6289*2500000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      495687141 2500000000 11706425029217 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2753992033/5000000000 : ℝ)^8337 ≤ (22678664353511/50000000000000 : ℝ)^6289 := by
    have hnat : (2753992033 : ℕ)^8337*50000000000000^6289 ≤ 22678664353511^6289*5000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2753992033 5000000000 22678664353511 50000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642357323/5000000000 : ℝ), (-495687141/2500000000 : ℝ), (2753992033/5000000000 : ℝ)] ![(42936246260327/100000000000000 : ℝ), (11706425029217/100000000000000 : ℝ), (22678664353511/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642357323/5000000000 : ℝ)|^8337 ≤ (42936246260327/100000000000000 : ℝ)^6289
        have hw : |(2642357323/5000000000 : ℝ)|=(2642357323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-495687141/2500000000 : ℝ)|^8337 ≤ (11706425029217/100000000000000 : ℝ)^6289
        have hw : |(-495687141/2500000000 : ℝ)|=(495687141/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2753992033/5000000000 : ℝ)|^8337 ≤ (22678664353511/50000000000000 : ℝ)^6289
        have hw : |(2753992033/5000000000 : ℝ)|=(2753992033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s2_6 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5284713107/10000000000 : ℝ)*x 0 + (1101596769/2000000000 : ℝ)*x 1 + (-1982750989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284713107/10000000000 : ℝ)^8337 ≤ (10734057421181/25000000000000 : ℝ)^6289 := by
    have hnat : (5284713107 : ℕ)^8337*25000000000000^6289 ≤ 10734057421181^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284713107 10000000000 10734057421181 25000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1101596769/2000000000 : ℝ)^8337 ≤ (22678663147239/50000000000000 : ℝ)^6289 := by
    have hnat : (1101596769 : ℕ)^8337*50000000000000^6289 ≤ 22678663147239^6289*2000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101596769 2000000000 22678663147239 50000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1982750989/10000000000 : ℝ)^8337 ≤ (11706444009237/100000000000000 : ℝ)^6289 := by
    have hnat : (1982750989 : ℕ)^8337*100000000000000^6289 ≤ 11706444009237^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1982750989 10000000000 11706444009237 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284713107/10000000000 : ℝ), (1101596769/2000000000 : ℝ), (-1982750989/10000000000 : ℝ)] ![(10734057421181/25000000000000 : ℝ), (22678663147239/50000000000000 : ℝ), (11706444009237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284713107/10000000000 : ℝ)|^8337 ≤ (10734057421181/25000000000000 : ℝ)^6289
        have hw : |(5284713107/10000000000 : ℝ)|=(5284713107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1101596769/2000000000 : ℝ)|^8337 ≤ (22678663147239/50000000000000 : ℝ)^6289
        have hw : |(1101596769/2000000000 : ℝ)|=(1101596769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1982750989/10000000000 : ℝ)|^8337 ≤ (11706444009237/100000000000000 : ℝ)^6289
        have hw : |(-1982750989/10000000000 : ℝ)|=(1982750989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s2_7 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2176961507/5000000000 : ℝ)*x 0 + (2356024141/5000000000 : ℝ)*x 1 + (4023194833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2176961507/5000000000 : ℝ)^8337 ≤ (16605539979913/50000000000000 : ℝ)^6289 := by
    have hnat : (2176961507 : ℕ)^8337*50000000000000^6289 ≤ 16605539979913^6289*5000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176961507 5000000000 16605539979913 50000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2356024141/5000000000 : ℝ)^8337 ≤ (922000501647/2500000000000 : ℝ)^6289 := by
    have hnat : (2356024141 : ℕ)^8337*2500000000000^6289 ≤ 922000501647^6289*5000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2356024141 5000000000 922000501647 2500000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4023194833/10000000000 : ℝ)^8337 ≤ (598177999153/2000000000000 : ℝ)^6289 := by
    have hnat : (4023194833 : ℕ)^8337*2000000000000^6289 ≤ 598177999153^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4023194833 10000000000 598177999153 2000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2176961507/5000000000 : ℝ), (2356024141/5000000000 : ℝ), (4023194833/10000000000 : ℝ)] ![(16605539979913/50000000000000 : ℝ), (922000501647/2500000000000 : ℝ), (598177999153/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2176961507/5000000000 : ℝ)|^8337 ≤ (16605539979913/50000000000000 : ℝ)^6289
        have hw : |(2176961507/5000000000 : ℝ)|=(2176961507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2356024141/5000000000 : ℝ)|^8337 ≤ (922000501647/2500000000000 : ℝ)^6289
        have hw : |(2356024141/5000000000 : ℝ)|=(2356024141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4023194833/10000000000 : ℝ)|^8337 ≤ (598177999153/2000000000000 : ℝ)^6289
        have hw : |(4023194833/10000000000 : ℝ)|=(4023194833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1144_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37378183/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5107/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5661/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9079/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1031/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5107/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5661/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5107/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5661/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5107/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5661/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5107/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5661/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5107/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5661/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5107/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5661/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5661/100000 : ℝ) ^ (521/128 : ℝ) ≤ (209809634963349/25000000000000000000 : ℝ) := by
    have hpowers : (5661/100000 : ℝ)^521 ≤ (209809634963349/25000000000000000000 : ℝ)^128 := by
      have hnat : (5661 : ℕ)^521*25000000000000000000^128 ≤ 209809634963349^128*100000^521 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5661 100000 209809634963349 25000000000000000000 521 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5661/100000 : ℝ)) (X := (209809634963349/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have hpowhi : (5107/25000 : ℝ) ^ (521/128 : ℝ) ≤ (155741248449128563/100000000000000000000 : ℝ) := by
    have hpowers : (5107/25000 : ℝ)^521 ≤ (155741248449128563/100000000000000000000 : ℝ)^128 := by
      have hnat : (5107 : ℕ)^521*100000000000000000000^128 ≤ 155741248449128563^128*25000^521 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5107 25000 155741248449128563 100000000000000000000 521 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5107/25000 : ℝ)) (X := (155741248449128563/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500209809634963349/12500000000000000000 : ℝ) ≤ (10000041236795803/10000000000000000 : ℝ) ^ (521/128 : ℝ) := by
    have hpowers : (12500209809634963349/12500000000000000000 : ℝ)^128 ≤ (10000041236795803/10000000000000000 : ℝ)^521 := by
      have hnat : (12500209809634963349 : ℕ)^128*10000000000000000^521 ≤ 10000041236795803^521*12500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500209809634963349 12500000000000000000 10000041236795803 10000000000000000 128 521 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000041236795803/10000000000000000 : ℝ)) (X := (12500209809634963349/12500000000000000000 : ℝ)) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100156580486988981959/100000000000000000000 : ℝ) ≤ (25009611553273/25000000000000 : ℝ) ^ (521/128 : ℝ) := by
    have hpowers : (100156580486988981959/100000000000000000000 : ℝ)^128 ≤ (25009611553273/25000000000000 : ℝ)^521 := by
      have hnat : (100156580486988981959 : ℕ)^128*25000000000000^521 ≤ 25009611553273^521*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100156580486988981959 100000000000000000000 25009611553273 25000000000000 128 521 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (25009611553273/25000000000000 : ℝ)) (X := (100156580486988981959/100000000000000000000 : ℝ)) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50155741248449128563/50000000000000000000 : ℝ) ≤ (10007648005822597/10000000000000000 : ℝ) ^ (521/128 : ℝ) := by
    have hpowers : (50155741248449128563/50000000000000000000 : ℝ)^128 ≤ (10007648005822597/10000000000000000 : ℝ)^521 := by
      have hnat : (50155741248449128563 : ℕ)^128*10000000000000000^521 ≤ 10007648005822597^521*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50155741248449128563 50000000000000000000 10007648005822597 10000000000000000 128 521 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007648005822597/10000000000000000 : ℝ)) (X := (50155741248449128563/50000000000000000000 : ℝ)) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(209809634963349/25000000000000000000 : ℝ) ≤ ((147627547024302942067/147670000000000000000 : ℝ)+2*(3803384513397/1476700000000000 : ℝ)*(5661/100000 : ℝ))^(521/128 : ℝ) := by
    rw [show (147627547024302942067/147670000000000000000 : ℝ)+2*(3803384513397/1476700000000000 : ℝ)*(5661/100000 : ℝ)=(10000041236795803/10000000000000000 : ℝ) by norm_num, show 1+2*(209809634963349/25000000000000000000 : ℝ)=(12500209809634963349/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(155741248449128563/100000000000000000000 : ℝ)+(209809634963349/25000000000000000000 : ℝ) ≤ ((147627547024302942067/147670000000000000000 : ℝ)+(3803384513397/1476700000000000 : ℝ)*((5107/25000 : ℝ)+(5661/100000 : ℝ)))^(521/128 : ℝ) := by
    rw [show (147627547024302942067/147670000000000000000 : ℝ)+(3803384513397/1476700000000000 : ℝ)*((5107/25000 : ℝ)+(5661/100000 : ℝ))=(25009611553273/25000000000000 : ℝ) by norm_num, show 1+(155741248449128563/100000000000000000000 : ℝ)+(209809634963349/25000000000000000000 : ℝ)=(100156580486988981959/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(155741248449128563/100000000000000000000 : ℝ) ≤ ((147627547024302942067/147670000000000000000 : ℝ)+2*(3803384513397/1476700000000000 : ℝ)*(5107/25000 : ℝ))^(521/128 : ℝ) := by
    rw [show (147627547024302942067/147670000000000000000 : ℝ)+2*(3803384513397/1476700000000000 : ℝ)*(5107/25000 : ℝ)=(10007648005822597/10000000000000000 : ℝ) by norm_num, show 1+2*(155741248449128563/100000000000000000000 : ℝ)=(50155741248449128563/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (147627547024302942067/147670000000000000000 : ℝ)*(X 1 0+X 2 0)+(3803384513397/1476700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (521/128 : ℝ)) (lo := (5661/100000 : ℝ)) (hi := (5107/25000 : ℝ)) (c := (147627547024302942067/147670000000000000000 : ℝ)) (alpha := (3803384513397/1476700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (147627547024302942067/147670000000000000000 : ℝ)*(X 0 1+X 2 1)+(3803384513397/1476700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (521/128 : ℝ)) (lo := (5661/100000 : ℝ)) (hi := (5107/25000 : ℝ)) (c := (147627547024302942067/147670000000000000000 : ℝ)) (alpha := (3803384513397/1476700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (147627547024302942067/147670000000000000000 : ℝ)*(X 0 2+X 1 2)+(3803384513397/1476700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (521/128 : ℝ)) (lo := (5661/100000 : ℝ)) (hi := (5107/25000 : ℝ)) (c := (147627547024302942067/147670000000000000000 : ℝ)) (alpha := (3803384513397/1476700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-268602917/1250000000 : ℝ)*X 0 0+(5510424513/10000000000 : ℝ)*X 0 1+(5159452647/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2686888667/5000000000 : ℝ)*X 1 0+(-2331279309/10000000000 : ℝ)*X 1 1+(644931843/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1343444339/2500000000 : ℝ)*X 2 0+(2579727279/5000000000 : ℝ)*X 2 1+(-2331279521/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((544215097/1250000000 : ℝ)*X 0 0+(1004584533/2500000000 : ℝ)*X 0 1+(147401773/312500000 : ℝ)*X 0 2+(544215097/1250000000 : ℝ)*X 1 0+(1004584533/2500000000 : ℝ)*X 1 1+(147401773/312500000 : ℝ)*X 1 2+(544215097/1250000000 : ℝ)*X 2 0+(1004584533/2500000000 : ℝ)*X 2 1+(147401773/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2148925429/10000000000 : ℝ)*X 0 0+(5161869549/10000000000 : ℝ)*X 0 1+(5507983371/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2642357323/5000000000 : ℝ)*X 1 0+(-495687141/2500000000 : ℝ)*X 1 1+(2753992033/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5284713107/10000000000 : ℝ)*X 2 0+(1101596769/2000000000 : ℝ)*X 2 1+(-1982750989/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2176961507/5000000000 : ℝ)*X 0 0+(2356024141/5000000000 : ℝ)*X 0 1+(4023194833/10000000000 : ℝ)*X 0 2+(2176961507/5000000000 : ℝ)*X 1 0+(2356024141/5000000000 : ℝ)*X 1 1+(4023194833/10000000000 : ℝ)*X 1 2+(2176961507/5000000000 : ℝ)*X 2 0+(2356024141/5000000000 : ℝ)*X 2 1+(4023194833/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (78907703216216503892533789377/7383500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (635046071/50000000000000 : ℝ)*(base19) + (956218997/100000000000000 : ℝ)*(base23) + (79093621/20000000000000 : ℝ)*(upper3) + (8746843/5000000000000 : ℝ)*(upper4) + (14970407/100000000000000 : ℝ)*(upper5) + (2140450255891977/100000000000000 : ℝ)*(major0) + (2140450255891977/100000000000000 : ℝ)*(major1) + (1070225127945989/50000000000000 : ℝ)*(major2) + (1424629669966241/50000000000000 : ℝ)*(sp0) + (56985630118951/2000000000000 : ℝ)*(sp1) + (356160227477587/12500000000000 : ℝ)*(sp2) + (1431607401940679/100000000000000 : ℝ)*(sp3) + (2343610721/10000000000000 : ℝ)*(sp4) + (4988784583/50000000000000 : ℝ)*(sp7) + (286323475901969/20000000000000 : ℝ)*(f.failure) + (712320694009923/25000000000000 : ℝ)*(f.sum) + (19238956075703/29534000000000000000000000000 : ℝ)*base65 + (49464689876435696459/14767000000000000000000000000000000 : ℝ)*base67 + (61804347501234469263/7383500000000000000000000000000000 : ℝ)*base69 + (44935438766408303541/14767000000000000000000000000000000 : ℝ)*base72 + (123224882823367/29534000000000000000000000000 : ℝ)*base73 + (14639187199971530737/7383500000000000000000000000000000 : ℝ)*base76 + (12269122516040003541/14767000000000000000000000000000000 : ℝ)*base78 + (272007123049708003541/14767000000000000000000000000000000 : ℝ)*base80 + (259776266478859/73835000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (2342327/500000000000000000000 : ℝ)*base89 + (2342327/500000000000000000000 : ℝ)*base91 + (2657673/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23956315294136709542817062733/7383500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (60698527/20000000000000 : ℝ)*(base19) + (193551349/50000000000000 : ℝ)*(upper2) + (128846461/100000000000000 : ℝ)*(upper3) + (682993/4000000000000 : ℝ)*(lower4) + (1085228394539067/50000000000000 : ℝ)*(major0) + (1085228394539067/50000000000000 : ℝ)*(major1) + (434091357815627/20000000000000 : ℝ)*(major2) + (3743871389/50000000000000 : ℝ)*(sp0) + (2692771999/20000000000000 : ℝ)*(sp1) + (169480859/20000000000000 : ℝ)*(sp3) + (1444609526147823/50000000000000 : ℝ)*(sp4) + (1444606386342897/50000000000000 : ℝ)*(sp5) + (361153317504803/12500000000000 : ℝ)*(sp6) + (181460760320133/12500000000000 : ℝ)*(sp7) + (1451686929965359/100000000000000 : ℝ)*(f.failure) + (361153317504803/12500000000000 : ℝ)*(f.sum) + (634480913125787/147670000000000000000000000000 : ℝ)*base66 + (24257738265227018511/7383500000000000000000000000000000 : ℝ)*base68 + (28891461768894641009/2953400000000000000000000000000000 : ℝ)*base69 + (45327163280646018511/7383500000000000000000000000000000 : ℝ)*base72 + (33687798593597/147670000000000000000000000000 : ℝ)*base74 + (18317732604077841009/2953400000000000000000000000000000 : ℝ)*base75 + (16043368586534868511/7383500000000000000000000000000000 : ℝ)*base78 + (28203594997748868511/7383500000000000000000000000000000 : ℝ)*base80 + (127718997451519/36917500000000000000000000000 : ℝ)*base81 + (22362697/2500000000000000000000 : ℝ)*base89 + (22362697/2500000000000000000000 : ℝ)*base91 + (2637303/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1144_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37378183/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5107/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5661/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9079/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1031/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1144_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1144_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37378183/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9079/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1031/6250 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1144_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1144_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1144_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37378183/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9079/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1031/6250 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1144_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

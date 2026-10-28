-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1212_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:07:18.628895+00:00
-- url     : https://prove2.me/submissions/ee9a5d34-5a98-4231-8401-a6ef21f2e85b

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
theorem support_rectangle_w1212_s0_0 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-116865759/625000000 : ℝ)*x 0 + (6038292473/10000000000 : ℝ)*x 1 + (299328813/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (116865759/625000000 : ℝ)^8405 ≤ (10894552284937/100000000000000 : ℝ)^6357 := by
    have hnat : (116865759 : ℕ)^8405*100000000000000^6357 ≤ 10894552284937^6357*625000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116865759 625000000 10894552284937 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6038292473/10000000000 : ℝ)^8405 ≤ (1603919147927/3125000000000 : ℝ)^6357 := by
    have hnat : (6038292473 : ℕ)^8405*3125000000000^6357 ≤ 1603919147927^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6038292473 10000000000 1603919147927 3125000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (299328813/625000000 : ℝ)^8405 ≤ (295156523159/781250000000 : ℝ)^6357 := by
    have hnat : (299328813 : ℕ)^8405*781250000000^6357 ≤ 295156523159^6357*625000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299328813 625000000 295156523159 781250000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-116865759/625000000 : ℝ), (6038292473/10000000000 : ℝ), (299328813/625000000 : ℝ)] ![(10894552284937/100000000000000 : ℝ), (1603919147927/3125000000000 : ℝ), (295156523159/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-116865759/625000000 : ℝ)|^8405 ≤ (10894552284937/100000000000000 : ℝ)^6357
        have hw : |(-116865759/625000000 : ℝ)|=(116865759/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6038292473/10000000000 : ℝ)|^8405 ≤ (1603919147927/3125000000000 : ℝ)^6357
        have hw : |(6038292473/10000000000 : ℝ)|=(6038292473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(299328813/625000000 : ℝ)|^8405 ≤ (295156523159/781250000000 : ℝ)^6357
        have hw : |(299328813/625000000 : ℝ)|=(299328813/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1212_s0_1 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5512849689/10000000000 : ℝ)*x 0 + (-516942243/2000000000 : ℝ)*x 1 + (4789260983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5512849689/10000000000 : ℝ)^8405 ≤ (4550474838781/10000000000000 : ℝ)^6357 := by
    have hnat : (5512849689 : ℕ)^8405*10000000000000^6357 ≤ 4550474838781^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5512849689 10000000000 4550474838781 10000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (516942243/2000000000 : ℝ)^8405 ≤ (8357608450547/50000000000000 : ℝ)^6357 := by
    have hnat : (516942243 : ℕ)^8405*50000000000000^6357 ≤ 8357608450547^6357*2000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516942243 2000000000 8357608450547 50000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4789260983/10000000000 : ℝ)^8405 ≤ (7556006940721/20000000000000 : ℝ)^6357 := by
    have hnat : (4789260983 : ℕ)^8405*20000000000000^6357 ≤ 7556006940721^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4789260983 10000000000 7556006940721 20000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5512849689/10000000000 : ℝ), (-516942243/2000000000 : ℝ), (4789260983/10000000000 : ℝ)] ![(4550474838781/10000000000000 : ℝ), (8357608450547/50000000000000 : ℝ), (7556006940721/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5512849689/10000000000 : ℝ)|^8405 ≤ (4550474838781/10000000000000 : ℝ)^6357
        have hw : |(5512849689/10000000000 : ℝ)|=(5512849689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-516942243/2000000000 : ℝ)|^8405 ≤ (8357608450547/50000000000000 : ℝ)^6357
        have hw : |(-516942243/2000000000 : ℝ)|=(516942243/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4789260983/10000000000 : ℝ)|^8405 ≤ (7556006940721/20000000000000 : ℝ)^6357
        have hw : |(4789260983/10000000000 : ℝ)|=(4789260983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1212_s0_2 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (689106209/1250000000 : ℝ)*x 0 + (4789261001/10000000000 : ℝ)*x 1 + (-1292355607/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (689106209/1250000000 : ℝ)^8405 ≤ (1137618705057/2500000000000 : ℝ)^6357 := by
    have hnat : (689106209 : ℕ)^8405*2500000000000^6357 ≤ 1137618705057^6357*1250000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689106209 1250000000 1137618705057 2500000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4789261001/10000000000 : ℝ)^8405 ≤ (18890017445671/50000000000000 : ℝ)^6357 := by
    have hnat : (4789261001 : ℕ)^8405*50000000000000^6357 ≤ 18890017445671^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4789261001 10000000000 18890017445671 50000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1292355607/5000000000 : ℝ)^8405 ≤ (16715216892543/100000000000000 : ℝ)^6357 := by
    have hnat : (1292355607 : ℕ)^8405*100000000000000^6357 ≤ 16715216892543^6357*5000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292355607 5000000000 16715216892543 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(689106209/1250000000 : ℝ), (4789261001/10000000000 : ℝ), (-1292355607/5000000000 : ℝ)] ![(1137618705057/2500000000000 : ℝ), (18890017445671/50000000000000 : ℝ), (16715216892543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(689106209/1250000000 : ℝ)|^8405 ≤ (1137618705057/2500000000000 : ℝ)^6357
        have hw : |(689106209/1250000000 : ℝ)|=(689106209/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4789261001/10000000000 : ℝ)|^8405 ≤ (18890017445671/50000000000000 : ℝ)^6357
        have hw : |(4789261001/10000000000 : ℝ)|=(4789261001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1292355607/5000000000 : ℝ)|^8405 ≤ (16715216892543/100000000000000 : ℝ)^6357
        have hw : |(-1292355607/5000000000 : ℝ)|=(1292355607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1212_s0_3 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (419538791/1000000000 : ℝ)*x 0 + (623611007/2000000000 : ℝ)*x 1 + (1409283603/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (419538791/1000000000 : ℝ)^8405 ≤ (31713390522119/100000000000000 : ℝ)^6357 := by
    have hnat : (419538791 : ℕ)^8405*100000000000000^6357 ≤ 31713390522119^6357*1000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419538791 1000000000 31713390522119 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (623611007/2000000000 : ℝ)^8405 ≤ (21420572530909/100000000000000 : ℝ)^6357 := by
    have hnat : (623611007 : ℕ)^8405*100000000000000^6357 ≤ 21420572530909^6357*2000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      623611007 2000000000 21420572530909 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1409283603/2500000000 : ℝ)^8405 ≤ (9373207384443/20000000000000 : ℝ)^6357 := by
    have hnat : (1409283603 : ℕ)^8405*20000000000000^6357 ≤ 9373207384443^6357*2500000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1409283603 2500000000 9373207384443 20000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(419538791/1000000000 : ℝ), (623611007/2000000000 : ℝ), (1409283603/2500000000 : ℝ)] ![(31713390522119/100000000000000 : ℝ), (21420572530909/100000000000000 : ℝ), (9373207384443/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(419538791/1000000000 : ℝ)|^8405 ≤ (31713390522119/100000000000000 : ℝ)^6357
        have hw : |(419538791/1000000000 : ℝ)|=(419538791/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(623611007/2000000000 : ℝ)|^8405 ≤ (21420572530909/100000000000000 : ℝ)^6357
        have hw : |(623611007/2000000000 : ℝ)|=(623611007/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1409283603/2500000000 : ℝ)|^8405 ≤ (9373207384443/20000000000000 : ℝ)^6357
        have hw : |(1409283603/2500000000 : ℝ)|=(1409283603/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1212_s0_4 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1874795383/10000000000 : ℝ)*x 0 + (301340317/625000000 : ℝ)*x 1 + (300248599/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1874795383/10000000000 : ℝ)^8405 ≤ (10932648692871/100000000000000 : ℝ)^6357 := by
    have hnat : (1874795383 : ℕ)^8405*100000000000000^6357 ≤ 10932648692871^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1874795383 10000000000 10932648692871 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (301340317/625000000 : ℝ)^8405 ≤ (9529018434087/25000000000000 : ℝ)^6357 := by
    have hnat : (301340317 : ℕ)^8405*25000000000000^6357 ≤ 9529018434087^6357*625000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      301340317 625000000 9529018434087 25000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (300248599/500000000 : ℝ)^8405 ≤ (5095127756089/10000000000000 : ℝ)^6357 := by
    have hnat : (300248599 : ℕ)^8405*10000000000000^6357 ≤ 5095127756089^6357*500000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300248599 500000000 5095127756089 10000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1874795383/10000000000 : ℝ), (301340317/625000000 : ℝ), (300248599/500000000 : ℝ)] ![(10932648692871/100000000000000 : ℝ), (9529018434087/25000000000000 : ℝ), (5095127756089/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1874795383/10000000000 : ℝ)|^8405 ≤ (10932648692871/100000000000000 : ℝ)^6357
        have hw : |(-1874795383/10000000000 : ℝ)|=(1874795383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(301340317/625000000 : ℝ)|^8405 ≤ (9529018434087/25000000000000 : ℝ)^6357
        have hw : |(301340317/625000000 : ℝ)|=(301340317/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(300248599/500000000 : ℝ)|^8405 ≤ (5095127756089/10000000000000 : ℝ)^6357
        have hw : |(300248599/500000000 : ℝ)|=(300248599/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1212_s0_5 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5173136121/10000000000 : ℝ)*x 0 + (-1368998617/10000000000 : ℝ)*x 1 + (6004973693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5173136121/10000000000 : ℝ)^8405 ≤ (41834594539363/100000000000000 : ℝ)^6357 := by
    have hnat : (5173136121 : ℕ)^8405*100000000000000^6357 ≤ 41834594539363^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173136121 10000000000 41834594539363 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1368998617/10000000000 : ℝ)^8405 ≤ (225440895689/3125000000000 : ℝ)^6357 := by
    have hnat : (1368998617 : ℕ)^8405*3125000000000^6357 ≤ 225440895689^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368998617 10000000000 225440895689 3125000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6004973693/10000000000 : ℝ)^8405 ≤ (1592228024311/3125000000000 : ℝ)^6357 := by
    have hnat : (6004973693 : ℕ)^8405*3125000000000^6357 ≤ 1592228024311^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6004973693 10000000000 1592228024311 3125000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5173136121/10000000000 : ℝ), (-1368998617/10000000000 : ℝ), (6004973693/10000000000 : ℝ)] ![(41834594539363/100000000000000 : ℝ), (225440895689/3125000000000 : ℝ), (1592228024311/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5173136121/10000000000 : ℝ)|^8405 ≤ (41834594539363/100000000000000 : ℝ)^6357
        have hw : |(5173136121/10000000000 : ℝ)|=(5173136121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1368998617/10000000000 : ℝ)|^8405 ≤ (225440895689/3125000000000 : ℝ)^6357
        have hw : |(-1368998617/10000000000 : ℝ)|=(1368998617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6004973693/10000000000 : ℝ)|^8405 ≤ (1592228024311/3125000000000 : ℝ)^6357
        have hw : |(6004973693/10000000000 : ℝ)|=(6004973693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1212_s0_6 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5173136973/10000000000 : ℝ)*x 0 + (375310779/625000000 : ℝ)*x 1 + (-1368999289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5173136973/10000000000 : ℝ)^8405 ≤ (261466272807/625000000000 : ℝ)^6357 := by
    have hnat : (5173136973 : ℕ)^8405*625000000000^6357 ≤ 261466272807^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173136973 10000000000 261466272807 625000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (375310779/625000000 : ℝ)^8405 ≤ (2547564149529/5000000000000 : ℝ)^6357 := by
    have hnat : (375310779 : ℕ)^8405*5000000000000^6357 ≤ 2547564149529^6357*625000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375310779 625000000 2547564149529 5000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1368999289/10000000000 : ℝ)^8405 ≤ (7214113344081/100000000000000 : ℝ)^6357 := by
    have hnat : (1368999289 : ℕ)^8405*100000000000000^6357 ≤ 7214113344081^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368999289 10000000000 7214113344081 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5173136973/10000000000 : ℝ), (375310779/625000000 : ℝ), (-1368999289/10000000000 : ℝ)] ![(261466272807/625000000000 : ℝ), (2547564149529/5000000000000 : ℝ), (7214113344081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5173136973/10000000000 : ℝ)|^8405 ≤ (261466272807/625000000000 : ℝ)^6357
        have hw : |(5173136973/10000000000 : ℝ)|=(5173136973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(375310779/625000000 : ℝ)|^8405 ≤ (2547564149529/5000000000000 : ℝ)^6357
        have hw : |(375310779/625000000 : ℝ)|=(375310779/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1368999289/10000000000 : ℝ)|^8405 ≤ (7214113344081/100000000000000 : ℝ)^6357
        have hw : |(-1368999289/10000000000 : ℝ)|=(1368999289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1212_s0_7 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4205356589/10000000000 : ℝ)*x 0 + (10883259/19531250 : ℝ)*x 1 + (3185251957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4205356589/10000000000 : ℝ)^8405 ≤ (31813059447469/100000000000000 : ℝ)^6357 := by
    have hnat : (4205356589 : ℕ)^8405*100000000000000^6357 ≤ 31813059447469^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4205356589 10000000000 31813059447469 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10883259/19531250 : ℝ)^8405 ≤ (11538476215413/25000000000000 : ℝ)^6357 := by
    have hnat : (10883259 : ℕ)^8405*25000000000000^6357 ≤ 11538476215413^6357*19531250^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10883259 19531250 11538476215413 25000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3185251957/10000000000 : ℝ)^8405 ≤ (22033035680731/100000000000000 : ℝ)^6357 := by
    have hnat : (3185251957 : ℕ)^8405*100000000000000^6357 ≤ 22033035680731^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3185251957 10000000000 22033035680731 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4205356589/10000000000 : ℝ), (10883259/19531250 : ℝ), (3185251957/10000000000 : ℝ)] ![(31813059447469/100000000000000 : ℝ), (11538476215413/25000000000000 : ℝ), (22033035680731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4205356589/10000000000 : ℝ)|^8405 ≤ (31813059447469/100000000000000 : ℝ)^6357
        have hw : |(4205356589/10000000000 : ℝ)|=(4205356589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(10883259/19531250 : ℝ)|^8405 ≤ (11538476215413/25000000000000 : ℝ)^6357
        have hw : |(10883259/19531250 : ℝ)|=(10883259/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3185251957/10000000000 : ℝ)|^8405 ≤ (22033035680731/100000000000000 : ℝ)^6357
        have hw : |(3185251957/10000000000 : ℝ)|=(3185251957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1212_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4713791/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (349/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27549/100000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (2101/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2101 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2101*1^512 ≤ 0^512*1^2101 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2101 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2101 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2101/512 : ℝ) ≤ (1164171494078855577/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2101 ≤ (1164171494078855577/50000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2101*50000000000000000000^512 ≤ 1164171494078855577^512*5^2101 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1164171494078855577 50000000000000000000 2101 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1164171494078855577/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2101 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2101/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2101 := by
      have hnat : (1 : ℕ)^512*1^2101 ≤ 1^2101*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2101 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2101 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (51164171494078855577/50000000000000000000 : ℝ) ≤ (157128864406791/156250000000000 : ℝ) ^ (2101/512 : ℝ) := by
    have hpowers : (51164171494078855577/50000000000000000000 : ℝ)^512 ≤ (157128864406791/156250000000000 : ℝ)^2101 := by
      have hnat : (51164171494078855577 : ℕ)^512*156250000000000^2101 ≤ 157128864406791^2101*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51164171494078855577 50000000000000000000 157128864406791 156250000000000 512 2101 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (157128864406791/156250000000000 : ℝ)) (X := (51164171494078855577/50000000000000000000 : ℝ)) (by norm_num) 2101 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (26164171494078855577/25000000000000000000 : ℝ) ≤ (79003864406791/78125000000000 : ℝ) ^ (2101/512 : ℝ) := by
    have hpowers : (26164171494078855577/25000000000000000000 : ℝ)^512 ≤ (79003864406791/78125000000000 : ℝ)^2101 := by
      have hnat : (26164171494078855577 : ℕ)^512*78125000000000^2101 ≤ 79003864406791^2101*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26164171494078855577 25000000000000000000 79003864406791 78125000000000 512 2101 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (79003864406791/78125000000000 : ℝ)) (X := (26164171494078855577/25000000000000000000 : ℝ)) (by norm_num) 2101 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(878864406791/62500000000000 : ℝ)*(0 : ℝ))^(2101/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(878864406791/62500000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1164171494078855577/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(878864406791/62500000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2101/512 : ℝ) := by
    rw [show (1 : ℝ)+(878864406791/62500000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(157128864406791/156250000000000 : ℝ) by norm_num, show 1+(1164171494078855577/50000000000000000000 : ℝ)+(0 : ℝ)=(51164171494078855577/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1164171494078855577/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(878864406791/62500000000000 : ℝ)*(2/5 : ℝ))^(2101/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(878864406791/62500000000000 : ℝ)*(2/5 : ℝ)=(79003864406791/78125000000000 : ℝ) by norm_num, show 1+2*(1164171494078855577/50000000000000000000 : ℝ)=(26164171494078855577/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(878864406791/62500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2101/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (878864406791/62500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(878864406791/62500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2101/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (878864406791/62500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(878864406791/62500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2101/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (878864406791/62500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-116865759/625000000 : ℝ)*X 0 0+(6038292473/10000000000 : ℝ)*X 0 1+(299328813/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5512849689/10000000000 : ℝ)*X 1 0+(-516942243/2000000000 : ℝ)*X 1 1+(4789260983/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((689106209/1250000000 : ℝ)*X 2 0+(4789261001/10000000000 : ℝ)*X 2 1+(-1292355607/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((419538791/1000000000 : ℝ)*X 0 0+(623611007/2000000000 : ℝ)*X 0 1+(1409283603/2500000000 : ℝ)*X 0 2+(419538791/1000000000 : ℝ)*X 1 0+(623611007/2000000000 : ℝ)*X 1 1+(1409283603/2500000000 : ℝ)*X 1 2+(419538791/1000000000 : ℝ)*X 2 0+(623611007/2000000000 : ℝ)*X 2 1+(1409283603/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1874795383/10000000000 : ℝ)*X 0 0+(301340317/625000000 : ℝ)*X 0 1+(300248599/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5173136121/10000000000 : ℝ)*X 1 0+(-1368998617/10000000000 : ℝ)*X 1 1+(6004973693/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5173136973/10000000000 : ℝ)*X 2 0+(375310779/625000000 : ℝ)*X 2 1+(-1368999289/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4205356589/10000000000 : ℝ)*X 0 0+(10883259/19531250 : ℝ)*X 0 1+(3185251957/10000000000 : ℝ)*X 0 2+(4205356589/10000000000 : ℝ)*X 1 0+(10883259/19531250 : ℝ)*X 1 1+(3185251957/10000000000 : ℝ)*X 1 2+(4205356589/10000000000 : ℝ)*X 2 0+(10883259/19531250 : ℝ)*X 2 1+(3185251957/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (569531372239200018573/97656250000000000000000000 : ℝ) := by norm_num
    linear_combination (8078063/12500000000000 : ℝ)*(base1) + (1426305711/100000000000000 : ℝ)*(base19) + (1326189949/100000000000000 : ℝ)*(base23) + (48823433/50000000000000 : ℝ)*(base24) + (326161929/100000000000000 : ℝ)*(upper3) + (18712545181921/3125000000000 : ℝ)*(major0) + (18712545181921/3125000000000 : ℝ)*(major1) + (18712545181921/3125000000000 : ℝ)*(major2) + (800625167582677/100000000000000 : ℝ)*(sp0) + (800626836094383/100000000000000 : ℝ)*(sp1) + (800626838563279/100000000000000 : ℝ)*(sp2) + (99242969407169/25000000000000 : ℝ)*(sp3) + (3159441921/100000000000000 : ℝ)*(sp4) + (19940717/800000000000 : ℝ)*(sp7) + (79394886968561/20000000000000 : ℝ)*(f.failure) + (400314131200047/50000000000000 : ℝ)*(f.sum) + (2713352376199/1562500000000000000000000000 : ℝ)*base66 + (9133543519949/3125000000000000000000000000 : ℝ)*base68 + (15947129269949/3125000000000000000000000000 : ℝ)*base70 + (4878357738581/781250000000000000000000000 : ℝ)*base72 + (3111811818023/3125000000000000000000000000 : ℝ)*base74 + (1712043530287/1562500000000000000000000000 : ℝ)*base76 + (7920298457449/3125000000000000000000000000 : ℝ)*base78 + (17181758351199/3125000000000000000000000000 : ℝ)*base80 + (14468885618023/3125000000000000000000000000 : ℝ)*base82 + (124751/62500000000000000000 : ℝ)*base89 + (124751/62500000000000000000 : ℝ)*base91 + (124751/62500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17276259472330773074727/3125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1531081059/100000000000000 : ℝ)*(base19) + (1712336497/100000000000000 : ℝ)*(base23) + (5300937/25000000000000 : ℝ)*(base39) + (325319153/100000000000000 : ℝ)*(upper3) + (16927443/25000000000000 : ℝ)*(upper5) + (315967874076779/50000000000000 : ℝ)*(major0) + (315967874076779/50000000000000 : ℝ)*(major1) + (63193572694981/10000000000000 : ℝ)*(major2) + (3545972277/100000000000000 : ℝ)*(sp1) + (3872938369/100000000000000 : ℝ)*(sp2) + (422465262339931/50000000000000 : ℝ)*(sp4) + (844925447626527/100000000000000 : ℝ)*(sp5) + (105615620076093/12500000000000 : ℝ)*(sp6) + (418940766143401/100000000000000 : ℝ)*(sp7) + (418940766143401/100000000000000 : ℝ)*(f.failure) + (84493054588361/10000000000000 : ℝ)*(f.sum) + (2064705798331/3125000000000000000000000000 : ℝ)*base66 + (3474150595971/625000000000000000000000000 : ℝ)*base67 + (1098349097641/781250000000000000000000000 : ℝ)*base69 + (294070005173/312500000000000000000000000 : ℝ)*base71 + (4651125146147/1562500000000000000000000000 : ℝ)*base73 + (9021201401593/1562500000000000000000000000 : ℝ)*base76 + (1295674447641/781250000000000000000000000 : ℝ)*base77 + (655381048629/195312500000000000000000000 : ℝ)*base79 + (2432956090503/3125000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (406809/312500000000000000000 : ℝ)*base90 + (406809/312500000000000000000 : ℝ)*base92 + (406809/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1212_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4713791/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (349/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27549/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1212_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1212_s1_0 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-129340227/625000000 : ℝ)*x 0 + (1136641591/2000000000 : ℝ)*x 1 + (2508291673/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (129340227/625000000 : ℝ)^8405 ≤ (12457930096329/100000000000000 : ℝ)^6357 := by
    have hnat : (129340227 : ℕ)^8405*100000000000000^6357 ≤ 12457930096329^6357*625000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129340227 625000000 12457930096329 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1136641591/2000000000 : ℝ)^8405 ≤ (47373152912493/100000000000000 : ℝ)^6357 := by
    have hnat : (1136641591 : ℕ)^8405*100000000000000^6357 ≤ 47373152912493^6357*2000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136641591 2000000000 47373152912493 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2508291673/5000000000 : ℝ)^8405 ≤ (40168916980821/100000000000000 : ℝ)^6357 := by
    have hnat : (2508291673 : ℕ)^8405*100000000000000^6357 ≤ 40168916980821^6357*5000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2508291673 5000000000 40168916980821 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-129340227/625000000 : ℝ), (1136641591/2000000000 : ℝ), (2508291673/5000000000 : ℝ)] ![(12457930096329/100000000000000 : ℝ), (47373152912493/100000000000000 : ℝ), (40168916980821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-129340227/625000000 : ℝ)|^8405 ≤ (12457930096329/100000000000000 : ℝ)^6357
        have hw : |(-129340227/625000000 : ℝ)|=(129340227/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1136641591/2000000000 : ℝ)|^8405 ≤ (47373152912493/100000000000000 : ℝ)^6357
        have hw : |(1136641591/2000000000 : ℝ)|=(1136641591/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2508291673/5000000000 : ℝ)|^8405 ≤ (40168916980821/100000000000000 : ℝ)^6357
        have hw : |(2508291673/5000000000 : ℝ)|=(2508291673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1212_s1_1 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (108305837/200000000 : ℝ)*x 0 + (-2427932909/10000000000 : ℝ)*x 1 + (5016583853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108305837/200000000 : ℝ)^8405 ≤ (177772372841/400000000000 : ℝ)^6357 := by
    have hnat : (108305837 : ℕ)^8405*400000000000^6357 ≤ 177772372841^6357*200000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108305837 200000000 177772372841 400000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2427932909/10000000000 : ℝ)^8405 ≤ (15387984430641/100000000000000 : ℝ)^6357 := by
    have hnat : (2427932909 : ℕ)^8405*100000000000000^6357 ≤ 15387984430641^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2427932909 10000000000 15387984430641 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5016583853/10000000000 : ℝ)^8405 ≤ (10042230587091/25000000000000 : ℝ)^6357 := by
    have hnat : (5016583853 : ℕ)^8405*25000000000000^6357 ≤ 10042230587091^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5016583853 10000000000 10042230587091 25000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(108305837/200000000 : ℝ), (-2427932909/10000000000 : ℝ), (5016583853/10000000000 : ℝ)] ![(177772372841/400000000000 : ℝ), (15387984430641/100000000000000 : ℝ), (10042230587091/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(108305837/200000000 : ℝ)|^8405 ≤ (177772372841/400000000000 : ℝ)^6357
        have hw : |(108305837/200000000 : ℝ)|=(108305837/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2427932909/10000000000 : ℝ)|^8405 ≤ (15387984430641/100000000000000 : ℝ)^6357
        have hw : |(-2427932909/10000000000 : ℝ)|=(2427932909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5016583853/10000000000 : ℝ)|^8405 ≤ (10042230587091/25000000000000 : ℝ)^6357
        have hw : |(5016583853/10000000000 : ℝ)|=(5016583853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1212_s1_2 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (541529053/1000000000 : ℝ)*x 0 + (5016584697/10000000000 : ℝ)*x 1 + (-151745847/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541529053/1000000000 : ℝ)^8405 ≤ (2777692430437/6250000000000 : ℝ)^6357 := by
    have hnat : (541529053 : ℕ)^8405*6250000000000^6357 ≤ 2777692430437^6357*1000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541529053 1000000000 2777692430437 6250000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5016584697/10000000000 : ℝ)^8405 ≤ (40168931283683/100000000000000 : ℝ)^6357 := by
    have hnat : (5016584697 : ℕ)^8405*100000000000000^6357 ≤ 40168931283683^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5016584697 10000000000 40168931283683 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (151745847/625000000 : ℝ)^8405 ≤ (3077597963763/20000000000000 : ℝ)^6357 := by
    have hnat : (151745847 : ℕ)^8405*20000000000000^6357 ≤ 3077597963763^6357*625000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151745847 625000000 3077597963763 20000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(541529053/1000000000 : ℝ), (5016584697/10000000000 : ℝ), (-151745847/625000000 : ℝ)] ![(2777692430437/6250000000000 : ℝ), (40168931283683/100000000000000 : ℝ), (3077597963763/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(541529053/1000000000 : ℝ)|^8405 ≤ (2777692430437/6250000000000 : ℝ)^6357
        have hw : |(541529053/1000000000 : ℝ)|=(541529053/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5016584697/10000000000 : ℝ)|^8405 ≤ (40168931283683/100000000000000 : ℝ)^6357
        have hw : |(5016584697/10000000000 : ℝ)|=(5016584697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-151745847/625000000 : ℝ)|^8405 ≤ (3077597963763/20000000000000 : ℝ)^6357
        have hw : |(-151745847/625000000 : ℝ)|=(151745847/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1212_s1_3 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2155725373/5000000000 : ℝ)*x 0 + (1844999073/5000000000 : ℝ)*x 1 + (1006893063/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155725373/5000000000 : ℝ)^8405 ≤ (1643925217179/5000000000000 : ℝ)^6357 := by
    have hnat : (2155725373 : ℕ)^8405*5000000000000^6357 ≤ 1643925217179^6357*5000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155725373 5000000000 1643925217179 5000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1844999073/5000000000 : ℝ)^8405 ≤ (26763155951139/100000000000000 : ℝ)^6357 := by
    have hnat : (1844999073 : ℕ)^8405*100000000000000^6357 ≤ 26763155951139^6357*5000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1844999073 5000000000 26763155951139 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1006893063/2000000000 : ℝ)^8405 ≤ (20179169841959/50000000000000 : ℝ)^6357 := by
    have hnat : (1006893063 : ℕ)^8405*50000000000000^6357 ≤ 20179169841959^6357*2000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006893063 2000000000 20179169841959 50000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2155725373/5000000000 : ℝ), (1844999073/5000000000 : ℝ), (1006893063/2000000000 : ℝ)] ![(1643925217179/5000000000000 : ℝ), (26763155951139/100000000000000 : ℝ), (20179169841959/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2155725373/5000000000 : ℝ)|^8405 ≤ (1643925217179/5000000000000 : ℝ)^6357
        have hw : |(2155725373/5000000000 : ℝ)|=(2155725373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1844999073/5000000000 : ℝ)|^8405 ≤ (26763155951139/100000000000000 : ℝ)^6357
        have hw : |(1844999073/5000000000 : ℝ)|=(1844999073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1006893063/2000000000 : ℝ)|^8405 ≤ (20179169841959/50000000000000 : ℝ)^6357
        have hw : |(1006893063/2000000000 : ℝ)|=(1006893063/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1212_s1_4 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1035076881/5000000000 : ℝ)*x 0 + (5025442173/10000000000 : ℝ)*x 1 + (283709027/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1035076881/5000000000 : ℝ)^8405 ≤ (2492716516889/20000000000000 : ℝ)^6357 := by
    have hnat : (1035076881 : ℕ)^8405*20000000000000^6357 ≤ 2492716516889^6357*5000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035076881 5000000000 2492716516889 20000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5025442173/10000000000 : ℝ)^8405 ≤ (20131365450989/50000000000000 : ℝ)^6357 := by
    have hnat : (5025442173 : ℕ)^8405*50000000000000^6357 ≤ 20131365450989^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5025442173 10000000000 20131365450989 50000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (283709027/500000000 : ℝ)^8405 ≤ (472736864941/1000000000000 : ℝ)^6357 := by
    have hnat : (283709027 : ℕ)^8405*1000000000000^6357 ≤ 472736864941^6357*500000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283709027 500000000 472736864941 1000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1035076881/5000000000 : ℝ), (5025442173/10000000000 : ℝ), (283709027/500000000 : ℝ)] ![(2492716516889/20000000000000 : ℝ), (20131365450989/50000000000000 : ℝ), (472736864941/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1035076881/5000000000 : ℝ)|^8405 ≤ (2492716516889/20000000000000 : ℝ)^6357
        have hw : |(-1035076881/5000000000 : ℝ)|=(1035076881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5025442173/10000000000 : ℝ)|^8405 ≤ (20131365450989/50000000000000 : ℝ)^6357
        have hw : |(5025442173/10000000000 : ℝ)|=(5025442173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(283709027/500000000 : ℝ)|^8405 ≤ (472736864941/1000000000000 : ℝ)^6357
        have hw : |(283709027/500000000 : ℝ)|=(283709027/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1212_s1_5 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5243794197/10000000000 : ℝ)*x 0 + (-88516993/500000000 : ℝ)*x 1 + (2837088391/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5243794197/10000000000 : ℝ)^8405 ≤ (42591742081739/100000000000000 : ℝ)^6357 := by
    have hnat : (5243794197 : ℕ)^8405*100000000000000^6357 ≤ 42591742081739^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243794197 10000000000 42591742081739 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (88516993/500000000 : ℝ)^8405 ≤ (10134612812719/100000000000000 : ℝ)^6357 := by
    have hnat : (88516993 : ℕ)^8405*100000000000000^6357 ≤ 10134612812719^6357*500000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88516993 500000000 10134612812719 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2837088391/5000000000 : ℝ)^8405 ≤ (47273645098083/100000000000000 : ℝ)^6357 := by
    have hnat : (2837088391 : ℕ)^8405*100000000000000^6357 ≤ 47273645098083^6357*5000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2837088391 5000000000 47273645098083 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5243794197/10000000000 : ℝ), (-88516993/500000000 : ℝ), (2837088391/5000000000 : ℝ)] ![(42591742081739/100000000000000 : ℝ), (10134612812719/100000000000000 : ℝ), (47273645098083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5243794197/10000000000 : ℝ)|^8405 ≤ (42591742081739/100000000000000 : ℝ)^6357
        have hw : |(5243794197/10000000000 : ℝ)|=(5243794197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-88516993/500000000 : ℝ)|^8405 ≤ (10134612812719/100000000000000 : ℝ)^6357
        have hw : |(-88516993/500000000 : ℝ)|=(88516993/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2837088391/5000000000 : ℝ)|^8405 ≤ (47273645098083/100000000000000 : ℝ)^6357
        have hw : |(2837088391/5000000000 : ℝ)|=(2837088391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1212_s1_6 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5243794353/10000000000 : ℝ)*x 0 + (5674177223/10000000000 : ℝ)*x 1 + (-442584749/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5243794353/10000000000 : ℝ)^8405 ≤ (10647935939257/25000000000000 : ℝ)^6357 := by
    have hnat : (5243794353 : ℕ)^8405*25000000000000^6357 ≤ 10647935939257^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243794353 10000000000 10647935939257 25000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5674177223/10000000000 : ℝ)^8405 ≤ (4727364995589/10000000000000 : ℝ)^6357 := by
    have hnat : (5674177223 : ℕ)^8405*10000000000000^6357 ≤ 4727364995589^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5674177223 10000000000 4727364995589 10000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (442584749/2500000000 : ℝ)^8405 ≤ (10134606273141/100000000000000 : ℝ)^6357 := by
    have hnat : (442584749 : ℕ)^8405*100000000000000^6357 ≤ 10134606273141^6357*2500000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442584749 2500000000 10134606273141 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5243794353/10000000000 : ℝ), (5674177223/10000000000 : ℝ), (-442584749/2500000000 : ℝ)] ![(10647935939257/25000000000000 : ℝ), (4727364995589/10000000000000 : ℝ), (10134606273141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5243794353/10000000000 : ℝ)|^8405 ≤ (10647935939257/25000000000000 : ℝ)^6357
        have hw : |(5243794353/10000000000 : ℝ)|=(5243794353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5674177223/10000000000 : ℝ)|^8405 ≤ (4727364995589/10000000000000 : ℝ)^6357
        have hw : |(5674177223/10000000000 : ℝ)|=(5674177223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-442584749/2500000000 : ℝ)|^8405 ≤ (10134606273141/100000000000000 : ℝ)^6357
        have hw : |(-442584749/2500000000 : ℝ)|=(442584749/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1212_s1_7 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (862577609/2000000000 : ℝ)*x 0 + (5016595169/10000000000 : ℝ)*x 1 + (3708212441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (862577609/2000000000 : ℝ)^8405 ≤ (32892996885753/100000000000000 : ℝ)^6357 := by
    have hnat : (862577609 : ℕ)^8405*100000000000000^6357 ≤ 32892996885753^6357*2000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862577609 2000000000 32892996885753 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5016595169/10000000000 : ℝ)^8405 ≤ (40169042149437/100000000000000 : ℝ)^6357 := by
    have hnat : (5016595169 : ℕ)^8405*100000000000000^6357 ≤ 40169042149437^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5016595169 10000000000 40169042149437 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3708212441/10000000000 : ℝ)^8405 ≤ (6734490237241/25000000000000 : ℝ)^6357 := by
    have hnat : (3708212441 : ℕ)^8405*25000000000000^6357 ≤ 6734490237241^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3708212441 10000000000 6734490237241 25000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(862577609/2000000000 : ℝ), (5016595169/10000000000 : ℝ), (3708212441/10000000000 : ℝ)] ![(32892996885753/100000000000000 : ℝ), (40169042149437/100000000000000 : ℝ), (6734490237241/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(862577609/2000000000 : ℝ)|^8405 ≤ (32892996885753/100000000000000 : ℝ)^6357
        have hw : |(862577609/2000000000 : ℝ)|=(862577609/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5016595169/10000000000 : ℝ)|^8405 ≤ (40169042149437/100000000000000 : ℝ)^6357
        have hw : |(5016595169/10000000000 : ℝ)|=(5016595169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3708212441/10000000000 : ℝ)|^8405 ≤ (6734490237241/25000000000000 : ℝ)^6357
        have hw : |(3708212441/10000000000 : ℝ)|=(3708212441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1212_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4713791/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27549/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (349/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (377/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20127/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27549/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (349/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27549/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (349/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27549/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (349/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27549/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (349/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27549/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (349/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27549/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (349/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (349/50000 : ℝ) ^ (2101/512 : ℝ) ≤ (141979955911/100000000000000000000 : ℝ) := by
    have hpowers : (349/50000 : ℝ)^2101 ≤ (141979955911/100000000000000000000 : ℝ)^512 := by
      have hnat : (349 : ℕ)^2101*100000000000000000000^512 ≤ 141979955911^512*50000^2101 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        349 50000 141979955911 100000000000000000000 2101 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (349/50000 : ℝ)) (X := (141979955911/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2101 512 (by norm_num) hpowers
    exact h
  have hpowhi : (27549/100000 : ℝ) ^ (2101/512 : ℝ) ≤ (252020324529735453/50000000000000000000 : ℝ) := by
    have hpowers : (27549/100000 : ℝ)^2101 ≤ (252020324529735453/50000000000000000000 : ℝ)^512 := by
      have hnat : (27549 : ℕ)^2101*50000000000000000000^512 ≤ 252020324529735453^512*100000^2101 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27549 100000 252020324529735453 50000000000000000000 2101 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27549/100000 : ℝ)) (X := (252020324529735453/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2101 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000141979955911/50000000000000000000 : ℝ) ≤ (5000000003459959/5000000000000000 : ℝ) ^ (2101/512 : ℝ) := by
    have hpowers : (50000000141979955911/50000000000000000000 : ℝ)^512 ≤ (5000000003459959/5000000000000000 : ℝ)^2101 := by
      have hnat : (50000000141979955911 : ℕ)^512*5000000000000000^2101 ≤ 5000000003459959^2101*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000141979955911 50000000000000000000 5000000003459959 5000000000000000 512 2101 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000003459959/5000000000000000 : ℝ)) (X := (50000000141979955911/50000000000000000000 : ℝ)) (by norm_num) 2101 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100504040791039426817/100000000000000000000 : ℝ) ≤ (2002451960401111/2000000000000000 : ℝ) ^ (2101/512 : ℝ) := by
    have hpowers : (100504040791039426817/100000000000000000000 : ℝ)^512 ≤ (2002451960401111/2000000000000000 : ℝ)^2101 := by
      have hnat : (100504040791039426817 : ℕ)^512*2000000000000000^2101 ≤ 2002451960401111^2101*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100504040791039426817 100000000000000000000 2002451960401111 2000000000000000 512 2101 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2002451960401111/2000000000000000 : ℝ)) (X := (100504040791039426817/100000000000000000000 : ℝ)) (by norm_num) 2101 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25252020324529735453/25000000000000000000 : ℝ) ≤ (1253064949636399/1250000000000000 : ℝ) ^ (2101/512 : ℝ) := by
    have hpowers : (25252020324529735453/25000000000000000000 : ℝ)^512 ≤ (1253064949636399/1250000000000000 : ℝ)^2101 := by
      have hnat : (25252020324529735453 : ℕ)^512*1250000000000000^2101 ≤ 1253064949636399^2101*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25252020324529735453 25000000000000000000 1253064949636399 1250000000000000 512 2101 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1253064949636399/1250000000000000 : ℝ)) (X := (25252020324529735453/25000000000000000000 : ℝ)) (by norm_num) 2101 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(141979955911/100000000000000000000 : ℝ) ≤ ((12204222068721234953/12205000000000000000 : ℝ)+2*(1114526825967/244100000000000 : ℝ)*(349/50000 : ℝ))^(2101/512 : ℝ) := by
    rw [show (12204222068721234953/12205000000000000000 : ℝ)+2*(1114526825967/244100000000000 : ℝ)*(349/50000 : ℝ)=(5000000003459959/5000000000000000 : ℝ) by norm_num, show 1+2*(141979955911/100000000000000000000 : ℝ)=(50000000141979955911/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(252020324529735453/50000000000000000000 : ℝ)+(141979955911/100000000000000000000 : ℝ) ≤ ((12204222068721234953/12205000000000000000 : ℝ)+(1114526825967/244100000000000 : ℝ)*((27549/100000 : ℝ)+(349/50000 : ℝ)))^(2101/512 : ℝ) := by
    rw [show (12204222068721234953/12205000000000000000 : ℝ)+(1114526825967/244100000000000 : ℝ)*((27549/100000 : ℝ)+(349/50000 : ℝ))=(2002451960401111/2000000000000000 : ℝ) by norm_num, show 1+(252020324529735453/50000000000000000000 : ℝ)+(141979955911/100000000000000000000 : ℝ)=(100504040791039426817/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(252020324529735453/50000000000000000000 : ℝ) ≤ ((12204222068721234953/12205000000000000000 : ℝ)+2*(1114526825967/244100000000000 : ℝ)*(27549/100000 : ℝ))^(2101/512 : ℝ) := by
    rw [show (12204222068721234953/12205000000000000000 : ℝ)+2*(1114526825967/244100000000000 : ℝ)*(27549/100000 : ℝ)=(1253064949636399/1250000000000000 : ℝ) by norm_num, show 1+2*(252020324529735453/50000000000000000000 : ℝ)=(25252020324529735453/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12204222068721234953/12205000000000000000 : ℝ)*(X 1 0+X 2 0)+(1114526825967/244100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2101/512 : ℝ)) (lo := (349/50000 : ℝ)) (hi := (27549/100000 : ℝ)) (c := (12204222068721234953/12205000000000000000 : ℝ)) (alpha := (1114526825967/244100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12204222068721234953/12205000000000000000 : ℝ)*(X 0 1+X 2 1)+(1114526825967/244100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2101/512 : ℝ)) (lo := (349/50000 : ℝ)) (hi := (27549/100000 : ℝ)) (c := (12204222068721234953/12205000000000000000 : ℝ)) (alpha := (1114526825967/244100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12204222068721234953/12205000000000000000 : ℝ)*(X 0 2+X 1 2)+(1114526825967/244100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2101/512 : ℝ)) (lo := (349/50000 : ℝ)) (hi := (27549/100000 : ℝ)) (c := (12204222068721234953/12205000000000000000 : ℝ)) (alpha := (1114526825967/244100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-129340227/625000000 : ℝ)*X 0 0+(1136641591/2000000000 : ℝ)*X 0 1+(2508291673/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((108305837/200000000 : ℝ)*X 1 0+(-2427932909/10000000000 : ℝ)*X 1 1+(5016583853/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((541529053/1000000000 : ℝ)*X 2 0+(5016584697/10000000000 : ℝ)*X 2 1+(-151745847/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2155725373/5000000000 : ℝ)*X 0 0+(1844999073/5000000000 : ℝ)*X 0 1+(1006893063/2000000000 : ℝ)*X 0 2+(2155725373/5000000000 : ℝ)*X 1 0+(1844999073/5000000000 : ℝ)*X 1 1+(1006893063/2000000000 : ℝ)*X 1 2+(2155725373/5000000000 : ℝ)*X 2 0+(1844999073/5000000000 : ℝ)*X 2 1+(1006893063/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1035076881/5000000000 : ℝ)*X 0 0+(5025442173/10000000000 : ℝ)*X 0 1+(283709027/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5243794197/10000000000 : ℝ)*X 1 0+(-88516993/500000000 : ℝ)*X 1 1+(2837088391/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5243794353/10000000000 : ℝ)*X 2 0+(5674177223/10000000000 : ℝ)*X 2 1+(-442584749/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((862577609/2000000000 : ℝ)*X 0 0+(5016595169/10000000000 : ℝ)*X 0 1+(3708212441/10000000000 : ℝ)*X 0 2+(862577609/2000000000 : ℝ)*X 1 0+(5016595169/10000000000 : ℝ)*X 1 1+(3708212441/10000000000 : ℝ)*X 1 2+(862577609/2000000000 : ℝ)*X 2 0+(5016595169/10000000000 : ℝ)*X 2 1+(3708212441/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2263217698584696364024240179/305125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (943032733/50000000000000 : ℝ)*(base19) + (1411202011/100000000000000 : ℝ)*(base23) + (3632209/100000000000000 : ℝ)*(upper2) + (421655827/100000000000000 : ℝ)*(upper3) + (7846169/12500000000000 : ℝ)*(upper4) + (560979599519173/50000000000000 : ℝ)*(major0) + (560979599519173/50000000000000 : ℝ)*(major1) + (560979599519173/50000000000000 : ℝ)*(major2) + (375027026343287/25000000000000 : ℝ)*(sp0) + (375028814207843/25000000000000 : ℝ)*(sp1) + (1500115731694827/100000000000000 : ℝ)*(sp2) + (148758834416923/20000000000000 : ℝ)*(sp3) + (903752369/10000000000000 : ℝ)*(sp4) + (6835850363/100000000000000 : ℝ)*(sp7) + (371900503967489/50000000000000 : ℝ)*(f.failure) + (750058571448419/50000000000000 : ℝ)*(f.sum) + (37249098078263/12205000000000000000000000000 : ℝ)*base66 + (3946268307444053869/610250000000000000000000000000000 : ℝ)*base67 + (2507793250911803869/610250000000000000000000000000000 : ℝ)*base69 + (1387239563244553869/610250000000000000000000000000000 : ℝ)*base71 + (28451256869837/12205000000000000000000000000 : ℝ)*base73 + (2654466528404803869/610250000000000000000000000000000 : ℝ)*base75 + (235594003617053869/610250000000000000000000000000000 : ℝ)*base77 + (8320118192026803869/610250000000000000000000000000000 : ℝ)*base79 + (15079610362631/6102500000000000000000000000 : ℝ)*base81 + (1684201/156250000000000000000 : ℝ)*base90 + (1684201/156250000000000000000 : ℝ)*base92 + (1684201/156250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (633269507276848758143914791/152562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (77333411/25000000000000 : ℝ)*(base19) + (874525659/100000000000000 : ℝ)*(base23) + (238523/625000000000 : ℝ)*(lower2) + (36977983/25000000000000 : ℝ)*(lower3) + (258686281/100000000000000 : ℝ)*(lower4) + (288220598303849/25000000000000 : ℝ)*(major0) + (288220598303849/25000000000000 : ℝ)*(major1) + (288220598303849/25000000000000 : ℝ)*(major2) + (4524922853/100000000000000 : ℝ)*(sp0) + (604160961/20000000000000 : ℝ)*(sp2) + (770729317214321/50000000000000 : ℝ)*(sp4) + (385365712504463/25000000000000 : ℝ)*(sp5) + (1541459264021031/100000000000000 : ℝ)*(sp6) + (764301488716431/100000000000000 : ℝ)*(sp7) + (764301488716431/100000000000000 : ℝ)*(f.failure) + (308292631870299/20000000000000 : ℝ)*(f.sum) + (231567220941543/12205000000000000000000000000 : ℝ)*base66 + (330414127902615903/305125000000000000000000000000000 : ℝ)*base68 + (37132362243740903/305125000000000000000000000000000 : ℝ)*base70 + (2356149901662490903/305125000000000000000000000000000 : ℝ)*base72 + (16665816369463/12205000000000000000000000000 : ℝ)*base74 + (1060606878204490903/305125000000000000000000000000000 : ℝ)*base76 + (1225398271173884097/305125000000000000000000000000000 : ℝ)*base77 + (4648178891497759097/305125000000000000000000000000000 : ℝ)*base79 + (119404863921757/12205000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1499921/312500000000000000000 : ℝ)*base89 + (1499921/312500000000000000000 : ℝ)*base91 + (1499921/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1212_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4713791/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27549/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (349/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (377/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20127/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1212_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1212_s2_0 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-423801483/2000000000 : ℝ)*x 0 + (5497988167/10000000000 : ℝ)*x 1 + (5170221489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (423801483/2000000000 : ℝ)^8405 ≤ (12853939564211/100000000000000 : ℝ)^6357 := by
    have hnat : (423801483 : ℕ)^8405*100000000000000^6357 ≤ 12853939564211^6357*2000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423801483 2000000000 12853939564211 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5497988167/10000000000 : ℝ)^8405 ≤ (22671313443627/50000000000000 : ℝ)^6357 := by
    have hnat : (5497988167 : ℕ)^8405*50000000000000^6357 ≤ 22671313443627^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5497988167 10000000000 22671313443627 50000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5170221489/10000000000 : ℝ)^8405 ≤ (41803433533271/100000000000000 : ℝ)^6357 := by
    have hnat : (5170221489 : ℕ)^8405*100000000000000^6357 ≤ 41803433533271^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5170221489 10000000000 41803433533271 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-423801483/2000000000 : ℝ), (5497988167/10000000000 : ℝ), (5170221489/10000000000 : ℝ)] ![(12853939564211/100000000000000 : ℝ), (22671313443627/50000000000000 : ℝ), (41803433533271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-423801483/2000000000 : ℝ)|^8405 ≤ (12853939564211/100000000000000 : ℝ)^6357
        have hw : |(-423801483/2000000000 : ℝ)|=(423801483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5497988167/10000000000 : ℝ)|^8405 ≤ (22671313443627/50000000000000 : ℝ)^6357
        have hw : |(5497988167/10000000000 : ℝ)|=(5497988167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5170221489/10000000000 : ℝ)|^8405 ≤ (41803433533271/100000000000000 : ℝ)^6357
        have hw : |(5170221489/10000000000 : ℝ)|=(5170221489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1212_s2_1 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5370912531/10000000000 : ℝ)*x 0 + (-2288964291/10000000000 : ℝ)*x 1 + (2585113163/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370912531/10000000000 : ℝ)^8405 ≤ (43962172152609/100000000000000 : ℝ)^6357 := by
    have hnat : (5370912531 : ℕ)^8405*100000000000000^6357 ≤ 43962172152609^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370912531 10000000000 43962172152609 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2288964291/10000000000 : ℝ)^8405 ≤ (7117171296161/50000000000000 : ℝ)^6357 := by
    have hnat : (2288964291 : ℕ)^8405*50000000000000^6357 ≤ 7117171296161^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2288964291 10000000000 7117171296161 50000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2585113163/5000000000 : ℝ)^8405 ≤ (5225435655259/12500000000000 : ℝ)^6357 := by
    have hnat : (2585113163 : ℕ)^8405*12500000000000^6357 ≤ 5225435655259^6357*5000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585113163 5000000000 5225435655259 12500000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370912531/10000000000 : ℝ), (-2288964291/10000000000 : ℝ), (2585113163/5000000000 : ℝ)] ![(43962172152609/100000000000000 : ℝ), (7117171296161/50000000000000 : ℝ), (5225435655259/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370912531/10000000000 : ℝ)|^8405 ≤ (43962172152609/100000000000000 : ℝ)^6357
        have hw : |(5370912531/10000000000 : ℝ)|=(5370912531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2288964291/10000000000 : ℝ)|^8405 ≤ (7117171296161/50000000000000 : ℝ)^6357
        have hw : |(-2288964291/10000000000 : ℝ)|=(2288964291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2585113163/5000000000 : ℝ)|^8405 ≤ (5225435655259/12500000000000 : ℝ)^6357
        have hw : |(2585113163/5000000000 : ℝ)|=(2585113163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1212_s2_2 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5370914767/10000000000 : ℝ)*x 0 + (2585111619/5000000000 : ℝ)*x 1 + (-2288965363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370914767/10000000000 : ℝ)^8405 ≤ (21981098175553/50000000000000 : ℝ)^6357 := by
    have hnat : (5370914767 : ℕ)^8405*50000000000000^6357 ≤ 21981098175553^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370914767 10000000000 21981098175553 50000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2585111619/5000000000 : ℝ)^8405 ≤ (41803452230539/100000000000000 : ℝ)^6357 := by
    have hnat : (2585111619 : ℕ)^8405*100000000000000^6357 ≤ 41803452230539^6357*5000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585111619 5000000000 41803452230539 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2288965363/10000000000 : ℝ)^8405 ≤ (14234351406437/100000000000000 : ℝ)^6357 := by
    have hnat : (2288965363 : ℕ)^8405*100000000000000^6357 ≤ 14234351406437^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2288965363 10000000000 14234351406437 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370914767/10000000000 : ℝ), (2585111619/5000000000 : ℝ), (-2288965363/10000000000 : ℝ)] ![(21981098175553/50000000000000 : ℝ), (41803452230539/100000000000000 : ℝ), (14234351406437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370914767/10000000000 : ℝ)|^8405 ≤ (21981098175553/50000000000000 : ℝ)^6357
        have hw : |(5370914767/10000000000 : ℝ)|=(5370914767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2585111619/5000000000 : ℝ)|^8405 ≤ (41803452230539/100000000000000 : ℝ)^6357
        have hw : |(2585111619/5000000000 : ℝ)|=(2585111619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2288965363/10000000000 : ℝ)|^8405 ≤ (14234351406437/100000000000000 : ℝ)^6357
        have hw : |(-2288965363/10000000000 : ℝ)|=(2288965363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1212_s2_3 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4345618109/10000000000 : ℝ)*x 0 + (805470609/2000000000 : ℝ)*x 1 + (4688398733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4345618109/10000000000 : ℝ)^8405 ≤ (33223440441703/100000000000000 : ℝ)^6357 := by
    have hnat : (4345618109 : ℕ)^8405*100000000000000^6357 ≤ 33223440441703^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4345618109 10000000000 33223440441703 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (805470609/2000000000 : ℝ)^8405 ≤ (30044920224027/100000000000000 : ℝ)^6357 := by
    have hnat : (805470609 : ℕ)^8405*100000000000000^6357 ≤ 30044920224027^6357*2000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      805470609 2000000000 30044920224027 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4688398733/10000000000 : ℝ)^8405 ≤ (18365819658117/50000000000000 : ℝ)^6357 := by
    have hnat : (4688398733 : ℕ)^8405*50000000000000^6357 ≤ 18365819658117^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4688398733 10000000000 18365819658117 50000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4345618109/10000000000 : ℝ), (805470609/2000000000 : ℝ), (4688398733/10000000000 : ℝ)] ![(33223440441703/100000000000000 : ℝ), (30044920224027/100000000000000 : ℝ), (18365819658117/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4345618109/10000000000 : ℝ)|^8405 ≤ (33223440441703/100000000000000 : ℝ)^6357
        have hw : |(4345618109/10000000000 : ℝ)|=(4345618109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(805470609/2000000000 : ℝ)|^8405 ≤ (30044920224027/100000000000000 : ℝ)^6357
        have hw : |(805470609/2000000000 : ℝ)|=(805470609/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4688398733/10000000000 : ℝ)|^8405 ≤ (18365819658117/50000000000000 : ℝ)^6357
        have hw : |(4688398733/10000000000 : ℝ)|=(4688398733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1212_s2_4 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-423818189/2000000000 : ℝ)*x 0 + (5172374809/10000000000 : ℝ)*x 1 + (5495815349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (423818189/2000000000 : ℝ)^8405 ≤ (12854609502073/100000000000000 : ℝ)^6357 := by
    have hnat : (423818189 : ℕ)^8405*100000000000000^6357 ≤ 12854609502073^6357*2000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423818189 2000000000 12854609502073 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5172374809/10000000000 : ℝ)^8405 ≤ (41826454630473/100000000000000 : ℝ)^6357 := by
    have hnat : (5172374809 : ℕ)^8405*100000000000000^6357 ≤ 41826454630473^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172374809 10000000000 41826454630473 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5495815349/10000000000 : ℝ)^8405 ≤ (22659467924817/50000000000000 : ℝ)^6357 := by
    have hnat : (5495815349 : ℕ)^8405*50000000000000^6357 ≤ 22659467924817^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5495815349 10000000000 22659467924817 50000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-423818189/2000000000 : ℝ), (5172374809/10000000000 : ℝ), (5495815349/10000000000 : ℝ)] ![(12854609502073/100000000000000 : ℝ), (41826454630473/100000000000000 : ℝ), (22659467924817/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-423818189/2000000000 : ℝ)|^8405 ≤ (12854609502073/100000000000000 : ℝ)^6357
        have hw : |(-423818189/2000000000 : ℝ)|=(423818189/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5172374809/10000000000 : ℝ)|^8405 ≤ (41826454630473/100000000000000 : ℝ)^6357
        have hw : |(5172374809/10000000000 : ℝ)|=(5172374809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5495815349/10000000000 : ℝ)|^8405 ≤ (22659467924817/50000000000000 : ℝ)^6357
        have hw : |(5495815349/10000000000 : ℝ)|=(5495815349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1212_s2_5 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (82615157/156250000 : ℝ)*x 0 + (-1963373571/10000000000 : ℝ)*x 1 + (5495815379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82615157/156250000 : ℝ)^8405 ≤ (21530164962127/50000000000000 : ℝ)^6357 := by
    have hnat : (82615157 : ℕ)^8405*50000000000000^6357 ≤ 21530164962127^6357*156250000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82615157 156250000 21530164962127 50000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1963373571/10000000000 : ℝ)^8405 ≤ (5810366944653/50000000000000 : ℝ)^6357 := by
    have hnat : (1963373571 : ℕ)^8405*50000000000000^6357 ≤ 5810366944653^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1963373571 10000000000 5810366944653 50000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5495815379/10000000000 : ℝ)^8405 ≤ (9063787235343/20000000000000 : ℝ)^6357 := by
    have hnat : (5495815379 : ℕ)^8405*20000000000000^6357 ≤ 9063787235343^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5495815379 10000000000 9063787235343 20000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82615157/156250000 : ℝ), (-1963373571/10000000000 : ℝ), (5495815379/10000000000 : ℝ)] ![(21530164962127/50000000000000 : ℝ), (5810366944653/50000000000000 : ℝ), (9063787235343/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82615157/156250000 : ℝ)|^8405 ≤ (21530164962127/50000000000000 : ℝ)^6357
        have hw : |(82615157/156250000 : ℝ)|=(82615157/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1963373571/10000000000 : ℝ)|^8405 ≤ (5810366944653/50000000000000 : ℝ)^6357
        have hw : |(-1963373571/10000000000 : ℝ)|=(1963373571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5495815379/10000000000 : ℝ)|^8405 ≤ (9063787235343/20000000000000 : ℝ)^6357
        have hw : |(5495815379/10000000000 : ℝ)|=(5495815379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1212_s2_6 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5287370229/10000000000 : ℝ)*x 0 + (1373953853/2500000000 : ℝ)*x 1 + (-490843319/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287370229/10000000000 : ℝ)^8405 ≤ (5382541484151/12500000000000 : ℝ)^6357 := by
    have hnat : (5287370229 : ℕ)^8405*12500000000000^6357 ≤ 5382541484151^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287370229 10000000000 5382541484151 12500000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1373953853/2500000000 : ℝ)^8405 ≤ (45318936536503/100000000000000 : ℝ)^6357 := by
    have hnat : (1373953853 : ℕ)^8405*100000000000000^6357 ≤ 45318936536503^6357*2500000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1373953853 2500000000 45318936536503 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (490843319/2500000000 : ℝ)^8405 ≤ (11620731580763/100000000000000 : ℝ)^6357 := by
    have hnat : (490843319 : ℕ)^8405*100000000000000^6357 ≤ 11620731580763^6357*2500000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490843319 2500000000 11620731580763 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287370229/10000000000 : ℝ), (1373953853/2500000000 : ℝ), (-490843319/2500000000 : ℝ)] ![(5382541484151/12500000000000 : ℝ), (45318936536503/100000000000000 : ℝ), (11620731580763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287370229/10000000000 : ℝ)|^8405 ≤ (5382541484151/12500000000000 : ℝ)^6357
        have hw : |(5287370229/10000000000 : ℝ)|=(5287370229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1373953853/2500000000 : ℝ)|^8405 ≤ (45318936536503/100000000000000 : ℝ)^6357
        have hw : |(1373953853/2500000000 : ℝ)|=(1373953853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-490843319/2500000000 : ℝ)|^8405 ≤ (11620731580763/100000000000000 : ℝ)^6357
        have hw : |(-490843319/2500000000 : ℝ)|=(490843319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1212_s2_7 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4345789069/10000000000 : ℝ)*x 0 + (4684058483/10000000000 : ℝ)*x 1 + (4031734447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4345789069/10000000000 : ℝ)^8405 ≤ (3322516856933/10000000000000 : ℝ)^6357 := by
    have hnat : (4345789069 : ℕ)^8405*10000000000000^6357 ≤ 3322516856933^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4345789069 10000000000 3322516856933 10000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4684058483/10000000000 : ℝ)^8405 ≤ (18343343543041/50000000000000 : ℝ)^6357 := by
    have hnat : (4684058483 : ℕ)^8405*50000000000000^6357 ≤ 18343343543041^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4684058483 10000000000 18343343543041 50000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4031734447/10000000000 : ℝ)^8405 ≤ (30088144332377/100000000000000 : ℝ)^6357 := by
    have hnat : (4031734447 : ℕ)^8405*100000000000000^6357 ≤ 30088144332377^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4031734447 10000000000 30088144332377 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4345789069/10000000000 : ℝ), (4684058483/10000000000 : ℝ), (4031734447/10000000000 : ℝ)] ![(3322516856933/10000000000000 : ℝ), (18343343543041/50000000000000 : ℝ), (30088144332377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4345789069/10000000000 : ℝ)|^8405 ≤ (3322516856933/10000000000000 : ℝ)^6357
        have hw : |(4345789069/10000000000 : ℝ)|=(4345789069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4684058483/10000000000 : ℝ)|^8405 ≤ (18343343543041/50000000000000 : ℝ)^6357
        have hw : |(4684058483/10000000000 : ℝ)|=(4684058483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4031734447/10000000000 : ℝ)|^8405 ≤ (30088144332377/100000000000000 : ℝ)^6357
        have hw : |(4031734447/10000000000 : ℝ)|=(4031734447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1212_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4713791/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20127/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (377/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (3/32 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16303/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20127/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (377/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20127/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (377/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20127/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (377/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20127/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (377/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20127/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (377/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20127/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (377/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (377/6250 : ℝ) ^ (2101/512 : ℝ) ≤ (989928947568627/100000000000000000000 : ℝ) := by
    have hpowers : (377/6250 : ℝ)^2101 ≤ (989928947568627/100000000000000000000 : ℝ)^512 := by
      have hnat : (377 : ℕ)^2101*100000000000000000000^512 ≤ 989928947568627^512*6250^2101 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        377 6250 989928947568627 100000000000000000000 2101 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (377/6250 : ℝ)) (X := (989928947568627/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2101 512 (by norm_num) hpowers
    exact h
  have hpowhi : (20127/100000 : ℝ) ^ (2101/512 : ℝ) ≤ (139010126725392371/100000000000000000000 : ℝ) := by
    have hpowers : (20127/100000 : ℝ)^2101 ≤ (139010126725392371/100000000000000000000 : ℝ)^512 := by
      have hnat : (20127 : ℕ)^2101*100000000000000000000^512 ≤ 139010126725392371^512*100000^2101 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20127 100000 139010126725392371 100000000000000000000 2101 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20127/100000 : ℝ)) (X := (139010126725392371/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2101 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000989928947568627/50000000000000000000 : ℝ) ≤ (2500012061871169/2500000000000000 : ℝ) ^ (2101/512 : ℝ) := by
    have hpowers : (50000989928947568627/50000000000000000000 : ℝ)^512 ≤ (2500012061871169/2500000000000000 : ℝ)^2101 := by
      have hnat : (50000989928947568627 : ℕ)^512*2500000000000000^2101 ≤ 2500012061871169^2101*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000989928947568627 50000000000000000000 2500012061871169 2500000000000000 512 2101 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500012061871169/2500000000000000 : ℝ)) (X := (50000989928947568627/50000000000000000000 : ℝ)) (by norm_num) 2101 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50070000027836480499/50000000000000000000 : ℝ) ≤ (312606559541753/312500000000000 : ℝ) ^ (2101/512 : ℝ) := by
    have hpowers : (50070000027836480499/50000000000000000000 : ℝ)^512 ≤ (312606559541753/312500000000000 : ℝ)^2101 := by
      have hnat : (50070000027836480499 : ℕ)^512*312500000000000^2101 ≤ 312606559541753^2101*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50070000027836480499 50000000000000000000 312606559541753 312500000000000 512 2101 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312606559541753/312500000000000 : ℝ)) (X := (50070000027836480499/50000000000000000000 : ℝ)) (by norm_num) 2101 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50139010126725392371/50000000000000000000 : ℝ) ≤ (2501692890796879/2500000000000000 : ℝ) ^ (2101/512 : ℝ) := by
    have hpowers : (50139010126725392371/50000000000000000000 : ℝ)^512 ≤ (2501692890796879/2500000000000000 : ℝ)^2101 := by
      have hnat : (50139010126725392371 : ℕ)^512*2500000000000000^2101 ≤ 2501692890796879^2101*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50139010126725392371 50000000000000000000 2501692890796879 2500000000000000 512 2101 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501692890796879/2500000000000000 : ℝ)) (X := (50139010126725392371/50000000000000000000 : ℝ)) (by norm_num) 2101 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(989928947568627/100000000000000000000 : ℝ) ≤ ((7045506250398848867/7047500000000000000 : ℝ)+2*(168082892571/70475000000000 : ℝ)*(377/6250 : ℝ))^(2101/512 : ℝ) := by
    rw [show (7045506250398848867/7047500000000000000 : ℝ)+2*(168082892571/70475000000000 : ℝ)*(377/6250 : ℝ)=(2500012061871169/2500000000000000 : ℝ) by norm_num, show 1+2*(989928947568627/100000000000000000000 : ℝ)=(50000989928947568627/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(139010126725392371/100000000000000000000 : ℝ)+(989928947568627/100000000000000000000 : ℝ) ≤ ((7045506250398848867/7047500000000000000 : ℝ)+(168082892571/70475000000000 : ℝ)*((20127/100000 : ℝ)+(377/6250 : ℝ)))^(2101/512 : ℝ) := by
    rw [show (7045506250398848867/7047500000000000000 : ℝ)+(168082892571/70475000000000 : ℝ)*((20127/100000 : ℝ)+(377/6250 : ℝ))=(312606559541753/312500000000000 : ℝ) by norm_num, show 1+(139010126725392371/100000000000000000000 : ℝ)+(989928947568627/100000000000000000000 : ℝ)=(50070000027836480499/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(139010126725392371/100000000000000000000 : ℝ) ≤ ((7045506250398848867/7047500000000000000 : ℝ)+2*(168082892571/70475000000000 : ℝ)*(20127/100000 : ℝ))^(2101/512 : ℝ) := by
    rw [show (7045506250398848867/7047500000000000000 : ℝ)+2*(168082892571/70475000000000 : ℝ)*(20127/100000 : ℝ)=(2501692890796879/2500000000000000 : ℝ) by norm_num, show 1+2*(139010126725392371/100000000000000000000 : ℝ)=(50139010126725392371/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7045506250398848867/7047500000000000000 : ℝ)*(X 1 0+X 2 0)+(168082892571/70475000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2101/512 : ℝ)) (lo := (377/6250 : ℝ)) (hi := (20127/100000 : ℝ)) (c := (7045506250398848867/7047500000000000000 : ℝ)) (alpha := (168082892571/70475000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7045506250398848867/7047500000000000000 : ℝ)*(X 0 1+X 2 1)+(168082892571/70475000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2101/512 : ℝ)) (lo := (377/6250 : ℝ)) (hi := (20127/100000 : ℝ)) (c := (7045506250398848867/7047500000000000000 : ℝ)) (alpha := (168082892571/70475000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7045506250398848867/7047500000000000000 : ℝ)*(X 0 2+X 1 2)+(168082892571/70475000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2101/512 : ℝ)) (lo := (377/6250 : ℝ)) (hi := (20127/100000 : ℝ)) (c := (7045506250398848867/7047500000000000000 : ℝ)) (alpha := (168082892571/70475000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-423801483/2000000000 : ℝ)*X 0 0+(5497988167/10000000000 : ℝ)*X 0 1+(5170221489/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5370912531/10000000000 : ℝ)*X 1 0+(-2288964291/10000000000 : ℝ)*X 1 1+(2585113163/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5370914767/10000000000 : ℝ)*X 2 0+(2585111619/5000000000 : ℝ)*X 2 1+(-2288965363/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4345618109/10000000000 : ℝ)*X 0 0+(805470609/2000000000 : ℝ)*X 0 1+(4688398733/10000000000 : ℝ)*X 0 2+(4345618109/10000000000 : ℝ)*X 1 0+(805470609/2000000000 : ℝ)*X 1 1+(4688398733/10000000000 : ℝ)*X 1 2+(4345618109/10000000000 : ℝ)*X 2 0+(805470609/2000000000 : ℝ)*X 2 1+(4688398733/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-423818189/2000000000 : ℝ)*X 0 0+(5172374809/10000000000 : ℝ)*X 0 1+(5495815349/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((82615157/156250000 : ℝ)*X 1 0+(-1963373571/10000000000 : ℝ)*X 1 1+(5495815379/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5287370229/10000000000 : ℝ)*X 2 0+(1373953853/2500000000 : ℝ)*X 2 1+(-490843319/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4345789069/10000000000 : ℝ)*X 0 0+(4684058483/10000000000 : ℝ)*X 0 1+(4031734447/10000000000 : ℝ)*X 0 2+(4345789069/10000000000 : ℝ)*X 1 0+(4684058483/10000000000 : ℝ)*X 1 1+(4031734447/10000000000 : ℝ)*X 1 2+(4345789069/10000000000 : ℝ)*X 2 0+(4684058483/10000000000 : ℝ)*X 2 1+(4031734447/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1211482042001735939998135863/176187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (418056829/25000000000000 : ℝ)*(base19) + (1239462309/50000000000000 : ℝ)*(base23) + (75228273/100000000000000 : ℝ)*(upper2) + (40368059/5000000000000 : ℝ)*(upper3) + (162086063/50000000000000 : ℝ)*(upper4) + (1140961482624979/50000000000000 : ℝ)*(major0) + (1140961482624979/50000000000000 : ℝ)*(major1) + (1140961482624979/50000000000000 : ℝ)*(major2) + (762750821268537/25000000000000 : ℝ)*(sp0) + (305104694782289/10000000000000 : ℝ)*(sp1) + (762761535281397/25000000000000 : ℝ)*(sp2) + (1512770708803167/100000000000000 : ℝ)*(sp3) + (22667488029/50000000000000 : ℝ)*(sp4) + (26372443353/100000000000000 : ℝ)*(sp7) + (37819927031163/2500000000000 : ℝ)*(f.failure) + (1525524310025103/50000000000000 : ℝ)*(f.sum) + (41707389490861/7047500000000000000000000000 : ℝ)*base65 + (2641532198412448793/352375000000000000000000000000000 : ℝ)*base67 + (2415444112122948793/352375000000000000000000000000000 : ℝ)*base69 + (2914637800054698793/352375000000000000000000000000000 : ℝ)*base71 + (2753116158737/880937500000000000000000000 : ℝ)*base73 + (4102784214398698793/352375000000000000000000000000000 : ℝ)*base75 + (5197631939865448793/352375000000000000000000000000000 : ℝ)*base77 + (2600979366085698793/352375000000000000000000000000000 : ℝ)*base79 + (10486412620469/7047500000000000000000000000 : ℝ)*base82 + (99817/7812500000000000000 : ℝ)*base90 + (99817/7812500000000000000 : ℝ)*base92 + (99817/7812500000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27706752900934810978583877/5505859375000000000000000000000 : ℝ) := by norm_num
    linear_combination (270026377/20000000000000 : ℝ)*(base19) + (1602933381/100000000000000 : ℝ)*(base23) + (18035071/50000000000000 : ℝ)*(upper2) + (185977849/100000000000000 : ℝ)*(upper3) + (102278531/100000000000000 : ℝ)*(upper5) + (72261539910677/3125000000000 : ℝ)*(major0) + (72261539910677/3125000000000 : ℝ)*(major1) + (72261539910677/3125000000000 : ℝ)*(major2) + (1325049923/10000000000000 : ℝ)*(sp1) + (18233693809/100000000000000 : ℝ)*(sp2) + (3091756972842019/100000000000000 : ℝ)*(sp4) + (386467796526363/12500000000000 : ℝ)*(sp5) + (3091737136214829/100000000000000 : ℝ)*(sp6) + (153298141370029/10000000000000 : ℝ)*(sp7) + (153298141370029/10000000000000 : ℝ)*(f.failure) + (3091756972842019/100000000000000 : ℝ)*(f.sum) + (66001570702649/14095000000000000000000000000 : ℝ)*base66 + (354197197596590957/44046875000000000000000000000000 : ℝ)*base68 + (408589794668153457/44046875000000000000000000000000 : ℝ)*base70 + (52994878732115791/22023437500000000000000000000000 : ℝ)*base72 + (26732425009311/3523750000000000000000000000 : ℝ)*base74 + (3528788751976763/688232421875000000000000000000 : ℝ)*base76 + (13660982526297677/2752929687500000000000000000000 : ℝ)*base78 + (38348349569977959/22023437500000000000000000000000 : ℝ)*base79 + (34698409518529/14095000000000000000000000000 : ℝ)*base82 + (369939/31250000000000000000 : ℝ)*base89 + (369939/31250000000000000000 : ℝ)*base91 + (369939/31250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1212_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4713791/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20127/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (377/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3/32 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16303/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1212_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1212_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4713791/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3/32 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16303/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1212_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1212_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1212_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4713791/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3/32 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16303/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1212_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

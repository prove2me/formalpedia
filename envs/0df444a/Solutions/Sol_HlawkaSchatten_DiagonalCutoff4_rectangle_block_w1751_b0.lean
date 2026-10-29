-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1751_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:19:32.324162+00:00
-- url     : https://prove2.me/submissions/62b3b616-e285-4d22-9f14-cfa955d45aa3

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
theorem support_rectangle_w1751_s0_0 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-117239659/1000000000 : ℝ)*x 0 + (2813636199/5000000000 : ℝ)*x 1 + (1244851793/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (117239659/1000000000 : ℝ)^5791 ≤ (3698897627391/50000000000000 : ℝ)^4767 := by
    have hnat : (117239659 : ℕ)^5791*50000000000000^4767 ≤ 3698897627391^4767*1000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117239659 1000000000 3698897627391 50000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2813636199/5000000000 : ℝ)^5791 ≤ (49734688290597/100000000000000 : ℝ)^4767 := by
    have hnat : (2813636199 : ℕ)^5791*100000000000000^4767 ≤ 49734688290597^4767*5000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2813636199 5000000000 49734688290597 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1244851793/2500000000 : ℝ)^5791 ≤ (4286751644021/10000000000000 : ℝ)^4767 := by
    have hnat : (1244851793 : ℕ)^5791*10000000000000^4767 ≤ 4286751644021^4767*2500000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1244851793 2500000000 4286751644021 10000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-117239659/1000000000 : ℝ), (2813636199/5000000000 : ℝ), (1244851793/2500000000 : ℝ)] ![(3698897627391/50000000000000 : ℝ), (49734688290597/100000000000000 : ℝ), (4286751644021/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-117239659/1000000000 : ℝ)|^5791 ≤ (3698897627391/50000000000000 : ℝ)^4767
        have hw : |(-117239659/1000000000 : ℝ)|=(117239659/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2813636199/5000000000 : ℝ)|^5791 ≤ (49734688290597/100000000000000 : ℝ)^4767
        have hw : |(2813636199/5000000000 : ℝ)|=(2813636199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1244851793/2500000000 : ℝ)|^5791 ≤ (4286751644021/10000000000000 : ℝ)^4767
        have hw : |(1244851793/2500000000 : ℝ)|=(1244851793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1751_s0_1 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1342657551/2500000000 : ℝ)*x 0 + (-1519787061/10000000000 : ℝ)*x 1 + (311212977/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342657551/2500000000 : ℝ)^5791 ≤ (23496432999077/50000000000000 : ℝ)^4767 := by
    have hnat : (1342657551 : ℕ)^5791*50000000000000^4767 ≤ 23496432999077^4767*2500000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342657551 2500000000 23496432999077 50000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1519787061/10000000000 : ℝ)^5791 ≤ (5069806370107/50000000000000 : ℝ)^4767 := by
    have hnat : (1519787061 : ℕ)^5791*50000000000000^4767 ≤ 5069806370107^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1519787061 10000000000 5069806370107 50000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (311212977/625000000 : ℝ)^5791 ≤ (21433760625503/50000000000000 : ℝ)^4767 := by
    have hnat : (311212977 : ℕ)^5791*50000000000000^4767 ≤ 21433760625503^4767*625000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      311212977 625000000 21433760625503 50000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342657551/2500000000 : ℝ), (-1519787061/10000000000 : ℝ), (311212977/625000000 : ℝ)] ![(23496432999077/50000000000000 : ℝ), (5069806370107/50000000000000 : ℝ), (21433760625503/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342657551/2500000000 : ℝ)|^5791 ≤ (23496432999077/50000000000000 : ℝ)^4767
        have hw : |(1342657551/2500000000 : ℝ)|=(1342657551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1519787061/10000000000 : ℝ)|^5791 ≤ (5069806370107/50000000000000 : ℝ)^4767
        have hw : |(-1519787061/10000000000 : ℝ)|=(1519787061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(311212977/625000000 : ℝ)|^5791 ≤ (21433760625503/50000000000000 : ℝ)^4767
        have hw : |(311212977/625000000 : ℝ)|=(311212977/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1751_s0_2 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5370632023/10000000000 : ℝ)*x 0 + (4979406599/10000000000 : ℝ)*x 1 + (-189973251/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370632023/10000000000 : ℝ)^5791 ≤ (11748221333329/25000000000000 : ℝ)^4767 := by
    have hnat : (5370632023 : ℕ)^5791*25000000000000^4767 ≤ 11748221333329^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370632023 10000000000 11748221333329 25000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4979406599/10000000000 : ℝ)^5791 ≤ (42867510447631/100000000000000 : ℝ)^4767 := by
    have hnat : (4979406599 : ℕ)^5791*100000000000000^4767 ≤ 42867510447631^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4979406599 10000000000 42867510447631 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (189973251/1250000000 : ℝ)^5791 ≤ (10139604205767/100000000000000 : ℝ)^4767 := by
    have hnat : (189973251 : ℕ)^5791*100000000000000^4767 ≤ 10139604205767^4767*1250000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      189973251 1250000000 10139604205767 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370632023/10000000000 : ℝ), (4979406599/10000000000 : ℝ), (-189973251/1250000000 : ℝ)] ![(11748221333329/25000000000000 : ℝ), (42867510447631/100000000000000 : ℝ), (10139604205767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370632023/10000000000 : ℝ)|^5791 ≤ (11748221333329/25000000000000 : ℝ)^4767
        have hw : |(5370632023/10000000000 : ℝ)|=(5370632023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4979406599/10000000000 : ℝ)|^5791 ≤ (42867510447631/100000000000000 : ℝ)^4767
        have hw : |(4979406599/10000000000 : ℝ)|=(4979406599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-189973251/1250000000 : ℝ)|^5791 ≤ (10139604205767/100000000000000 : ℝ)^4767
        have hw : |(-189973251/1250000000 : ℝ)|=(189973251/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1751_s0_3 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3976067549/10000000000 : ℝ)*x 0 + (2984803479/10000000000 : ℝ)*x 1 + (5122107967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3976067549/10000000000 : ℝ)^5791 ≤ (16307311152589/50000000000000 : ℝ)^4767 := by
    have hnat : (3976067549 : ℕ)^5791*50000000000000^4767 ≤ 16307311152589^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3976067549 10000000000 16307311152589 50000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2984803479/10000000000 : ℝ)^5791 ≤ (11510450373303/50000000000000 : ℝ)^4767 := by
    have hnat : (2984803479 : ℕ)^5791*50000000000000^4767 ≤ 11510450373303^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2984803479 10000000000 11510450373303 50000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5122107967/10000000000 : ℝ)^5791 ≤ (44364476932079/100000000000000 : ℝ)^4767 := by
    have hnat : (5122107967 : ℕ)^5791*100000000000000^4767 ≤ 44364476932079^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5122107967 10000000000 44364476932079 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3976067549/10000000000 : ℝ), (2984803479/10000000000 : ℝ), (5122107967/10000000000 : ℝ)] ![(16307311152589/50000000000000 : ℝ), (11510450373303/50000000000000 : ℝ), (44364476932079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3976067549/10000000000 : ℝ)|^5791 ≤ (16307311152589/50000000000000 : ℝ)^4767
        have hw : |(3976067549/10000000000 : ℝ)|=(3976067549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2984803479/10000000000 : ℝ)|^5791 ≤ (11510450373303/50000000000000 : ℝ)^4767
        have hw : |(2984803479/10000000000 : ℝ)|=(2984803479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5122107967/10000000000 : ℝ)|^5791 ≤ (44364476932079/100000000000000 : ℝ)^4767
        have hw : |(5122107967/10000000000 : ℝ)|=(5122107967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1751_s0_4 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1173739849/10000000000 : ℝ)*x 0 + (4995885489/10000000000 : ℝ)*x 1 + (561025103/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1173739849/10000000000 : ℝ)^5791 ≤ (1852023292767/25000000000000 : ℝ)^4767 := by
    have hnat : (1173739849 : ℕ)^5791*25000000000000^4767 ≤ 1852023292767^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1173739849 10000000000 1852023292767 25000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4995885489/10000000000 : ℝ)^5791 ≤ (5379989003743/12500000000000 : ℝ)^4767 := by
    have hnat : (4995885489 : ℕ)^5791*12500000000000^4767 ≤ 5379989003743^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4995885489 10000000000 5379989003743 12500000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (561025103/1000000000 : ℝ)^5791 ≤ (49551994785431/100000000000000 : ℝ)^4767 := by
    have hnat : (561025103 : ℕ)^5791*100000000000000^4767 ≤ 49551994785431^4767*1000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561025103 1000000000 49551994785431 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1173739849/10000000000 : ℝ), (4995885489/10000000000 : ℝ), (561025103/1000000000 : ℝ)] ![(1852023292767/25000000000000 : ℝ), (5379989003743/12500000000000 : ℝ), (49551994785431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1173739849/10000000000 : ℝ)|^5791 ≤ (1852023292767/25000000000000 : ℝ)^4767
        have hw : |(-1173739849/10000000000 : ℝ)|=(1173739849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4995885489/10000000000 : ℝ)|^5791 ≤ (5379989003743/12500000000000 : ℝ)^4767
        have hw : |(4995885489/10000000000 : ℝ)|=(4995885489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(561025103/1000000000 : ℝ)|^5791 ≤ (49551994785431/100000000000000 : ℝ)^4767
        have hw : |(561025103/1000000000 : ℝ)|=(561025103/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1751_s0_5 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5197838373/10000000000 : ℝ)*x 0 + (-177788457/2000000000 : ℝ)*x 1 + (5610251123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5197838373/10000000000 : ℝ)^5791 ≤ (45162566793999/100000000000000 : ℝ)^4767 := by
    have hnat : (5197838373 : ℕ)^5791*100000000000000^4767 ≤ 45162566793999^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5197838373 10000000000 45162566793999 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (177788457/2000000000 : ℝ)^5791 ≤ (5285437414571/100000000000000 : ℝ)^4767 := by
    have hnat : (177788457 : ℕ)^5791*100000000000000^4767 ≤ 5285437414571^4767*2000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177788457 2000000000 5285437414571 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5610251123/10000000000 : ℝ)^5791 ≤ (12387998945823/25000000000000 : ℝ)^4767 := by
    have hnat : (5610251123 : ℕ)^5791*25000000000000^4767 ≤ 12387998945823^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5610251123 10000000000 12387998945823 25000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5197838373/10000000000 : ℝ), (-177788457/2000000000 : ℝ), (5610251123/10000000000 : ℝ)] ![(45162566793999/100000000000000 : ℝ), (5285437414571/100000000000000 : ℝ), (12387998945823/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5197838373/10000000000 : ℝ)|^5791 ≤ (45162566793999/100000000000000 : ℝ)^4767
        have hw : |(5197838373/10000000000 : ℝ)|=(5197838373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-177788457/2000000000 : ℝ)|^5791 ≤ (5285437414571/100000000000000 : ℝ)^4767
        have hw : |(-177788457/2000000000 : ℝ)|=(177788457/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5610251123/10000000000 : ℝ)|^5791 ≤ (12387998945823/25000000000000 : ℝ)^4767
        have hw : |(5610251123/10000000000 : ℝ)|=(5610251123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1751_s0_6 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (40608109/78125000 : ℝ)*x 0 + (5610251137/10000000000 : ℝ)*x 1 + (-888942879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (40608109/78125000 : ℝ)^5791 ≤ (22581281175141/50000000000000 : ℝ)^4767 := by
    have hnat : (40608109 : ℕ)^5791*50000000000000^4767 ≤ 22581281175141^4767*78125000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40608109 78125000 22581281175141 50000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5610251137/10000000000 : ℝ)^5791 ≤ (12387998983377/25000000000000 : ℝ)^4767 := by
    have hnat : (5610251137 : ℕ)^5791*25000000000000^4767 ≤ 12387998983377^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5610251137 10000000000 12387998983377 25000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (888942879/10000000000 : ℝ)^5791 ≤ (660680213127/12500000000000 : ℝ)^4767 := by
    have hnat : (888942879 : ℕ)^5791*12500000000000^4767 ≤ 660680213127^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      888942879 10000000000 660680213127 12500000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(40608109/78125000 : ℝ), (5610251137/10000000000 : ℝ), (-888942879/10000000000 : ℝ)] ![(22581281175141/50000000000000 : ℝ), (12387998983377/25000000000000 : ℝ), (660680213127/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(40608109/78125000 : ℝ)|^5791 ≤ (22581281175141/50000000000000 : ℝ)^4767
        have hw : |(40608109/78125000 : ℝ)|=(40608109/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5610251137/10000000000 : ℝ)|^5791 ≤ (12387998983377/25000000000000 : ℝ)^4767
        have hw : |(5610251137/10000000000 : ℝ)|=(5610251137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-888942879/10000000000 : ℝ)|^5791 ≤ (660680213127/12500000000000 : ℝ)^4767
        have hw : |(-888942879/10000000000 : ℝ)|=(888942879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1751_s0_7 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3980499657/10000000000 : ℝ)*x 0 + (1266936153/2500000000 : ℝ)*x 1 + (608191321/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3980499657/10000000000 : ℝ)^5791 ≤ (32658792500971/100000000000000 : ℝ)^4767 := by
    have hnat : (3980499657 : ℕ)^5791*100000000000000^4767 ≤ 32658792500971^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3980499657 10000000000 32658792500971 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1266936153/2500000000 : ℝ)^5791 ≤ (4379312386219/10000000000000 : ℝ)^4767 := by
    have hnat : (1266936153 : ℕ)^5791*10000000000000^4767 ≤ 4379312386219^4767*2500000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1266936153 2500000000 4379312386219 10000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (608191321/2000000000 : ℝ)^5791 ≤ (5887020907243/25000000000000 : ℝ)^4767 := by
    have hnat : (608191321 : ℕ)^5791*25000000000000^4767 ≤ 5887020907243^4767*2000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      608191321 2000000000 5887020907243 25000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3980499657/10000000000 : ℝ), (1266936153/2500000000 : ℝ), (608191321/2000000000 : ℝ)] ![(32658792500971/100000000000000 : ℝ), (4379312386219/10000000000000 : ℝ), (5887020907243/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3980499657/10000000000 : ℝ)|^5791 ≤ (32658792500971/100000000000000 : ℝ)^4767
        have hw : |(3980499657/10000000000 : ℝ)|=(3980499657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1266936153/2500000000 : ℝ)|^5791 ≤ (4379312386219/10000000000000 : ℝ)^4767
        have hw : |(1266936153/2500000000 : ℝ)|=(1266936153/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(608191321/2000000000 : ℝ)|^5791 ≤ (5887020907243/25000000000000 : ℝ)^4767
        have hw : |(608191321/2000000000 : ℝ)|=(608191321/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1751_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42989923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1353/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20773/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (5775/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5775 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5775*1^1024 ≤ 0^1024*1^5775 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5775 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5775 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5775/1024 : ℝ) ≤ (284923490573543419/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5775 ≤ (284923490573543419/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5775*50000000000000000000^1024 ≤ 284923490573543419^1024*5^5775 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 284923490573543419 50000000000000000000 5775 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (284923490573543419/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5775 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5775/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5775 := by
      have hnat : (1 : ℕ)^1024*1^5775 ≤ 1^5775*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5775 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5775 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50284923490573543419/50000000000000000000 : ℝ) ≤ (10010080696709913/10000000000000000 : ℝ) ^ (5775/1024 : ℝ) := by
    have hpowers : (50284923490573543419/50000000000000000000 : ℝ)^1024 ≤ (10010080696709913/10000000000000000 : ℝ)^5775 := by
      have hnat : (50284923490573543419 : ℕ)^1024*10000000000000000^5775 ≤ 10010080696709913^5775*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50284923490573543419 50000000000000000000 10010080696709913 10000000000000000 1024 5775 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10010080696709913/10000000000000000 : ℝ)) (X := (50284923490573543419/50000000000000000000 : ℝ)) (by norm_num) 5775 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25284923490573543419/25000000000000000000 : ℝ) ≤ (5010080696709913/5000000000000000 : ℝ) ^ (5775/1024 : ℝ) := by
    have hpowers : (25284923490573543419/25000000000000000000 : ℝ)^1024 ≤ (5010080696709913/5000000000000000 : ℝ)^5775 := by
      have hnat : (25284923490573543419 : ℕ)^1024*5000000000000000^5775 ≤ 5010080696709913^5775*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25284923490573543419 25000000000000000000 5010080696709913 5000000000000000 1024 5775 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5010080696709913/5000000000000000 : ℝ)) (X := (25284923490573543419/25000000000000000000 : ℝ)) (by norm_num) 5775 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(10080696709913/4000000000000000 : ℝ)*(0 : ℝ))^(5775/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(10080696709913/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(284923490573543419/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(10080696709913/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5775/1024 : ℝ) := by
    rw [show (1 : ℝ)+(10080696709913/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10010080696709913/10000000000000000 : ℝ) by norm_num, show 1+(284923490573543419/50000000000000000000 : ℝ)+(0 : ℝ)=(50284923490573543419/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(284923490573543419/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(10080696709913/4000000000000000 : ℝ)*(2/5 : ℝ))^(5775/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(10080696709913/4000000000000000 : ℝ)*(2/5 : ℝ)=(5010080696709913/5000000000000000 : ℝ) by norm_num, show 1+2*(284923490573543419/50000000000000000000 : ℝ)=(25284923490573543419/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(10080696709913/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5775/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (10080696709913/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(10080696709913/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5775/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (10080696709913/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(10080696709913/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5775/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (10080696709913/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-117239659/1000000000 : ℝ)*X 0 0+(2813636199/5000000000 : ℝ)*X 0 1+(1244851793/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1342657551/2500000000 : ℝ)*X 1 0+(-1519787061/10000000000 : ℝ)*X 1 1+(311212977/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5370632023/10000000000 : ℝ)*X 2 0+(4979406599/10000000000 : ℝ)*X 2 1+(-189973251/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((3976067549/10000000000 : ℝ)*X 0 0+(2984803479/10000000000 : ℝ)*X 0 1+(5122107967/10000000000 : ℝ)*X 0 2+(3976067549/10000000000 : ℝ)*X 1 0+(2984803479/10000000000 : ℝ)*X 1 1+(5122107967/10000000000 : ℝ)*X 1 2+(3976067549/10000000000 : ℝ)*X 2 0+(2984803479/10000000000 : ℝ)*X 2 1+(5122107967/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1173739849/10000000000 : ℝ)*X 0 0+(4995885489/10000000000 : ℝ)*X 0 1+(561025103/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5197838373/10000000000 : ℝ)*X 1 0+(-177788457/2000000000 : ℝ)*X 1 1+(5610251123/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((40608109/78125000 : ℝ)*X 2 0+(5610251137/10000000000 : ℝ)*X 2 1+(-888942879/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3980499657/10000000000 : ℝ)*X 0 0+(1266936153/2500000000 : ℝ)*X 0 1+(608191321/2000000000 : ℝ)*X 0 2+(3980499657/10000000000 : ℝ)*X 1 0+(1266936153/2500000000 : ℝ)*X 1 1+(608191321/2000000000 : ℝ)*X 1 2+(3980499657/10000000000 : ℝ)*X 2 0+(1266936153/2500000000 : ℝ)*X 2 1+(608191321/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (736805101912526002009539/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (245322201/20000000000000 : ℝ)*(base19) + (1619530449/100000000000000 : ℝ)*(base23) + (4938513/25000000000000 : ℝ)*(base24) + (59139033/100000000000000 : ℝ)*(upper4) + (214282269/50000000000000 : ℝ)*(upper5) + (1005715161911799/100000000000000 : ℝ)*(major0) + (1005715161911799/100000000000000 : ℝ)*(major1) + (1005715161911799/100000000000000 : ℝ)*(major2) + (38588376216333/2500000000000 : ℝ)*(sp0) + (771772354796897/50000000000000 : ℝ)*(sp1) + (771772148460149/50000000000000 : ℝ)*(sp2) + (467882065708929/100000000000000 : ℝ)*(sp3) + (10887551479/100000000000000 : ℝ)*(sp4) + (1038154083/50000000000000 : ℝ)*(sp7) + (93576828403419/20000000000000 : ℝ)*(f.failure) + (1543545936204799/100000000000000 : ℝ)*(f.sum) + (799394672563487/200000000000000000000000000000 : ℝ)*base65 + (1452655674636513/400000000000000000000000000000 : ℝ)*base68 + (2081512878236513/400000000000000000000000000000 : ℝ)*base70 + (2095031171363487/400000000000000000000000000000 : ℝ)*base71 + (233957165163487/200000000000000000000000000000 : ℝ)*base73 + (2751933437436513/400000000000000000000000000000 : ℝ)*base76 + (458971620163487/400000000000000000000000000000 : ℝ)*base77 + (594494439036513/400000000000000000000000000000 : ℝ)*base80 + (341173717163487/200000000000000000000000000000 : ℝ)*base81 + (253263/400000000000000000000 : ℝ)*base90 + (253263/400000000000000000000 : ℝ)*base92 + (253263/400000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1755853105397859485060259/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (387813757/20000000000000 : ℝ)*(base19) + (1811925851/100000000000000 : ℝ)*(base23) + (917151/4000000000000 : ℝ)*(upper2) + (331869819/100000000000000 : ℝ)*(upper3) + (296755731/100000000000000 : ℝ)*(upper5) + (1060543176827319/100000000000000 : ℝ)*(major0) + (1060543176827319/100000000000000 : ℝ)*(major1) + (1060543176827319/100000000000000 : ℝ)*(major2) + (8472311271/100000000000000 : ℝ)*(sp1) + (1457282231/20000000000000 : ℝ)*(sp2) + (406923634771061/25000000000000 : ℝ)*(sp4) + (406921031926047/25000000000000 : ℝ)*(sp5) + (813842720373619/50000000000000 : ℝ)*(sp6) + (246695760964103/50000000000000 : ℝ)*(sp7) + (246695760964103/50000000000000 : ℝ)*(f.failure) + (406923634771061/25000000000000 : ℝ)*(f.sum) + (473467799313247/200000000000000000000000000000 : ℝ)*base65 + (733440481313247/400000000000000000000000000000 : ℝ)*base67 + (776083743486753/400000000000000000000000000000 : ℝ)*base70 + (1149599263486753/400000000000000000000000000000 : ℝ)*base72 + (497170644313247/200000000000000000000000000000 : ℝ)*base73 + (2567304573886753/400000000000000000000000000000 : ℝ)*base76 + (2030222356686753/400000000000000000000000000000 : ℝ)*base78 + (2628633972686753/400000000000000000000000000000 : ℝ)*base80 + (873952398913247/200000000000000000000000000000 : ℝ)*base81 + (3734069/1000000000000000000000 : ℝ)*base89 + (3734069/1000000000000000000000 : ℝ)*base91 + (3734069/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1751_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42989923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1353/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20773/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1751_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1751_s1_0 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1215610381/10000000000 : ℝ)*x 0 + (5498860399/10000000000 : ℝ)*x 1 + (5078902393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1215610381/10000000000 : ℝ)^5791 ≤ (7730346219713/100000000000000 : ℝ)^4767 := by
    have hnat : (1215610381 : ℕ)^5791*100000000000000^4767 ≤ 7730346219713^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1215610381 10000000000 7730346219713 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5498860399/10000000000 : ℝ)^5791 ≤ (24179684860193/50000000000000 : ℝ)^4767 := by
    have hnat : (5498860399 : ℕ)^5791*50000000000000^4767 ≤ 24179684860193^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5498860399 10000000000 24179684860193 50000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5078902393/10000000000 : ℝ)^5791 ≤ (8782056811129/20000000000000 : ℝ)^4767 := by
    have hnat : (5078902393 : ℕ)^5791*20000000000000^4767 ≤ 8782056811129^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5078902393 10000000000 8782056811129 20000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1215610381/10000000000 : ℝ), (5498860399/10000000000 : ℝ), (5078902393/10000000000 : ℝ)] ![(7730346219713/100000000000000 : ℝ), (24179684860193/50000000000000 : ℝ), (8782056811129/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1215610381/10000000000 : ℝ)|^5791 ≤ (7730346219713/100000000000000 : ℝ)^4767
        have hw : |(-1215610381/10000000000 : ℝ)|=(1215610381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5498860399/10000000000 : ℝ)|^5791 ≤ (24179684860193/50000000000000 : ℝ)^4767
        have hw : |(5498860399/10000000000 : ℝ)|=(5498860399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5078902393/10000000000 : ℝ)|^5791 ≤ (8782056811129/20000000000000 : ℝ)^4767
        have hw : |(5078902393/10000000000 : ℝ)|=(5078902393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1751_s1_1 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1334117197/2500000000 : ℝ)*x 0 + (-1435389561/10000000000 : ℝ)*x 1 + (2539451243/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1334117197/2500000000 : ℝ)^5791 ≤ (46629993828827/100000000000000 : ℝ)^4767 := by
    have hnat : (1334117197 : ℕ)^5791*100000000000000^4767 ≤ 46629993828827^4767*2500000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1334117197 2500000000 46629993828827 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1435389561/10000000000 : ℝ)^5791 ≤ (2364930281637/25000000000000 : ℝ)^4767 := by
    have hnat : (1435389561 : ℕ)^5791*25000000000000^4767 ≤ 2364930281637^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1435389561 10000000000 2364930281637 25000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2539451243/5000000000 : ℝ)^5791 ≤ (8782057006481/20000000000000 : ℝ)^4767 := by
    have hnat : (2539451243 : ℕ)^5791*20000000000000^4767 ≤ 8782057006481^4767*5000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2539451243 5000000000 8782057006481 20000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1334117197/2500000000 : ℝ), (-1435389561/10000000000 : ℝ), (2539451243/5000000000 : ℝ)] ![(46629993828827/100000000000000 : ℝ), (2364930281637/25000000000000 : ℝ), (8782057006481/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1334117197/2500000000 : ℝ)|^5791 ≤ (46629993828827/100000000000000 : ℝ)^4767
        have hw : |(1334117197/2500000000 : ℝ)|=(1334117197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1435389561/10000000000 : ℝ)|^5791 ≤ (2364930281637/25000000000000 : ℝ)^4767
        have hw : |(-1435389561/10000000000 : ℝ)|=(1435389561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2539451243/5000000000 : ℝ)|^5791 ≤ (8782057006481/20000000000000 : ℝ)^4767
        have hw : |(2539451243/5000000000 : ℝ)|=(2539451243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1751_s1_2 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (83382333/156250000 : ℝ)*x 0 + (5078901943/10000000000 : ℝ)*x 1 + (-1435389577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83382333/156250000 : ℝ)^5791 ≤ (9325999878217/20000000000000 : ℝ)^4767 := by
    have hnat : (83382333 : ℕ)^5791*20000000000000^4767 ≤ 9325999878217^4767*156250000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83382333 156250000 9325999878217 20000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5078901943/10000000000 : ℝ)^5791 ≤ (43910279329389/100000000000000 : ℝ)^4767 := by
    have hnat : (5078901943 : ℕ)^5791*100000000000000^4767 ≤ 43910279329389^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5078901943 10000000000 43910279329389 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1435389577/10000000000 : ℝ)^5791 ≤ (1891944250929/20000000000000 : ℝ)^4767 := by
    have hnat : (1435389577 : ℕ)^5791*20000000000000^4767 ≤ 1891944250929^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1435389577 10000000000 1891944250929 20000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83382333/156250000 : ℝ), (5078901943/10000000000 : ℝ), (-1435389577/10000000000 : ℝ)] ![(9325999878217/20000000000000 : ℝ), (43910279329389/100000000000000 : ℝ), (1891944250929/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83382333/156250000 : ℝ)|^5791 ≤ (9325999878217/20000000000000 : ℝ)^4767
        have hw : |(83382333/156250000 : ℝ)|=(83382333/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5078901943/10000000000 : ℝ)|^5791 ≤ (43910279329389/100000000000000 : ℝ)^4767
        have hw : |(5078901943/10000000000 : ℝ)|=(5078901943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1435389577/10000000000 : ℝ)|^5791 ≤ (1891944250929/20000000000000 : ℝ)^4767
        have hw : |(-1435389577/10000000000 : ℝ)|=(1435389577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1751_s1_3 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1004494687/2500000000 : ℝ)*x 0 + (209849293/625000000 : ℝ)*x 1 + (2371514047/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1004494687/2500000000 : ℝ)^5791 ≤ (33032729031617/100000000000000 : ℝ)^4767 := by
    have hnat : (1004494687 : ℕ)^5791*100000000000000^4767 ≤ 33032729031617^4767*2500000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004494687 2500000000 33032729031617 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209849293/625000000 : ℝ)^5791 ≤ (6639775490523/25000000000000 : ℝ)^4767 := by
    have hnat : (209849293 : ℕ)^5791*25000000000000^4767 ≤ 6639775490523^4767*625000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209849293 625000000 6639775490523 25000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2371514047/5000000000 : ℝ)^5791 ≤ (10102042247583/25000000000000 : ℝ)^4767 := by
    have hnat : (2371514047 : ℕ)^5791*25000000000000^4767 ≤ 10102042247583^4767*5000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2371514047 5000000000 10102042247583 25000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1004494687/2500000000 : ℝ), (209849293/625000000 : ℝ), (2371514047/5000000000 : ℝ)] ![(33032729031617/100000000000000 : ℝ), (6639775490523/25000000000000 : ℝ), (10102042247583/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1004494687/2500000000 : ℝ)|^5791 ≤ (33032729031617/100000000000000 : ℝ)^4767
        have hw : |(1004494687/2500000000 : ℝ)|=(1004494687/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209849293/625000000 : ℝ)|^5791 ≤ (6639775490523/25000000000000 : ℝ)^4767
        have hw : |(209849293/625000000 : ℝ)|=(209849293/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2371514047/5000000000 : ℝ)|^5791 ≤ (10102042247583/25000000000000 : ℝ)^4767
        have hw : |(2371514047/5000000000 : ℝ)|=(2371514047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1751_s1_4 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-607987133/5000000000 : ℝ)*x 0 + (2542918721/5000000000 : ℝ)*x 1 + (1098355517/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (607987133/5000000000 : ℝ)^5791 ≤ (773315741537/10000000000000 : ℝ)^4767 := by
    have hnat : (607987133 : ℕ)^5791*10000000000000^4767 ≤ 773315741537^4767*5000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      607987133 5000000000 773315741537 10000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2542918721/5000000000 : ℝ)^5791 ≤ (21991566057943/50000000000000 : ℝ)^4767 := by
    have hnat : (2542918721 : ℕ)^5791*50000000000000^4767 ≤ 21991566057943^4767*5000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2542918721 5000000000 21991566057943 50000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1098355517/2000000000 : ℝ)^5791 ≤ (24141855230861/50000000000000 : ℝ)^4767 := by
    have hnat : (1098355517 : ℕ)^5791*50000000000000^4767 ≤ 24141855230861^4767*2000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098355517 2000000000 24141855230861 50000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-607987133/5000000000 : ℝ), (2542918721/5000000000 : ℝ), (1098355517/2000000000 : ℝ)] ![(773315741537/10000000000000 : ℝ), (21991566057943/50000000000000 : ℝ), (24141855230861/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-607987133/5000000000 : ℝ)|^5791 ≤ (773315741537/10000000000000 : ℝ)^4767
        have hw : |(-607987133/5000000000 : ℝ)|=(607987133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2542918721/5000000000 : ℝ)|^5791 ≤ (21991566057943/50000000000000 : ℝ)^4767
        have hw : |(2542918721/5000000000 : ℝ)|=(2542918721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1098355517/2000000000 : ℝ)|^5791 ≤ (24141855230861/50000000000000 : ℝ)^4767
        have hw : |(1098355517/2000000000 : ℝ)|=(1098355517/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1751_s1_5 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5225155787/10000000000 : ℝ)*x 0 + (-511257243/5000000000 : ℝ)*x 1 + (2745888773/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5225155787/10000000000 : ℝ)^5791 ≤ (9090213726447/20000000000000 : ℝ)^4767 := by
    have hnat : (5225155787 : ℕ)^5791*20000000000000^4767 ≤ 9090213726447^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225155787 10000000000 9090213726447 20000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (511257243/5000000000 : ℝ)^5791 ≤ (6265221310273/100000000000000 : ℝ)^4767 := by
    have hnat : (511257243 : ℕ)^5791*100000000000000^4767 ≤ 6265221310273^4767*5000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511257243 5000000000 6265221310273 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2745888773/5000000000 : ℝ)^5791 ≤ (24141855022589/50000000000000 : ℝ)^4767 := by
    have hnat : (2745888773 : ℕ)^5791*50000000000000^4767 ≤ 24141855022589^4767*5000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2745888773 5000000000 24141855022589 50000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5225155787/10000000000 : ℝ), (-511257243/5000000000 : ℝ), (2745888773/5000000000 : ℝ)] ![(9090213726447/20000000000000 : ℝ), (6265221310273/100000000000000 : ℝ), (24141855022589/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5225155787/10000000000 : ℝ)|^5791 ≤ (9090213726447/20000000000000 : ℝ)^4767
        have hw : |(5225155787/10000000000 : ℝ)|=(5225155787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-511257243/5000000000 : ℝ)|^5791 ≤ (6265221310273/100000000000000 : ℝ)^4767
        have hw : |(-511257243/5000000000 : ℝ)|=(511257243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2745888773/5000000000 : ℝ)|^5791 ≤ (24141855022589/50000000000000 : ℝ)^4767
        have hw : |(2745888773/5000000000 : ℝ)|=(2745888773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1751_s1_6 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5102691/9765625 : ℝ)*x 0 + (5491777653/10000000000 : ℝ)*x 1 + (-51125731/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5102691/9765625 : ℝ)^5791 ≤ (45451066487127/100000000000000 : ℝ)^4767 := by
    have hnat : (5102691 : ℕ)^5791*100000000000000^4767 ≤ 45451066487127^4767*9765625^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5102691 9765625 45451066487127 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5491777653/10000000000 : ℝ)^5791 ≤ (48283711188003/100000000000000 : ℝ)^4767 := by
    have hnat : (5491777653 : ℕ)^5791*100000000000000^4767 ≤ 48283711188003^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5491777653 10000000000 48283711188003 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51125731/500000000 : ℝ)^5791 ≤ (3132611153849/50000000000000 : ℝ)^4767 := by
    have hnat : (51125731 : ℕ)^5791*50000000000000^4767 ≤ 3132611153849^4767*500000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51125731 500000000 3132611153849 50000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5102691/9765625 : ℝ), (5491777653/10000000000 : ℝ), (-51125731/500000000 : ℝ)] ![(45451066487127/100000000000000 : ℝ), (48283711188003/100000000000000 : ℝ), (3132611153849/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5102691/9765625 : ℝ)|^5791 ≤ (45451066487127/100000000000000 : ℝ)^4767
        have hw : |(5102691/9765625 : ℝ)|=(5102691/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5491777653/10000000000 : ℝ)|^5791 ≤ (48283711188003/100000000000000 : ℝ)^4767
        have hw : |(5491777653/10000000000 : ℝ)|=(5491777653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-51125731/500000000 : ℝ)|^5791 ≤ (3132611153849/50000000000000 : ℝ)^4767
        have hw : |(-51125731/500000000 : ℝ)|=(51125731/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1751_s1_7 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (803835363/2000000000 : ℝ)*x 0 + (2360073733/5000000000 : ℝ)*x 1 + (3380956359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (803835363/2000000000 : ℝ)^5791 ≤ (33044694790457/100000000000000 : ℝ)^4767 := by
    have hnat : (803835363 : ℕ)^5791*100000000000000^4767 ≤ 33044694790457^4767*2000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      803835363 2000000000 33044694790457 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2360073733/5000000000 : ℝ)^5791 ≤ (4017148740769/10000000000000 : ℝ)^4767 := by
    have hnat : (2360073733 : ℕ)^5791*10000000000000^4767 ≤ 4017148740769^4767*5000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2360073733 5000000000 4017148740769 10000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3380956359/10000000000 : ℝ)^5791 ≤ (26783817789209/100000000000000 : ℝ)^4767 := by
    have hnat : (3380956359 : ℕ)^5791*100000000000000^4767 ≤ 26783817789209^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3380956359 10000000000 26783817789209 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(803835363/2000000000 : ℝ), (2360073733/5000000000 : ℝ), (3380956359/10000000000 : ℝ)] ![(33044694790457/100000000000000 : ℝ), (4017148740769/10000000000000 : ℝ), (26783817789209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(803835363/2000000000 : ℝ)|^5791 ≤ (33044694790457/100000000000000 : ℝ)^4767
        have hw : |(803835363/2000000000 : ℝ)|=(803835363/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2360073733/5000000000 : ℝ)|^5791 ≤ (4017148740769/10000000000000 : ℝ)^4767
        have hw : |(2360073733/5000000000 : ℝ)|=(2360073733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3380956359/10000000000 : ℝ)|^5791 ≤ (26783817789209/100000000000000 : ℝ)^4767
        have hw : |(3380956359/10000000000 : ℝ)|=(3380956359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1751_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42989923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20773/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1353/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (8997/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2253/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20773/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1353/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20773/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1353/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20773/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1353/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20773/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1353/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20773/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1353/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20773/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1353/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1353/20000 : ℝ) ^ (5775/1024 : ℝ) ≤ (12650032333717/50000000000000000000 : ℝ) := by
    have hpowers : (1353/20000 : ℝ)^5775 ≤ (12650032333717/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1353 : ℕ)^5775*50000000000000000000^1024 ≤ 12650032333717^1024*20000^5775 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1353 20000 12650032333717 50000000000000000000 5775 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1353/20000 : ℝ)) (X := (12650032333717/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5775 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (20773/100000 : ℝ) ^ (5775/1024 : ℝ) ≤ (2831167370625817/20000000000000000000 : ℝ) := by
    have hpowers : (20773/100000 : ℝ)^5775 ≤ (2831167370625817/20000000000000000000 : ℝ)^1024 := by
      have hnat : (20773 : ℕ)^5775*20000000000000000000^1024 ≤ 2831167370625817^1024*100000^5775 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20773 100000 2831167370625817 20000000000000000000 5775 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20773/100000 : ℝ)) (X := (2831167370625817/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5775 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000012650032333717/25000000000000000000 : ℝ) ≤ (2000000179444231/2000000000000000 : ℝ) ^ (5775/1024 : ℝ) := by
    have hpowers : (25000012650032333717/25000000000000000000 : ℝ)^1024 ≤ (2000000179444231/2000000000000000 : ℝ)^5775 := by
      have hnat : (25000012650032333717 : ℕ)^1024*2000000000000000^5775 ≤ 2000000179444231^5775*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000012650032333717 25000000000000000000 2000000179444231 2000000000000000 1024 5775 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000179444231/2000000000000000 : ℝ)) (X := (25000012650032333717/25000000000000000000 : ℝ)) (by norm_num) 5775 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100014181136917796519/100000000000000000000 : ℝ) ≤ (10000251439605117/10000000000000000 : ℝ) ^ (5775/1024 : ℝ) := by
    have hpowers : (100014181136917796519/100000000000000000000 : ℝ)^1024 ≤ (10000251439605117/10000000000000000 : ℝ)^5775 := by
      have hnat : (100014181136917796519 : ℕ)^1024*10000000000000000^5775 ≤ 10000251439605117^5775*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100014181136917796519 100000000000000000000 10000251439605117 10000000000000000 1024 5775 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000251439605117/10000000000000000 : ℝ)) (X := (100014181136917796519/100000000000000000000 : ℝ)) (by norm_num) 5775 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10002831167370625817/10000000000000000000 : ℝ) ≤ (10000501981989079/10000000000000000 : ℝ) ^ (5775/1024 : ℝ) := by
    have hpowers : (10002831167370625817/10000000000000000000 : ℝ)^1024 ≤ (10000501981989079/10000000000000000 : ℝ)^5775 := by
      have hnat : (10002831167370625817 : ℕ)^1024*10000000000000000^5775 ≤ 10000501981989079^5775*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002831167370625817 10000000000000000000 10000501981989079 10000000000000000 1024 5775 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000501981989079/10000000000000000 : ℝ)) (X := (10002831167370625817/10000000000000000000 : ℝ)) (by norm_num) 5775 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(12650032333717/50000000000000000000 : ℝ) ≤ ((7003831136490946669/7004000000000000000 : ℝ)+2*(125271191981/700400000000000 : ℝ)*(1353/20000 : ℝ))^(5775/1024 : ℝ) := by
    rw [show (7003831136490946669/7004000000000000000 : ℝ)+2*(125271191981/700400000000000 : ℝ)*(1353/20000 : ℝ)=(2000000179444231/2000000000000000 : ℝ) by norm_num, show 1+2*(12650032333717/50000000000000000000 : ℝ)=(25000012650032333717/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2831167370625817/20000000000000000000 : ℝ)+(12650032333717/50000000000000000000 : ℝ) ≤ ((7003831136490946669/7004000000000000000 : ℝ)+(125271191981/700400000000000 : ℝ)*((20773/100000 : ℝ)+(1353/20000 : ℝ)))^(5775/1024 : ℝ) := by
    rw [show (7003831136490946669/7004000000000000000 : ℝ)+(125271191981/700400000000000 : ℝ)*((20773/100000 : ℝ)+(1353/20000 : ℝ))=(10000251439605117/10000000000000000 : ℝ) by norm_num, show 1+(2831167370625817/20000000000000000000 : ℝ)+(12650032333717/50000000000000000000 : ℝ)=(100014181136917796519/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2831167370625817/20000000000000000000 : ℝ) ≤ ((7003831136490946669/7004000000000000000 : ℝ)+2*(125271191981/700400000000000 : ℝ)*(20773/100000 : ℝ))^(5775/1024 : ℝ) := by
    rw [show (7003831136490946669/7004000000000000000 : ℝ)+2*(125271191981/700400000000000 : ℝ)*(20773/100000 : ℝ)=(10000501981989079/10000000000000000 : ℝ) by norm_num, show 1+2*(2831167370625817/20000000000000000000 : ℝ)=(10002831167370625817/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7003831136490946669/7004000000000000000 : ℝ)*(X 1 0+X 2 0)+(125271191981/700400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5775/1024 : ℝ)) (lo := (1353/20000 : ℝ)) (hi := (20773/100000 : ℝ)) (c := (7003831136490946669/7004000000000000000 : ℝ)) (alpha := (125271191981/700400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7003831136490946669/7004000000000000000 : ℝ)*(X 0 1+X 2 1)+(125271191981/700400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5775/1024 : ℝ)) (lo := (1353/20000 : ℝ)) (hi := (20773/100000 : ℝ)) (c := (7003831136490946669/7004000000000000000 : ℝ)) (alpha := (125271191981/700400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7003831136490946669/7004000000000000000 : ℝ)*(X 0 2+X 1 2)+(125271191981/700400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5775/1024 : ℝ)) (lo := (1353/20000 : ℝ)) (hi := (20773/100000 : ℝ)) (c := (7003831136490946669/7004000000000000000 : ℝ)) (alpha := (125271191981/700400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1215610381/10000000000 : ℝ)*X 0 0+(5498860399/10000000000 : ℝ)*X 0 1+(5078902393/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1334117197/2500000000 : ℝ)*X 1 0+(-1435389561/10000000000 : ℝ)*X 1 1+(2539451243/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((83382333/156250000 : ℝ)*X 2 0+(5078901943/10000000000 : ℝ)*X 2 1+(-1435389577/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1004494687/2500000000 : ℝ)*X 0 0+(209849293/625000000 : ℝ)*X 0 1+(2371514047/5000000000 : ℝ)*X 0 2+(1004494687/2500000000 : ℝ)*X 1 0+(209849293/625000000 : ℝ)*X 1 1+(2371514047/5000000000 : ℝ)*X 1 2+(1004494687/2500000000 : ℝ)*X 2 0+(209849293/625000000 : ℝ)*X 2 1+(2371514047/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-607987133/5000000000 : ℝ)*X 0 0+(2542918721/5000000000 : ℝ)*X 0 1+(1098355517/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5225155787/10000000000 : ℝ)*X 1 0+(-511257243/5000000000 : ℝ)*X 1 1+(2745888773/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5102691/9765625 : ℝ)*X 2 0+(5491777653/10000000000 : ℝ)*X 2 1+(-51125731/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((803835363/2000000000 : ℝ)*X 0 0+(2360073733/5000000000 : ℝ)*X 0 1+(3380956359/10000000000 : ℝ)*X 0 2+(803835363/2000000000 : ℝ)*X 1 0+(2360073733/5000000000 : ℝ)*X 1 1+(3380956359/10000000000 : ℝ)*X 1 2+(803835363/2000000000 : ℝ)*X 2 0+(2360073733/5000000000 : ℝ)*X 2 1+(3380956359/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20718577400421810171267/2060000000000000000000000000 : ℝ) := by norm_num
    linear_combination (95188047/6250000000000 : ℝ)*(base19) + (405601633/25000000000000 : ℝ)*(base23) + (71732167/100000000000000 : ℝ)*(lower2) + (297324511/100000000000000 : ℝ)*(upper3) + (43037429/20000000000000 : ℝ)*(upper5) + (1551506837904187/100000000000000 : ℝ)*(major0) + (1551506837904187/100000000000000 : ℝ)*(major1) + (1551506837904187/100000000000000 : ℝ)*(major2) + (595300403044889/25000000000000 : ℝ)*(sp0) + (476242315420643/20000000000000 : ℝ)*(sp1) + (476242295541087/20000000000000 : ℝ)*(sp2) + (360898024099299/50000000000000 : ℝ)*(sp3) + (11487932411/100000000000000 : ℝ)*(sp4) + (262015359/6250000000000 : ℝ)*(sp7) + (360900120222171/50000000000000 : ℝ)*(f.failure) + (2381213100111967/100000000000000 : ℝ)*(f.sum) + (3174101109671/2060000000000000000000000000 : ℝ)*base65 + (76951221596451359/41200000000000000000000000000000 : ℝ)*base67 + (241112927423948641/41200000000000000000000000000000 : ℝ)*base70 + (381740509743548641/41200000000000000000000000000000 : ℝ)*base72 + (8322265627011/2060000000000000000000000000 : ℝ)*base73 + (100714921639651359/41200000000000000000000000000000 : ℝ)*base75 + (124288190503548641/41200000000000000000000000000000 : ℝ)*base78 + (18932363997651359/41200000000000000000000000000000 : ℝ)*base79 + (4892720480989/2060000000000000000000000000 : ℝ)*base82 + (4182833/1000000000000000000000 : ℝ)*base89 + (4182833/1000000000000000000000 : ℝ)*base91 + (4182833/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (223357763260694317636332189/17510000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (73015323/4000000000000 : ℝ)*(base19) + (941288577/50000000000000 : ℝ)*(base23) + (9456359/10000000000000 : ℝ)*(upper2) + (281333549/100000000000000 : ℝ)*(upper3) + (425451053/100000000000000 : ℝ)*(upper5) + (80253431602009/5000000000000 : ℝ)*(major0) + (80253431602009/5000000000000 : ℝ)*(major1) + (80253431602009/5000000000000 : ℝ)*(major2) + (12884828063/100000000000000 : ℝ)*(sp1) + (1445839731/12500000000000 : ℝ)*(sp2) + (1231709148235851/50000000000000 : ℝ)*(sp4) + (615850896565141/25000000000000 : ℝ)*(sp5) + (24634048471767/1000000000000 : ℝ)*(sp6) + (373359271204133/50000000000000 : ℝ)*(sp7) + (373359271204133/50000000000000 : ℝ)*(f.failure) + (1231709148235851/50000000000000 : ℝ)*(f.sum) + (3374000856271/1751000000000000000000000000 : ℝ)*base65 + (9368470254251979/35020000000000000000000000000000 : ℝ)*base68 + (57088225452731979/35020000000000000000000000000000 : ℝ)*base70 + (65901748705491979/35020000000000000000000000000000 : ℝ)*base72 + (795384387557/175100000000000000000000000 : ℝ)*base73 + (151759923890571979/35020000000000000000000000000000 : ℝ)*base76 + (81096641782771979/35020000000000000000000000000000 : ℝ)*base78 + (185070726003851979/35020000000000000000000000000000 : ℝ)*base80 + (5524041254131/1751000000000000000000000000 : ℝ)*base81 + (5048241/1000000000000000000000 : ℝ)*base90 + (5048241/1000000000000000000000 : ℝ)*base92 + (5048241/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1751_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42989923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20773/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1353/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8997/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2253/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1751_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1751_s2_0 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-243317883/2000000000 : ℝ)*x 0 + (5495716657/10000000000 : ℝ)*x 1 + (2540689867/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (243317883/2000000000 : ℝ)^5791 ≤ (3868955081729/50000000000000 : ℝ)^4767 := by
    have hnat : (243317883 : ℕ)^5791*50000000000000^4767 ≤ 3868955081729^4767*2000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243317883 2000000000 3868955081729 50000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5495716657/10000000000 : ℝ)^5791 ≤ (48325785399131/100000000000000 : ℝ)^4767 := by
    have hnat : (5495716657 : ℕ)^5791*100000000000000^4767 ≤ 48325785399131^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5495716657 10000000000 48325785399131 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2540689867/5000000000 : ℝ)^5791 ≤ (21968152208757/50000000000000 : ℝ)^4767 := by
    have hnat : (2540689867 : ℕ)^5791*50000000000000^4767 ≤ 21968152208757^4767*5000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2540689867 5000000000 21968152208757 50000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-243317883/2000000000 : ℝ), (5495716657/10000000000 : ℝ), (2540689867/5000000000 : ℝ)] ![(3868955081729/50000000000000 : ℝ), (48325785399131/100000000000000 : ℝ), (21968152208757/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-243317883/2000000000 : ℝ)|^5791 ≤ (3868955081729/50000000000000 : ℝ)^4767
        have hw : |(-243317883/2000000000 : ℝ)|=(243317883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5495716657/10000000000 : ℝ)|^5791 ≤ (48325785399131/100000000000000 : ℝ)^4767
        have hw : |(5495716657/10000000000 : ℝ)|=(5495716657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2540689867/5000000000 : ℝ)|^5791 ≤ (21968152208757/50000000000000 : ℝ)^4767
        have hw : |(2540689867/5000000000 : ℝ)|=(2540689867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1751_s2_1 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2667798063/5000000000 : ℝ)*x 0 + (-716648299/5000000000 : ℝ)*x 1 + (508137949/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2667798063/5000000000 : ℝ)^5791 ≤ (23310365344347/50000000000000 : ℝ)^4767 := by
    have hnat : (2667798063 : ℕ)^5791*50000000000000^4767 ≤ 23310365344347^4767*5000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2667798063 5000000000 23310365344347 50000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (716648299/5000000000 : ℝ)^5791 ≤ (472148371841/5000000000000 : ℝ)^4767 := by
    have hnat : (716648299 : ℕ)^5791*5000000000000^4767 ≤ 472148371841^4767*5000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      716648299 5000000000 472148371841 5000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (508137949/1000000000 : ℝ)^5791 ≤ (10984075463641/25000000000000 : ℝ)^4767 := by
    have hnat : (508137949 : ℕ)^5791*25000000000000^4767 ≤ 10984075463641^4767*1000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508137949 1000000000 10984075463641 25000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2667798063/5000000000 : ℝ), (-716648299/5000000000 : ℝ), (508137949/1000000000 : ℝ)] ![(23310365344347/50000000000000 : ℝ), (472148371841/5000000000000 : ℝ), (10984075463641/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2667798063/5000000000 : ℝ)|^5791 ≤ (23310365344347/50000000000000 : ℝ)^4767
        have hw : |(2667798063/5000000000 : ℝ)|=(2667798063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-716648299/5000000000 : ℝ)|^5791 ≤ (472148371841/5000000000000 : ℝ)^4767
        have hw : |(-716648299/5000000000 : ℝ)|=(716648299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(508137949/1000000000 : ℝ)|^5791 ≤ (10984075463641/25000000000000 : ℝ)^4767
        have hw : |(508137949/1000000000 : ℝ)|=(508137949/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1751_s2_2 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5335595899/10000000000 : ℝ)*x 0 + (5081379747/10000000000 : ℝ)*x 1 + (-1433296563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5335595899/10000000000 : ℝ)^5791 ≤ (23310364139587/50000000000000 : ℝ)^4767 := by
    have hnat : (5335595899 : ℕ)^5791*50000000000000^4767 ≤ 23310364139587^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5335595899 10000000000 23310364139587 50000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5081379747/10000000000 : ℝ)^5791 ≤ (8787260910813/20000000000000 : ℝ)^4767 := by
    have hnat : (5081379747 : ℕ)^5791*20000000000000^4767 ≤ 8787260910813^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5081379747 10000000000 8787260910813 20000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1433296563/10000000000 : ℝ)^5791 ≤ (9442967156697/100000000000000 : ℝ)^4767 := by
    have hnat : (1433296563 : ℕ)^5791*100000000000000^4767 ≤ 9442967156697^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1433296563 10000000000 9442967156697 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5335595899/10000000000 : ℝ), (5081379747/10000000000 : ℝ), (-1433296563/10000000000 : ℝ)] ![(23310364139587/50000000000000 : ℝ), (8787260910813/20000000000000 : ℝ), (9442967156697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5335595899/10000000000 : ℝ)|^5791 ≤ (23310364139587/50000000000000 : ℝ)^4767
        have hw : |(5335595899/10000000000 : ℝ)|=(5335595899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5081379747/10000000000 : ℝ)|^5791 ≤ (8787260910813/20000000000000 : ℝ)^4767
        have hw : |(5081379747/10000000000 : ℝ)|=(5081379747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1433296563/10000000000 : ℝ)|^5791 ≤ (9442967156697/100000000000000 : ℝ)^4767
        have hw : |(-1433296563/10000000000 : ℝ)|=(1433296563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1751_s2_3 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4018780501/10000000000 : ℝ)*x 0 + (3366801473/10000000000 : ℝ)*x 1 + (295856001/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4018780501/10000000000 : ℝ)^5791 ≤ (33040736498169/100000000000000 : ℝ)^4767 := by
    have hnat : (4018780501 : ℕ)^5791*100000000000000^4767 ≤ 33040736498169^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4018780501 10000000000 33040736498169 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3366801473/10000000000 : ℝ)^5791 ≤ (26647656968871/100000000000000 : ℝ)^4767 := by
    have hnat : (3366801473 : ℕ)^5791*100000000000000^4767 ≤ 26647656968871^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3366801473 10000000000 26647656968871 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (295856001/625000000 : ℝ)^5791 ≤ (20155803254827/50000000000000 : ℝ)^4767 := by
    have hnat : (295856001 : ℕ)^5791*50000000000000^4767 ≤ 20155803254827^4767*625000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      295856001 625000000 20155803254827 50000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4018780501/10000000000 : ℝ), (3366801473/10000000000 : ℝ), (295856001/625000000 : ℝ)] ![(33040736498169/100000000000000 : ℝ), (26647656968871/100000000000000 : ℝ), (20155803254827/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4018780501/10000000000 : ℝ)|^5791 ≤ (33040736498169/100000000000000 : ℝ)^4767
        have hw : |(4018780501/10000000000 : ℝ)|=(4018780501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3366801473/10000000000 : ℝ)|^5791 ≤ (26647656968871/100000000000000 : ℝ)^4767
        have hw : |(3366801473/10000000000 : ℝ)|=(3366801473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(295856001/625000000 : ℝ)|^5791 ≤ (20155803254827/50000000000000 : ℝ)^4767
        have hw : |(295856001/625000000 : ℝ)|=(295856001/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1751_s2_4 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-608469143/5000000000 : ℝ)*x 0 + (1272032799/2500000000 : ℝ)*x 1 + (54888237/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (608469143/5000000000 : ℝ)^5791 ≤ (3870302915433/50000000000000 : ℝ)^4767 := by
    have hnat : (608469143 : ℕ)^5791*50000000000000^4767 ≤ 3870302915433^4767*5000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      608469143 5000000000 3870302915433 50000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1272032799/2500000000 : ℝ)^5791 ≤ (44007231168213/100000000000000 : ℝ)^4767 := by
    have hnat : (1272032799 : ℕ)^5791*100000000000000^4767 ≤ 44007231168213^4767*2500000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1272032799 2500000000 44007231168213 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54888237/100000000 : ℝ)^5791 ≤ (48252162987101/100000000000000 : ℝ)^4767 := by
    have hnat : (54888237 : ℕ)^5791*100000000000000^4767 ≤ 48252162987101^4767*100000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54888237 100000000 48252162987101 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-608469143/5000000000 : ℝ), (1272032799/2500000000 : ℝ), (54888237/100000000 : ℝ)] ![(3870302915433/50000000000000 : ℝ), (44007231168213/100000000000000 : ℝ), (48252162987101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-608469143/5000000000 : ℝ)|^5791 ≤ (3870302915433/50000000000000 : ℝ)^4767
        have hw : |(-608469143/5000000000 : ℝ)|=(608469143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1272032799/2500000000 : ℝ)|^5791 ≤ (44007231168213/100000000000000 : ℝ)^4767
        have hw : |(1272032799/2500000000 : ℝ)|=(1272032799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(54888237/100000000 : ℝ)|^5791 ≤ (48252162987101/100000000000000 : ℝ)^4767
        have hw : |(54888237/100000000 : ℝ)|=(54888237/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1751_s2_5 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5225789043/10000000000 : ℝ)*x 0 + (-256463153/2500000000 : ℝ)*x 1 + (5488823643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5225789043/10000000000 : ℝ)^5791 ≤ (45457760359539/100000000000000 : ℝ)^4767 := by
    have hnat : (5225789043 : ℕ)^5791*100000000000000^4767 ≤ 45457760359539^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225789043 10000000000 45457760359539 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (256463153/2500000000 : ℝ)^5791 ≤ (6290077251237/100000000000000 : ℝ)^4767 := by
    have hnat : (256463153 : ℕ)^5791*100000000000000^4767 ≤ 6290077251237^4767*2500000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256463153 2500000000 6290077251237 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5488823643/10000000000 : ℝ)^5791 ≤ (48252162378377/100000000000000 : ℝ)^4767 := by
    have hnat : (5488823643 : ℕ)^5791*100000000000000^4767 ≤ 48252162378377^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5488823643 10000000000 48252162378377 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5225789043/10000000000 : ℝ), (-256463153/2500000000 : ℝ), (5488823643/10000000000 : ℝ)] ![(45457760359539/100000000000000 : ℝ), (6290077251237/100000000000000 : ℝ), (48252162378377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5225789043/10000000000 : ℝ)|^5791 ≤ (45457760359539/100000000000000 : ℝ)^4767
        have hw : |(5225789043/10000000000 : ℝ)|=(5225789043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-256463153/2500000000 : ℝ)|^5791 ≤ (6290077251237/100000000000000 : ℝ)^4767
        have hw : |(-256463153/2500000000 : ℝ)|=(256463153/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5488823643/10000000000 : ℝ)|^5791 ≤ (48252162378377/100000000000000 : ℝ)^4767
        have hw : |(5488823643/10000000000 : ℝ)|=(5488823643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1751_s2_6 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2612894481/5000000000 : ℝ)*x 0 + (2744411841/5000000000 : ℝ)*x 1 + (-1025852671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2612894481/5000000000 : ℝ)^5791 ≤ (22728879751793/50000000000000 : ℝ)^4767 := by
    have hnat : (2612894481 : ℕ)^5791*50000000000000^4767 ≤ 22728879751793^4767*5000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612894481 5000000000 22728879751793 50000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2744411841/5000000000 : ℝ)^5791 ≤ (48252162794873/100000000000000 : ℝ)^4767 := by
    have hnat : (2744411841 : ℕ)^5791*100000000000000^4767 ≤ 48252162794873^4767*5000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2744411841 5000000000 48252162794873 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1025852671/10000000000 : ℝ)^5791 ≤ (6290077690709/100000000000000 : ℝ)^4767 := by
    have hnat : (1025852671 : ℕ)^5791*100000000000000^4767 ≤ 6290077690709^4767*10000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025852671 10000000000 6290077690709 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2612894481/5000000000 : ℝ), (2744411841/5000000000 : ℝ), (-1025852671/10000000000 : ℝ)] ![(22728879751793/50000000000000 : ℝ), (48252162794873/100000000000000 : ℝ), (6290077690709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2612894481/5000000000 : ℝ)|^5791 ≤ (22728879751793/50000000000000 : ℝ)^4767
        have hw : |(2612894481/5000000000 : ℝ)|=(2612894481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2744411841/5000000000 : ℝ)|^5791 ≤ (48252162794873/100000000000000 : ℝ)^4767
        have hw : |(2744411841/5000000000 : ℝ)|=(2744411841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1025852671/10000000000 : ℝ)|^5791 ≤ (6290077690709/100000000000000 : ℝ)^4767
        have hw : |(-1025852671/10000000000 : ℝ)|=(1025852671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1751_s2_7 (p : ℝ) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (803986321/2000000000 : ℝ)*x 0 + (2355711543/5000000000 : ℝ)*x 1 + (105923171/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (803986321/2000000000 : ℝ)^5791 ≤ (33052233689761/100000000000000 : ℝ)^4767 := by
    have hnat : (803986321 : ℕ)^5791*100000000000000^4767 ≤ 33052233689761^4767*2000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      803986321 2000000000 33052233689761 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2355711543/5000000000 : ℝ)^5791 ≤ (8016261114639/20000000000000 : ℝ)^4767 := by
    have hnat : (2355711543 : ℕ)^5791*20000000000000^4767 ≤ 8016261114639^4767*5000000000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2355711543 5000000000 8016261114639 20000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105923171/312500000 : ℝ)^5791 ≤ (26866460717207/100000000000000 : ℝ)^4767 := by
    have hnat : (105923171 : ℕ)^5791*100000000000000^4767 ≤ 26866460717207^4767*312500000^5791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105923171 312500000 26866460717207 100000000000000 5791 4767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5791/1024 : ℝ)) 5791 4767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(803986321/2000000000 : ℝ), (2355711543/5000000000 : ℝ), (105923171/312500000 : ℝ)] ![(33052233689761/100000000000000 : ℝ), (8016261114639/20000000000000 : ℝ), (26866460717207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(803986321/2000000000 : ℝ)|^5791 ≤ (33052233689761/100000000000000 : ℝ)^4767
        have hw : |(803986321/2000000000 : ℝ)|=(803986321/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2355711543/5000000000 : ℝ)|^5791 ≤ (8016261114639/20000000000000 : ℝ)^4767
        have hw : |(2355711543/5000000000 : ℝ)|=(2355711543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105923171/312500000 : ℝ)|^5791 ≤ (26866460717207/100000000000000 : ℝ)^4767
        have hw : |(105923171/312500000 : ℝ)|=(105923171/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1751_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42989923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2253/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8997/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2263/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17957/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2253/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8997/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2253/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8997/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2253/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8997/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2253/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8997/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2253/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8997/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2253/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8997/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8997/100000 : ℝ) ^ (5775/1024 : ℝ) ≤ (63160978254321/50000000000000000000 : ℝ) := by
    have hpowers : (8997/100000 : ℝ)^5775 ≤ (63160978254321/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8997 : ℕ)^5775*50000000000000000000^1024 ≤ 63160978254321^1024*100000^5775 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8997 100000 63160978254321 50000000000000000000 5775 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8997/100000 : ℝ)) (X := (63160978254321/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5775 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2253/12500 : ℝ) ^ (5775/1024 : ℝ) ≤ (1589286782155737/25000000000000000000 : ℝ) := by
    have hpowers : (2253/12500 : ℝ)^5775 ≤ (1589286782155737/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2253 : ℕ)^5775*25000000000000000000^1024 ≤ 1589286782155737^1024*12500^5775 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2253 12500 1589286782155737 25000000000000000000 5775 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2253/12500 : ℝ)) (X := (1589286782155737/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5775 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000063160978254321/25000000000000000000 : ℝ) ≤ (10000004479776591/10000000000000000 : ℝ) ^ (5775/1024 : ℝ) := by
    have hpowers : (25000063160978254321/25000000000000000000 : ℝ)^1024 ≤ (10000004479776591/10000000000000000 : ℝ)^5775 := by
      have hnat : (25000063160978254321 : ℕ)^1024*10000000000000000^5775 ≤ 10000004479776591^5775*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000063160978254321 25000000000000000000 10000004479776591 10000000000000000 1024 5775 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000004479776591/10000000000000000 : ℝ)) (X := (25000063160978254321/25000000000000000000 : ℝ)) (by norm_num) 5775 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10000648346908513159/10000000000000000000 : ℝ) ≤ (5000057479612911/5000000000000000 : ℝ) ^ (5775/1024 : ℝ) := by
    have hpowers : (10000648346908513159/10000000000000000000 : ℝ)^1024 ≤ (5000057479612911/5000000000000000 : ℝ)^5775 := by
      have hnat : (10000648346908513159 : ℕ)^1024*5000000000000000^5775 ≤ 5000057479612911^5775*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000648346908513159 10000000000000000000 5000057479612911 5000000000000000 1024 5775 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000057479612911/5000000000000000 : ℝ)) (X := (10000648346908513159/10000000000000000000 : ℝ)) (by norm_num) 5775 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12501589286782155737/12500000000000000000 : ℝ) ≤ (10000225438675053/10000000000000000 : ℝ) ^ (5775/1024 : ℝ) := by
    have hpowers : (12501589286782155737/12500000000000000000 : ℝ)^1024 ≤ (10000225438675053/10000000000000000 : ℝ)^5775 := by
      have hnat : (12501589286782155737 : ℕ)^1024*10000000000000000^5775 ≤ 10000225438675053^5775*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501589286782155737 12500000000000000000 10000225438675053 10000000000000000 1024 5775 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000225438675053/10000000000000000 : ℝ)) (X := (12501589286782155737/12500000000000000000 : ℝ)) (by norm_num) 5775 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(63160978254321/50000000000000000000 : ℝ) ≤ ((10029783607970424927/10030000000000000000 : ℝ)+2*(12275494359/100300000000000 : ℝ)*(8997/100000 : ℝ))^(5775/1024 : ℝ) := by
    rw [show (10029783607970424927/10030000000000000000 : ℝ)+2*(12275494359/100300000000000 : ℝ)*(8997/100000 : ℝ)=(10000004479776591/10000000000000000 : ℝ) by norm_num, show 1+2*(63160978254321/50000000000000000000 : ℝ)=(25000063160978254321/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1589286782155737/25000000000000000000 : ℝ)+(63160978254321/50000000000000000000 : ℝ) ≤ ((10029783607970424927/10030000000000000000 : ℝ)+(12275494359/100300000000000 : ℝ)*((2253/12500 : ℝ)+(8997/100000 : ℝ)))^(5775/1024 : ℝ) := by
    rw [show (10029783607970424927/10030000000000000000 : ℝ)+(12275494359/100300000000000 : ℝ)*((2253/12500 : ℝ)+(8997/100000 : ℝ))=(5000057479612911/5000000000000000 : ℝ) by norm_num, show 1+(1589286782155737/25000000000000000000 : ℝ)+(63160978254321/50000000000000000000 : ℝ)=(10000648346908513159/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1589286782155737/25000000000000000000 : ℝ) ≤ ((10029783607970424927/10030000000000000000 : ℝ)+2*(12275494359/100300000000000 : ℝ)*(2253/12500 : ℝ))^(5775/1024 : ℝ) := by
    rw [show (10029783607970424927/10030000000000000000 : ℝ)+2*(12275494359/100300000000000 : ℝ)*(2253/12500 : ℝ)=(10000225438675053/10000000000000000 : ℝ) by norm_num, show 1+2*(1589286782155737/25000000000000000000 : ℝ)=(12501589286782155737/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10029783607970424927/10030000000000000000 : ℝ)*(X 1 0+X 2 0)+(12275494359/100300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5775/1024 : ℝ)) (lo := (8997/100000 : ℝ)) (hi := (2253/12500 : ℝ)) (c := (10029783607970424927/10030000000000000000 : ℝ)) (alpha := (12275494359/100300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10029783607970424927/10030000000000000000 : ℝ)*(X 0 1+X 2 1)+(12275494359/100300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5775/1024 : ℝ)) (lo := (8997/100000 : ℝ)) (hi := (2253/12500 : ℝ)) (c := (10029783607970424927/10030000000000000000 : ℝ)) (alpha := (12275494359/100300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10029783607970424927/10030000000000000000 : ℝ)*(X 0 2+X 1 2)+(12275494359/100300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5775/1024 : ℝ)) (lo := (8997/100000 : ℝ)) (hi := (2253/12500 : ℝ)) (c := (10029783607970424927/10030000000000000000 : ℝ)) (alpha := (12275494359/100300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-243317883/2000000000 : ℝ)*X 0 0+(5495716657/10000000000 : ℝ)*X 0 1+(2540689867/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2667798063/5000000000 : ℝ)*X 1 0+(-716648299/5000000000 : ℝ)*X 1 1+(508137949/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5335595899/10000000000 : ℝ)*X 2 0+(5081379747/10000000000 : ℝ)*X 2 1+(-1433296563/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4018780501/10000000000 : ℝ)*X 0 0+(3366801473/10000000000 : ℝ)*X 0 1+(295856001/625000000 : ℝ)*X 0 2+(4018780501/10000000000 : ℝ)*X 1 0+(3366801473/10000000000 : ℝ)*X 1 1+(295856001/625000000 : ℝ)*X 1 2+(4018780501/10000000000 : ℝ)*X 2 0+(3366801473/10000000000 : ℝ)*X 2 1+(295856001/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-608469143/5000000000 : ℝ)*X 0 0+(1272032799/2500000000 : ℝ)*X 0 1+(54888237/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5225789043/10000000000 : ℝ)*X 1 0+(-256463153/2500000000 : ℝ)*X 1 1+(5488823643/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2612894481/5000000000 : ℝ)*X 2 0+(2744411841/5000000000 : ℝ)*X 2 1+(-1025852671/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((803986321/2000000000 : ℝ)*X 0 0+(2355711543/5000000000 : ℝ)*X 0 1+(105923171/312500000 : ℝ)*X 0 2+(803986321/2000000000 : ℝ)*X 1 0+(2355711543/5000000000 : ℝ)*X 1 1+(105923171/312500000 : ℝ)*X 1 2+(803986321/2000000000 : ℝ)*X 2 0+(2355711543/5000000000 : ℝ)*X 2 1+(105923171/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1751_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2301107955569930064807265863/250750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (693785469/50000000000000 : ℝ)*(base19) + (611147439/50000000000000 : ℝ)*(base23) + (4174733/12500000000000 : ℝ)*(lower2) + (52751119/25000000000000 : ℝ)*(upper3) + (8628773/5000000000000 : ℝ)*(upper5) + (786276797634641/50000000000000 : ℝ)*(major0) + (786276797634641/50000000000000 : ℝ)*(major1) + (786276797634641/50000000000000 : ℝ)*(major2) + (603376258393809/25000000000000 : ℝ)*(sp0) + (1206756886265761/50000000000000 : ℝ)*(sp1) + (1206756968903791/50000000000000 : ℝ)*(sp2) + (182897097312147/25000000000000 : ℝ)*(sp3) + (10126527223/100000000000000 : ℝ)*(sp4) + (833822701/25000000000000 : ℝ)*(sp7) + (731591724539391/100000000000000 : ℝ)*(f.failure) + (2413515160102459/100000000000000 : ℝ)*(f.sum) + (780335119191/156718750000000000000000000 : ℝ)*base66 + (938972476765003793/501500000000000000000000000000000 : ℝ)*base68 + (281593835553003793/501500000000000000000000000000000 : ℝ)*base70 + (4194309653893003793/501500000000000000000000000000000 : ℝ)*base72 + (422363391779/2507500000000000000000000000 : ℝ)*base73 + (3890905110737003793/501500000000000000000000000000000 : ℝ)*base76 + (4983782210562003793/501500000000000000000000000000000 : ℝ)*base78 + (3707446554256003793/501500000000000000000000000000000 : ℝ)*base80 + (4033615801697/1253750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (10443107/2000000000000000000000 : ℝ)*base90 + (10443107/2000000000000000000000 : ℝ)*base92 + (10443107/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (42282424605485157393355029/3917968750000000000000000000000 : ℝ) := by norm_num
    linear_combination (68153619/5000000000000 : ℝ)*(base19) + (1438487041/100000000000000 : ℝ)*(base23) + (380027757/100000000000000 : ℝ)*(lower1) + (8826117/4000000000000 : ℝ)*(upper3) + (10702043/20000000000000 : ℝ)*(lower4) + (204273973/100000000000000 : ℝ)*(upper5) + (50815057696607/3125000000000 : ℝ)*(major0) + (50815057696607/3125000000000 : ℝ)*(major1) + (50815057696607/3125000000000 : ℝ)*(major2) + (278433859/50000000000000 : ℝ)*(sp2) + (1247834455727007/50000000000000 : ℝ)*(sp4) + (499133509676327/20000000000000 : ℝ)*(sp5) + (1247833458049627/50000000000000 : ℝ)*(sp6) + (378247210698987/50000000000000 : ℝ)*(sp7) + (378247210698987/50000000000000 : ℝ)*(f.failure) + (1247834455727007/50000000000000 : ℝ)*(f.sum) + (9685715961613/2507500000000000000000000000 : ℝ)*base65 + (225267790704797689/31343750000000000000000000000000 : ℝ)*base67 + (329850568734172689/31343750000000000000000000000000 : ℝ)*base69 + (2660671790613983561/31343750000000000000000000000000 : ℝ)*base72 + (2384406456257/626875000000000000000000000 : ℝ)*base73 + (1863448084405578939/31343750000000000000000000000000 : ℝ)*base75 + (363044177586797689/31343750000000000000000000000000 : ℝ)*base77 + (661942025408235189/31343750000000000000000000000000 : ℝ)*base79 + (7579632755329/1253750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (12691999/1000000000000000000000 : ℝ)*base90 + (12691999/1000000000000000000000 : ℝ)*base92 + (12691999/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1751_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42989923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2253/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8997/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2263/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17957/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1751_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1751_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42989923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2263/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17957/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1751_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1751_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1751_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5775/1024 : ℝ) ≤ p) (hpb : p ≤ (5791/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42989923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2263/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17957/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1751_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

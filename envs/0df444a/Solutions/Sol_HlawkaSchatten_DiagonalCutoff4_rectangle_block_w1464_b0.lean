-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1464_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:08:40.60602+00:00
-- url     : https://prove2.me/submissions/b339c699-b84c-4bbb-ab76-42b9ad72e5e6

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
theorem support_rectangle_w1464_s0_0 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1737950677/10000000000 : ℝ)*x 0 + (1190151119/2000000000 : ℝ)*x 1 + (2417126627/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1737950677/10000000000 : ℝ)^4425 ≤ (10261761251789/100000000000000 : ℝ)^3401 := by
    have hnat : (1737950677 : ℕ)^4425*100000000000000^3401 ≤ 10261761251789^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1737950677 10000000000 10261761251789 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1190151119/2000000000 : ℝ)^4425 ≤ (12724435068909/25000000000000 : ℝ)^3401 := by
    have hnat : (1190151119 : ℕ)^4425*25000000000000^3401 ≤ 12724435068909^3401*2000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1190151119 2000000000 12724435068909 25000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2417126627/5000000000 : ℝ)^4425 ≤ (38840498461831/100000000000000 : ℝ)^3401 := by
    have hnat : (2417126627 : ℕ)^4425*100000000000000^3401 ≤ 38840498461831^3401*5000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2417126627 5000000000 38840498461831 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1737950677/10000000000 : ℝ), (1190151119/2000000000 : ℝ), (2417126627/5000000000 : ℝ)] ![(10261761251789/100000000000000 : ℝ), (12724435068909/25000000000000 : ℝ), (38840498461831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1737950677/10000000000 : ℝ)|^4425 ≤ (10261761251789/100000000000000 : ℝ)^3401
        have hw : |(-1737950677/10000000000 : ℝ)|=(1737950677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1190151119/2000000000 : ℝ)|^4425 ≤ (12724435068909/25000000000000 : ℝ)^3401
        have hw : |(1190151119/2000000000 : ℝ)|=(1190151119/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2417126627/5000000000 : ℝ)|^4425 ≤ (38840498461831/100000000000000 : ℝ)^3401
        have hw : |(2417126627/5000000000 : ℝ)|=(2417126627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1464_s0_1 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5488495363/10000000000 : ℝ)*x 0 + (-1183879989/5000000000 : ℝ)*x 1 + (2417126631/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5488495363/10000000000 : ℝ)^4425 ≤ (5726850584599/12500000000000 : ℝ)^3401 := by
    have hnat : (5488495363 : ℕ)^4425*12500000000000^3401 ≤ 5726850584599^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5488495363 10000000000 5726850584599 12500000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1183879989/5000000000 : ℝ)^4425 ≤ (15344696762891/100000000000000 : ℝ)^3401 := by
    have hnat : (1183879989 : ℕ)^4425*100000000000000^3401 ≤ 15344696762891^3401*5000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1183879989 5000000000 15344696762891 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2417126631/5000000000 : ℝ)^4425 ≤ (38840498545459/100000000000000 : ℝ)^3401 := by
    have hnat : (2417126631 : ℕ)^4425*100000000000000^3401 ≤ 38840498545459^3401*5000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2417126631 5000000000 38840498545459 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5488495363/10000000000 : ℝ), (-1183879989/5000000000 : ℝ), (2417126631/5000000000 : ℝ)] ![(5726850584599/12500000000000 : ℝ), (15344696762891/100000000000000 : ℝ), (38840498545459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5488495363/10000000000 : ℝ)|^4425 ≤ (5726850584599/12500000000000 : ℝ)^3401
        have hw : |(5488495363/10000000000 : ℝ)|=(5488495363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1183879989/5000000000 : ℝ)|^4425 ≤ (15344696762891/100000000000000 : ℝ)^3401
        have hw : |(-1183879989/5000000000 : ℝ)|=(1183879989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2417126631/5000000000 : ℝ)|^4425 ≤ (38840498545459/100000000000000 : ℝ)^3401
        have hw : |(2417126631/5000000000 : ℝ)|=(2417126631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1464_s0_2 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2744247673/5000000000 : ℝ)*x 0 + (604281659/1250000000 : ℝ)*x 1 + (-591939997/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2744247673/5000000000 : ℝ)^4425 ≤ (71585632019/156250000000 : ℝ)^3401 := by
    have hnat : (2744247673 : ℕ)^4425*156250000000^3401 ≤ 71585632019^3401*5000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2744247673 5000000000 71585632019 156250000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (604281659/1250000000 : ℝ)^4425 ≤ (19420249324997/50000000000000 : ℝ)^3401 := by
    have hnat : (604281659 : ℕ)^4425*50000000000000^3401 ≤ 19420249324997^3401*1250000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      604281659 1250000000 19420249324997 50000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (591939997/2500000000 : ℝ)^4425 ≤ (1534469684721/10000000000000 : ℝ)^3401 := by
    have hnat : (591939997 : ℕ)^4425*10000000000000^3401 ≤ 1534469684721^3401*2500000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      591939997 2500000000 1534469684721 10000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2744247673/5000000000 : ℝ), (604281659/1250000000 : ℝ), (-591939997/2500000000 : ℝ)] ![(71585632019/156250000000 : ℝ), (19420249324997/50000000000000 : ℝ), (1534469684721/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2744247673/5000000000 : ℝ)|^4425 ≤ (71585632019/156250000000 : ℝ)^3401
        have hw : |(2744247673/5000000000 : ℝ)|=(2744247673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(604281659/1250000000 : ℝ)|^4425 ≤ (19420249324997/50000000000000 : ℝ)^3401
        have hw : |(604281659/1250000000 : ℝ)|=(604281659/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-591939997/2500000000 : ℝ)|^4425 ≤ (1534469684721/10000000000000 : ℝ)^3401
        have hw : |(-591939997/2500000000 : ℝ)|=(591939997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1464_s0_3 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (259896859/625000000 : ℝ)*x 0 + (772988647/2500000000 : ℝ)*x 1 + (55383277/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (259896859/625000000 : ℝ)^4425 ≤ (3192881024783/10000000000000 : ℝ)^3401 := by
    have hnat : (259896859 : ℕ)^4425*10000000000000^3401 ≤ 3192881024783^3401*625000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259896859 625000000 3192881024783 10000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (772988647/2500000000 : ℝ)^4425 ≤ (34743089749/160000000000 : ℝ)^3401 := by
    have hnat : (772988647 : ℕ)^4425*160000000000^3401 ≤ 34743089749^3401*2500000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      772988647 2500000000 34743089749 160000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (55383277/100000000 : ℝ)^4425 ≤ (23178379320449/50000000000000 : ℝ)^3401 := by
    have hnat : (55383277 : ℕ)^4425*50000000000000^3401 ≤ 23178379320449^3401*100000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55383277 100000000 23178379320449 50000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(259896859/625000000 : ℝ), (772988647/2500000000 : ℝ), (55383277/100000000 : ℝ)] ![(3192881024783/10000000000000 : ℝ), (34743089749/160000000000 : ℝ), (23178379320449/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(259896859/625000000 : ℝ)|^4425 ≤ (3192881024783/10000000000000 : ℝ)^3401
        have hw : |(259896859/625000000 : ℝ)|=(259896859/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(772988647/2500000000 : ℝ)|^4425 ≤ (34743089749/160000000000 : ℝ)^3401
        have hw : |(772988647/2500000000 : ℝ)|=(772988647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(55383277/100000000 : ℝ)|^4425 ≤ (23178379320449/50000000000000 : ℝ)^3401
        have hw : |(55383277/100000000 : ℝ)|=(55383277/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1464_s0_4 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1741902881/10000000000 : ℝ)*x 0 + (4862971493/10000000000 : ℝ)*x 1 + (148025081/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1741902881/10000000000 : ℝ)^4425 ≤ (10292133646173/100000000000000 : ℝ)^3401 := by
    have hnat : (1741902881 : ℕ)^4425*100000000000000^3401 ≤ 10292133646173^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1741902881 10000000000 10292133646173 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4862971493/10000000000 : ℝ)^4425 ≤ (4892621612609/12500000000000 : ℝ)^3401 := by
    have hnat : (4862971493 : ℕ)^4425*12500000000000^3401 ≤ 4892621612609^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4862971493 10000000000 4892621612609 12500000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (148025081/250000000 : ℝ)^4425 ≤ (50566893438879/100000000000000 : ℝ)^3401 := by
    have hnat : (148025081 : ℕ)^4425*100000000000000^3401 ≤ 50566893438879^3401*250000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      148025081 250000000 50566893438879 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1741902881/10000000000 : ℝ), (4862971493/10000000000 : ℝ), (148025081/250000000 : ℝ)] ![(10292133646173/100000000000000 : ℝ), (4892621612609/12500000000000 : ℝ), (50566893438879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1741902881/10000000000 : ℝ)|^4425 ≤ (10292133646173/100000000000000 : ℝ)^3401
        have hw : |(-1741902881/10000000000 : ℝ)|=(1741902881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4862971493/10000000000 : ℝ)|^4425 ≤ (4892621612609/12500000000000 : ℝ)^3401
        have hw : |(4862971493/10000000000 : ℝ)|=(4862971493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(148025081/250000000 : ℝ)|^4425 ≤ (50566893438879/100000000000000 : ℝ)^3401
        have hw : |(148025081/250000000 : ℝ)|=(148025081/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1464_s0_5 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1036751043/2000000000 : ℝ)*x 0 + (-128100983/1000000000 : ℝ)*x 1 + (1184200661/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1036751043/2000000000 : ℝ)^4425 ≤ (8506626876453/20000000000000 : ℝ)^3401 := by
    have hnat : (1036751043 : ℕ)^4425*20000000000000^3401 ≤ 8506626876453^3401*2000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036751043 2000000000 8506626876453 20000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (128100983/1000000000 : ℝ)^4425 ≤ (6899971449641/100000000000000 : ℝ)^3401 := by
    have hnat : (128100983 : ℕ)^4425*100000000000000^3401 ≤ 6899971449641^3401*1000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128100983 1000000000 6899971449641 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1184200661/2000000000 : ℝ)^4425 ≤ (25283447080567/50000000000000 : ℝ)^3401 := by
    have hnat : (1184200661 : ℕ)^4425*50000000000000^3401 ≤ 25283447080567^3401*2000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1184200661 2000000000 25283447080567 50000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1036751043/2000000000 : ℝ), (-128100983/1000000000 : ℝ), (1184200661/2000000000 : ℝ)] ![(8506626876453/20000000000000 : ℝ), (6899971449641/100000000000000 : ℝ), (25283447080567/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1036751043/2000000000 : ℝ)|^4425 ≤ (8506626876453/20000000000000 : ℝ)^3401
        have hw : |(1036751043/2000000000 : ℝ)|=(1036751043/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-128100983/1000000000 : ℝ)|^4425 ≤ (6899971449641/100000000000000 : ℝ)^3401
        have hw : |(-128100983/1000000000 : ℝ)|=(128100983/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1184200661/2000000000 : ℝ)|^4425 ≤ (25283447080567/50000000000000 : ℝ)^3401
        have hw : |(1184200661/2000000000 : ℝ)|=(1184200661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1464_s0_6 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5183755249/10000000000 : ℝ)*x 0 + (370062697/625000000 : ℝ)*x 1 + (-64050501/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5183755249/10000000000 : ℝ)^4425 ≤ (42533134745233/100000000000000 : ℝ)^3401 := by
    have hnat : (5183755249 : ℕ)^4425*100000000000000^3401 ≤ 42533134745233^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183755249 10000000000 42533134745233 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (370062697/625000000 : ℝ)^4425 ≤ (10113378492211/20000000000000 : ℝ)^3401 := by
    have hnat : (370062697 : ℕ)^4425*20000000000000^3401 ≤ 10113378492211^3401*625000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      370062697 625000000 10113378492211 20000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (64050501/500000000 : ℝ)^4425 ≤ (53906037353/781250000000 : ℝ)^3401 := by
    have hnat : (64050501 : ℕ)^4425*781250000000^3401 ≤ 53906037353^3401*500000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64050501 500000000 53906037353 781250000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5183755249/10000000000 : ℝ), (370062697/625000000 : ℝ), (-64050501/500000000 : ℝ)] ![(42533134745233/100000000000000 : ℝ), (10113378492211/20000000000000 : ℝ), (53906037353/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5183755249/10000000000 : ℝ)|^4425 ≤ (42533134745233/100000000000000 : ℝ)^3401
        have hw : |(5183755249/10000000000 : ℝ)|=(5183755249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(370062697/625000000 : ℝ)|^4425 ≤ (10113378492211/20000000000000 : ℝ)^3401
        have hw : |(370062697/625000000 : ℝ)|=(370062697/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-64050501/500000000 : ℝ)|^4425 ≤ (53906037353/781250000000 : ℝ)^3401
        have hw : |(-64050501/500000000 : ℝ)|=(64050501/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1464_s0_7 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (833401993/2000000000 : ℝ)*x 0 + (5475402923/10000000000 : ℝ)*x 1 + (394643147/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (833401993/2000000000 : ℝ)^4425 ≤ (1600767677029/5000000000000 : ℝ)^3401 := by
    have hnat : (833401993 : ℕ)^4425*5000000000000^3401 ≤ 1600767677029^3401*2000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833401993 2000000000 1600767677029 5000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5475402923/10000000000 : ℝ)^4425 ≤ (4567266225921/10000000000000 : ℝ)^3401 := by
    have hnat : (5475402923 : ℕ)^4425*10000000000000^3401 ≤ 4567266225921^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5475402923 10000000000 4567266225921 10000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (394643147/1250000000 : ℝ)^4425 ≤ (22311984179609/100000000000000 : ℝ)^3401 := by
    have hnat : (394643147 : ℕ)^4425*100000000000000^3401 ≤ 22311984179609^3401*1250000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394643147 1250000000 22311984179609 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(833401993/2000000000 : ℝ), (5475402923/10000000000 : ℝ), (394643147/1250000000 : ℝ)] ![(1600767677029/5000000000000 : ℝ), (4567266225921/10000000000000 : ℝ), (22311984179609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(833401993/2000000000 : ℝ)|^4425 ≤ (1600767677029/5000000000000 : ℝ)^3401
        have hw : |(833401993/2000000000 : ℝ)|=(833401993/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5475402923/10000000000 : ℝ)|^4425 ≤ (4567266225921/10000000000000 : ℝ)^3401
        have hw : |(5475402923/10000000000 : ℝ)|=(5475402923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(394643147/1250000000 : ℝ)|^4425 ≤ (22311984179609/100000000000000 : ℝ)^3401
        have hw : |(394643147/1250000000 : ℝ)|=(394643147/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1464_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9972201/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (547/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (653/2500 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4423/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4423 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4423*1^1024 ≤ 0^1024*1^4423 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4423 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4423 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4423/1024 : ℝ) ≤ (1910572047652848581/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4423 ≤ (1910572047652848581/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4423*100000000000000000000^1024 ≤ 1910572047652848581^1024*5^4423 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1910572047652848581 100000000000000000000 4423 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1910572047652848581/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4423 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4423/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4423 := by
      have hnat : (1 : ℕ)^1024*1^4423 ≤ 1^4423*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4423 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101910572047652848581/100000000000000000000 : ℝ) ≤ (5021955945022103/5000000000000000 : ℝ) ^ (4423/1024 : ℝ) := by
    have hpowers : (101910572047652848581/100000000000000000000 : ℝ)^1024 ≤ (5021955945022103/5000000000000000 : ℝ)^4423 := by
      have hnat : (101910572047652848581 : ℕ)^1024*5000000000000000^4423 ≤ 5021955945022103^4423*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101910572047652848581 100000000000000000000 5021955945022103 5000000000000000 1024 4423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5021955945022103/5000000000000000 : ℝ)) (X := (101910572047652848581/100000000000000000000 : ℝ)) (by norm_num) 4423 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51910572047652848581/50000000000000000000 : ℝ) ≤ (2521955945022103/2500000000000000 : ℝ) ^ (4423/1024 : ℝ) := by
    have hpowers : (51910572047652848581/50000000000000000000 : ℝ)^1024 ≤ (2521955945022103/2500000000000000 : ℝ)^4423 := by
      have hnat : (51910572047652848581 : ℕ)^1024*2500000000000000^4423 ≤ 2521955945022103^4423*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51910572047652848581 50000000000000000000 2521955945022103 2500000000000000 1024 4423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2521955945022103/2500000000000000 : ℝ)) (X := (51910572047652848581/50000000000000000000 : ℝ)) (by norm_num) 4423 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(21955945022103/2000000000000000 : ℝ)*(0 : ℝ))^(4423/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(21955945022103/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1910572047652848581/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(21955945022103/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4423/1024 : ℝ) := by
    rw [show (1 : ℝ)+(21955945022103/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5021955945022103/5000000000000000 : ℝ) by norm_num, show 1+(1910572047652848581/100000000000000000000 : ℝ)+(0 : ℝ)=(101910572047652848581/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1910572047652848581/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(21955945022103/2000000000000000 : ℝ)*(2/5 : ℝ))^(4423/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(21955945022103/2000000000000000 : ℝ)*(2/5 : ℝ)=(2521955945022103/2500000000000000 : ℝ) by norm_num, show 1+2*(1910572047652848581/100000000000000000000 : ℝ)=(51910572047652848581/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(21955945022103/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4423/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (21955945022103/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(21955945022103/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4423/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (21955945022103/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(21955945022103/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4423/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (21955945022103/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1737950677/10000000000 : ℝ)*X 0 0+(1190151119/2000000000 : ℝ)*X 0 1+(2417126627/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5488495363/10000000000 : ℝ)*X 1 0+(-1183879989/5000000000 : ℝ)*X 1 1+(2417126631/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2744247673/5000000000 : ℝ)*X 2 0+(604281659/1250000000 : ℝ)*X 2 1+(-591939997/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((259896859/625000000 : ℝ)*X 0 0+(772988647/2500000000 : ℝ)*X 0 1+(55383277/100000000 : ℝ)*X 0 2+(259896859/625000000 : ℝ)*X 1 0+(772988647/2500000000 : ℝ)*X 1 1+(55383277/100000000 : ℝ)*X 1 2+(259896859/625000000 : ℝ)*X 2 0+(772988647/2500000000 : ℝ)*X 2 1+(55383277/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1741902881/10000000000 : ℝ)*X 0 0+(4862971493/10000000000 : ℝ)*X 0 1+(148025081/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1036751043/2000000000 : ℝ)*X 1 0+(-128100983/1000000000 : ℝ)*X 1 1+(1184200661/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5183755249/10000000000 : ℝ)*X 2 0+(370062697/625000000 : ℝ)*X 2 1+(-64050501/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((833401993/2000000000 : ℝ)*X 0 0+(5475402923/10000000000 : ℝ)*X 0 1+(394643147/1250000000 : ℝ)*X 0 2+(833401993/2000000000 : ℝ)*X 1 0+(5475402923/10000000000 : ℝ)*X 1 1+(394643147/1250000000 : ℝ)*X 1 2+(833401993/2000000000 : ℝ)*X 2 0+(5475402923/10000000000 : ℝ)*X 2 1+(394643147/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (584797199362358433/250000000000000000000000 : ℝ) := by norm_num
    linear_combination (3944039/20000000000000 : ℝ)*(base1) + (4136629/781250000000 : ℝ)*(base19) + (263357157/50000000000000 : ℝ)*(base23) + (542603/800000000000 : ℝ)*(upper3) + (12868427/20000000000000 : ℝ)*(upper5) + (65221392216253/10000000000000 : ℝ)*(major0) + (65221392216253/10000000000000 : ℝ)*(major1) + (65221392216253/10000000000000 : ℝ)*(major2) + (13994623957171/1562500000000 : ℝ)*(sp0) + (1791314391349/200000000000 : ℝ)*(sp1) + (447828599224349/50000000000000 : ℝ)*(sp2) + (102192295024571/25000000000000 : ℝ)*(sp3) + (905812131/50000000000000 : ℝ)*(sp4) + (210342651/25000000000000 : ℝ)*(sp7) + (408770041189083/100000000000000 : ℝ)*(f.failure) + (223914431290753/25000000000000 : ℝ)*(f.sum) + (37432801619941/10000000000000000000000000000 : ℝ)*base66 + (33455094240059/20000000000000000000000000000 : ℝ)*base67 + (58052525640059/20000000000000000000000000000 : ℝ)*base69 + (76586792279941/20000000000000000000000000000 : ℝ)*base72 + (5831826000059/10000000000000000000000000000 : ℝ)*base73 + (183827601239941/20000000000000000000000000000 : ℝ)*base76 + (86295112439941/20000000000000000000000000000 : ℝ)*base78 + (204658605959941/20000000000000000000000000000 : ℝ)*base80 + (8892466040059/10000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (2181683/625000000000000000000 : ℝ)*base89 + (2181683/625000000000000000000 : ℝ)*base91 + (2181683/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (212743660841510774350731/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (244150489/50000000000000 : ℝ)*(base19) + (9870431/2000000000000 : ℝ)*(base23) + (39788887/50000000000000 : ℝ)*(base32) + (38735931/50000000000000 : ℝ)*(upper3) + (34134781/100000000000000 : ℝ)*(upper5) + (688254630523441/100000000000000 : ℝ)*(major0) + (688254630523441/100000000000000 : ℝ)*(major1) + (688254630523441/100000000000000 : ℝ)*(major2) + (235287641/20000000000000 : ℝ)*(sp1) + (144973949/12500000000000 : ℝ)*(sp2) + (37806036527243/4000000000000 : ℝ)*(sp4) + (945149248441891/100000000000000 : ℝ)*(sp5) + (945149259867933/100000000000000 : ℝ)*(sp6) + (431358197373473/100000000000000 : ℝ)*(sp7) + (26959892309453/6250000000000 : ℝ)*(f.failure) + (37806036527243/4000000000000 : ℝ)*(f.sum) + (143857067616423/100000000000000000000000000000 : ℝ)*base65 + (47886106183577/200000000000000000000000000000 : ℝ)*base68 + (702894644983577/200000000000000000000000000000 : ℝ)*base70 + (498477480383577/200000000000000000000000000000 : ℝ)*base72 + (279613848716423/100000000000000000000000000000 : ℝ)*base73 + (1498617062016423/200000000000000000000000000000 : ℝ)*base75 + (831118714183577/200000000000000000000000000000 : ℝ)*base78 + (285629879183577/200000000000000000000000000000 : ℝ)*base80 + (69284535416423/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (93857/9765625000000000000 : ℝ)*base89 + (93857/9765625000000000000 : ℝ)*base91 + (93857/9765625000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1464_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9972201/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (547/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (653/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1464_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1464_s1_0 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1904785663/10000000000 : ℝ)*x 0 + (5604584117/10000000000 : ℝ)*x 1 + (5073400163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1904785663/10000000000 : ℝ)^4425 ≤ (1445195145829/12500000000000 : ℝ)^3401 := by
    have hnat : (1904785663 : ℕ)^4425*12500000000000^3401 ≤ 1445195145829^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1904785663 10000000000 1445195145829 12500000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5604584117/10000000000 : ℝ)^4425 ≤ (23539804412449/50000000000000 : ℝ)^3401 := by
    have hnat : (5604584117 : ℕ)^4425*50000000000000^3401 ≤ 23539804412449^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5604584117 10000000000 23539804412449 50000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5073400163/10000000000 : ℝ)^4425 ≤ (10339707499367/25000000000000 : ℝ)^3401 := by
    have hnat : (5073400163 : ℕ)^4425*25000000000000^3401 ≤ 10339707499367^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5073400163 10000000000 10339707499367 25000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1904785663/10000000000 : ℝ), (5604584117/10000000000 : ℝ), (5073400163/10000000000 : ℝ)] ![(1445195145829/12500000000000 : ℝ), (23539804412449/50000000000000 : ℝ), (10339707499367/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1904785663/10000000000 : ℝ)|^4425 ≤ (1445195145829/12500000000000 : ℝ)^3401
        have hw : |(-1904785663/10000000000 : ℝ)|=(1904785663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5604584117/10000000000 : ℝ)|^4425 ≤ (23539804412449/50000000000000 : ℝ)^3401
        have hw : |(5604584117/10000000000 : ℝ)|=(5604584117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5073400163/10000000000 : ℝ)|^4425 ≤ (10339707499367/25000000000000 : ℝ)^3401
        have hw : |(5073400163/10000000000 : ℝ)|=(5073400163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1464_s1_1 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2697808007/5000000000 : ℝ)*x 0 + (-2186287113/10000000000 : ℝ)*x 1 + (5073401351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2697808007/5000000000 : ℝ)^4425 ≤ (4480864681817/10000000000000 : ℝ)^3401 := by
    have hnat : (2697808007 : ℕ)^4425*10000000000000^3401 ≤ 4480864681817^3401*5000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697808007 5000000000 4480864681817 10000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2186287113/10000000000 : ℝ)^4425 ≤ (13832510566859/100000000000000 : ℝ)^3401 := by
    have hnat : (2186287113 : ℕ)^4425*100000000000000^3401 ≤ 13832510566859^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186287113 10000000000 13832510566859 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5073401351/10000000000 : ℝ)^4425 ≤ (41358842598097/100000000000000 : ℝ)^3401 := by
    have hnat : (5073401351 : ℕ)^4425*100000000000000^3401 ≤ 41358842598097^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5073401351 10000000000 41358842598097 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2697808007/5000000000 : ℝ), (-2186287113/10000000000 : ℝ), (5073401351/10000000000 : ℝ)] ![(4480864681817/10000000000000 : ℝ), (13832510566859/100000000000000 : ℝ), (41358842598097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2697808007/5000000000 : ℝ)|^4425 ≤ (4480864681817/10000000000000 : ℝ)^3401
        have hw : |(2697808007/5000000000 : ℝ)|=(2697808007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2186287113/10000000000 : ℝ)|^4425 ≤ (13832510566859/100000000000000 : ℝ)^3401
        have hw : |(-2186287113/10000000000 : ℝ)|=(2186287113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5073401351/10000000000 : ℝ)|^4425 ≤ (41358842598097/100000000000000 : ℝ)^3401
        have hw : |(5073401351/10000000000 : ℝ)|=(5073401351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1464_s1_2 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5395617007/10000000000 : ℝ)*x 0 + (1014680053/2000000000 : ℝ)*x 1 + (-2186287209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5395617007/10000000000 : ℝ)^4425 ≤ (44808657547601/100000000000000 : ℝ)^3401 := by
    have hnat : (5395617007 : ℕ)^4425*100000000000000^3401 ≤ 44808657547601^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395617007 10000000000 44808657547601 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1014680053/2000000000 : ℝ)^4425 ≤ (2067941553967/5000000000000 : ℝ)^3401 := by
    have hnat : (1014680053 : ℕ)^4425*5000000000000^3401 ≤ 2067941553967^3401*2000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1014680053 2000000000 2067941553967 5000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2186287209/10000000000 : ℝ)^4425 ≤ (6916255678561/50000000000000 : ℝ)^3401 := by
    have hnat : (2186287209 : ℕ)^4425*50000000000000^3401 ≤ 6916255678561^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186287209 10000000000 6916255678561 50000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5395617007/10000000000 : ℝ), (1014680053/2000000000 : ℝ), (-2186287209/10000000000 : ℝ)] ![(44808657547601/100000000000000 : ℝ), (2067941553967/5000000000000 : ℝ), (6916255678561/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5395617007/10000000000 : ℝ)|^4425 ≤ (44808657547601/100000000000000 : ℝ)^3401
        have hw : |(5395617007/10000000000 : ℝ)|=(5395617007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1014680053/2000000000 : ℝ)|^4425 ≤ (2067941553967/5000000000000 : ℝ)^3401
        have hw : |(1014680053/2000000000 : ℝ)|=(1014680053/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2186287209/10000000000 : ℝ)|^4425 ≤ (6916255678561/50000000000000 : ℝ)^3401
        have hw : |(-2186287209/10000000000 : ℝ)|=(2186287209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1464_s1_3 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2133534219/5000000000 : ℝ)*x 0 + (232499517/625000000 : ℝ)*x 1 + (976773839/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2133534219/5000000000 : ℝ)^4425 ≤ (16509583138317/50000000000000 : ℝ)^3401 := by
    have hnat : (2133534219 : ℕ)^4425*50000000000000^3401 ≤ 16509583138317^3401*5000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133534219 5000000000 16509583138317 50000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (232499517/625000000 : ℝ)^4425 ≤ (13810437583479/50000000000000 : ℝ)^3401 := by
    have hnat : (232499517 : ℕ)^4425*50000000000000^3401 ≤ 13810437583479^3401*625000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      232499517 625000000 13810437583479 50000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (976773839/2000000000 : ℝ)^4425 ≤ (39359958550623/100000000000000 : ℝ)^3401 := by
    have hnat : (976773839 : ℕ)^4425*100000000000000^3401 ≤ 39359958550623^3401*2000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      976773839 2000000000 39359958550623 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2133534219/5000000000 : ℝ), (232499517/625000000 : ℝ), (976773839/2000000000 : ℝ)] ![(16509583138317/50000000000000 : ℝ), (13810437583479/50000000000000 : ℝ), (39359958550623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2133534219/5000000000 : ℝ)|^4425 ≤ (16509583138317/50000000000000 : ℝ)^3401
        have hw : |(2133534219/5000000000 : ℝ)|=(2133534219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(232499517/625000000 : ℝ)|^4425 ≤ (13810437583479/50000000000000 : ℝ)^3401
        have hw : |(232499517/625000000 : ℝ)|=(232499517/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(976773839/2000000000 : ℝ)|^4425 ≤ (39359958550623/100000000000000 : ℝ)^3401
        have hw : |(976773839/2000000000 : ℝ)|=(976773839/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1464_s1_4 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1905194807/10000000000 : ℝ)*x 0 + (5079758571/10000000000 : ℝ)*x 1 + (2799057787/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1905194807/10000000000 : ℝ)^4425 ≤ (1445599048991/12500000000000 : ℝ)^3401 := by
    have hnat : (1905194807 : ℕ)^4425*12500000000000^3401 ≤ 1445599048991^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1905194807 10000000000 1445599048991 12500000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5079758571/10000000000 : ℝ)^4425 ≤ (1657051349717/4000000000000 : ℝ)^3401 := by
    have hnat : (5079758571 : ℕ)^4425*4000000000000^3401 ≤ 1657051349717^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5079758571 10000000000 1657051349717 4000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2799057787/5000000000 : ℝ)^4425 ≤ (47008923854443/100000000000000 : ℝ)^3401 := by
    have hnat : (2799057787 : ℕ)^4425*100000000000000^3401 ≤ 47008923854443^3401*5000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2799057787 5000000000 47008923854443 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1905194807/10000000000 : ℝ), (5079758571/10000000000 : ℝ), (2799057787/5000000000 : ℝ)] ![(1445599048991/12500000000000 : ℝ), (1657051349717/4000000000000 : ℝ), (47008923854443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1905194807/10000000000 : ℝ)|^4425 ≤ (1445599048991/12500000000000 : ℝ)^3401
        have hw : |(-1905194807/10000000000 : ℝ)|=(1905194807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5079758571/10000000000 : ℝ)|^4425 ≤ (1657051349717/4000000000000 : ℝ)^3401
        have hw : |(5079758571/10000000000 : ℝ)|=(5079758571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2799057787/5000000000 : ℝ)|^4425 ≤ (47008923854443/100000000000000 : ℝ)^3401
        have hw : |(2799057787/5000000000 : ℝ)|=(2799057787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1464_s1_5 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256573851/10000000000 : ℝ)*x 0 + (-332314537/2000000000 : ℝ)*x 1 + (21867639/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256573851/10000000000 : ℝ)^4425 ≤ (10828037678971/25000000000000 : ℝ)^3401 := by
    have hnat : (5256573851 : ℕ)^4425*25000000000000^3401 ≤ 10828037678971^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256573851 10000000000 10828037678971 25000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (332314537/2000000000 : ℝ)^4425 ≤ (1935785061453/20000000000000 : ℝ)^3401 := by
    have hnat : (332314537 : ℕ)^4425*20000000000000^3401 ≤ 1935785061453^3401*2000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332314537 2000000000 1935785061453 20000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21867639/39062500 : ℝ)^4425 ≤ (47008923963699/100000000000000 : ℝ)^3401 := by
    have hnat : (21867639 : ℕ)^4425*100000000000000^3401 ≤ 47008923963699^3401*39062500^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21867639 39062500 47008923963699 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256573851/10000000000 : ℝ), (-332314537/2000000000 : ℝ), (21867639/39062500 : ℝ)] ![(10828037678971/25000000000000 : ℝ), (1935785061453/20000000000000 : ℝ), (47008923963699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256573851/10000000000 : ℝ)|^4425 ≤ (10828037678971/25000000000000 : ℝ)^3401
        have hw : |(5256573851/10000000000 : ℝ)|=(5256573851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-332314537/2000000000 : ℝ)|^4425 ≤ (1935785061453/20000000000000 : ℝ)^3401
        have hw : |(-332314537/2000000000 : ℝ)|=(332314537/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21867639/39062500 : ℝ)|^4425 ≤ (47008923963699/100000000000000 : ℝ)^3401
        have hw : |(21867639/39062500 : ℝ)|=(21867639/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1464_s1_6 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (210262957/400000000 : ℝ)*x 0 + (5598115543/10000000000 : ℝ)*x 1 + (-10384829/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210262957/400000000 : ℝ)^4425 ≤ (21656075754599/50000000000000 : ℝ)^3401 := by
    have hnat : (210262957 : ℕ)^4425*50000000000000^3401 ≤ 21656075754599^3401*400000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210262957 400000000 21656075754599 50000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5598115543/10000000000 : ℝ)^4425 ≤ (188035694063/400000000000 : ℝ)^3401 := by
    have hnat : (5598115543 : ℕ)^4425*400000000000^3401 ≤ 188035694063^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5598115543 10000000000 188035694063 400000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10384829/62500000 : ℝ)^4425 ≤ (151233202597/1562500000000 : ℝ)^3401 := by
    have hnat : (10384829 : ℕ)^4425*1562500000000^3401 ≤ 151233202597^3401*62500000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10384829 62500000 151233202597 1562500000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210262957/400000000 : ℝ), (5598115543/10000000000 : ℝ), (-10384829/62500000 : ℝ)] ![(21656075754599/50000000000000 : ℝ), (188035694063/400000000000 : ℝ), (151233202597/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210262957/400000000 : ℝ)|^4425 ≤ (21656075754599/50000000000000 : ℝ)^3401
        have hw : |(210262957/400000000 : ℝ)|=(210262957/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5598115543/10000000000 : ℝ)|^4425 ≤ (188035694063/400000000000 : ℝ)^3401
        have hw : |(5598115543/10000000000 : ℝ)|=(5598115543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-10384829/62500000 : ℝ)|^4425 ≤ (151233202597/1562500000000 : ℝ)^3401
        have hw : |(-10384829/62500000 : ℝ)|=(10384829/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1464_s1_7 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4267965347/10000000000 : ℝ)*x 0 + (2434969111/5000000000 : ℝ)*x 1 + (3734163753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4267965347/10000000000 : ℝ)^4425 ≤ (33028196640741/100000000000000 : ℝ)^3401 := by
    have hnat : (4267965347 : ℕ)^4425*100000000000000^3401 ≤ 33028196640741^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4267965347 10000000000 33028196640741 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2434969111/5000000000 : ℝ)^4425 ≤ (19606972687909/50000000000000 : ℝ)^3401 := by
    have hnat : (2434969111 : ℕ)^4425*50000000000000^3401 ≤ 19606972687909^3401*5000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2434969111 5000000000 19606972687909 50000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3734163753/10000000000 : ℝ)^4425 ≤ (13878928986301/50000000000000 : ℝ)^3401 := by
    have hnat : (3734163753 : ℕ)^4425*50000000000000^3401 ≤ 13878928986301^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3734163753 10000000000 13878928986301 50000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4267965347/10000000000 : ℝ), (2434969111/5000000000 : ℝ), (3734163753/10000000000 : ℝ)] ![(33028196640741/100000000000000 : ℝ), (19606972687909/50000000000000 : ℝ), (13878928986301/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4267965347/10000000000 : ℝ)|^4425 ≤ (33028196640741/100000000000000 : ℝ)^3401
        have hw : |(4267965347/10000000000 : ℝ)|=(4267965347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2434969111/5000000000 : ℝ)|^4425 ≤ (19606972687909/50000000000000 : ℝ)^3401
        have hw : |(2434969111/5000000000 : ℝ)|=(2434969111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3734163753/10000000000 : ℝ)|^4425 ≤ (13878928986301/50000000000000 : ℝ)^3401
        have hw : |(3734163753/10000000000 : ℝ)|=(3734163753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1464_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9972201/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (653/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (547/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (479/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18891/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (653/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (547/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (653/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (547/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (653/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (547/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (653/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (547/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (653/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (547/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (653/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (547/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (547/25000 : ℝ) ^ (4423/1024 : ℝ) ≤ (845311422687/12500000000000000000 : ℝ) := by
    have hpowers : (547/25000 : ℝ)^4423 ≤ (845311422687/12500000000000000000 : ℝ)^1024 := by
      have hnat : (547 : ℕ)^4423*12500000000000000000^1024 ≤ 845311422687^1024*25000^4423 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        547 25000 845311422687 12500000000000000000 4423 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (547/25000 : ℝ)) (X := (845311422687/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4423 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (653/2500 : ℝ) ^ (4423/1024 : ℝ) ≤ (151593742993559499/50000000000000000000 : ℝ) := by
    have hpowers : (653/2500 : ℝ)^4423 ≤ (151593742993559499/50000000000000000000 : ℝ)^1024 := by
      have hnat : (653 : ℕ)^4423*50000000000000000000^1024 ≤ 151593742993559499^1024*2500^4423 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        653 2500 151593742993559499 50000000000000000000 4423 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (653/2500 : ℝ)) (X := (151593742993559499/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4423 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250000845311422687/6250000000000000000 : ℝ) ≤ (5000000156563211/5000000000000000 : ℝ) ^ (4423/1024 : ℝ) := by
    have hpowers : (6250000845311422687/6250000000000000000 : ℝ)^1024 ≤ (5000000156563211/5000000000000000 : ℝ)^4423 := by
      have hnat : (6250000845311422687 : ℕ)^1024*5000000000000000^4423 ≤ 5000000156563211^4423*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250000845311422687 6250000000000000000 5000000156563211 5000000000000000 1024 4423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000156563211/5000000000000000 : ℝ)) (X := (6250000845311422687/6250000000000000000 : ℝ)) (by norm_num) 4423 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50151597124239250247/50000000000000000000 : ℝ) ≤ (10007011301323973/10000000000000000 : ℝ) ^ (4423/1024 : ℝ) := by
    have hpowers : (50151597124239250247/50000000000000000000 : ℝ)^1024 ≤ (10007011301323973/10000000000000000 : ℝ)^4423 := by
      have hnat : (50151597124239250247 : ℕ)^1024*10000000000000000^4423 ≤ 10007011301323973^4423*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50151597124239250247 50000000000000000000 10007011301323973 10000000000000000 1024 4423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007011301323973/10000000000000000 : ℝ)) (X := (50151597124239250247/50000000000000000000 : ℝ)) (by norm_num) 4423 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25151593742993559499/25000000000000000000 : ℝ) ≤ (2503505572380381/2500000000000000 : ℝ) ^ (4423/1024 : ℝ) := by
    have hpowers : (25151593742993559499/25000000000000000000 : ℝ)^1024 ≤ (2503505572380381/2500000000000000 : ℝ)^4423 := by
      have hnat : (25151593742993559499 : ℕ)^1024*2500000000000000^4423 ≤ 2503505572380381^4423*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25151593742993559499 25000000000000000000 2503505572380381 2500000000000000 1024 4423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2503505572380381/2500000000000000 : ℝ)) (X := (25151593742993559499/25000000000000000000 : ℝ)) (by norm_num) 4423 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(845311422687/12500000000000000000 : ℝ) ≤ ((3738895740771703877/3739375000000000000 : ℝ)+2*(7010988197551/2393200000000000 : ℝ)*(547/25000 : ℝ))^(4423/1024 : ℝ) := by
    rw [show (3738895740771703877/3739375000000000000 : ℝ)+2*(7010988197551/2393200000000000 : ℝ)*(547/25000 : ℝ)=(5000000156563211/5000000000000000 : ℝ) by norm_num, show 1+2*(845311422687/12500000000000000000 : ℝ)=(6250000845311422687/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(151593742993559499/50000000000000000000 : ℝ)+(845311422687/12500000000000000000 : ℝ) ≤ ((3738895740771703877/3739375000000000000 : ℝ)+(7010988197551/2393200000000000 : ℝ)*((653/2500 : ℝ)+(547/25000 : ℝ)))^(4423/1024 : ℝ) := by
    rw [show (3738895740771703877/3739375000000000000 : ℝ)+(7010988197551/2393200000000000 : ℝ)*((653/2500 : ℝ)+(547/25000 : ℝ))=(10007011301323973/10000000000000000 : ℝ) by norm_num, show 1+(151593742993559499/50000000000000000000 : ℝ)+(845311422687/12500000000000000000 : ℝ)=(50151597124239250247/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(151593742993559499/50000000000000000000 : ℝ) ≤ ((3738895740771703877/3739375000000000000 : ℝ)+2*(7010988197551/2393200000000000 : ℝ)*(653/2500 : ℝ))^(4423/1024 : ℝ) := by
    rw [show (3738895740771703877/3739375000000000000 : ℝ)+2*(7010988197551/2393200000000000 : ℝ)*(653/2500 : ℝ)=(2503505572380381/2500000000000000 : ℝ) by norm_num, show 1+2*(151593742993559499/50000000000000000000 : ℝ)=(25151593742993559499/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3738895740771703877/3739375000000000000 : ℝ)*(X 1 0+X 2 0)+(7010988197551/2393200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4423/1024 : ℝ)) (lo := (547/25000 : ℝ)) (hi := (653/2500 : ℝ)) (c := (3738895740771703877/3739375000000000000 : ℝ)) (alpha := (7010988197551/2393200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3738895740771703877/3739375000000000000 : ℝ)*(X 0 1+X 2 1)+(7010988197551/2393200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4423/1024 : ℝ)) (lo := (547/25000 : ℝ)) (hi := (653/2500 : ℝ)) (c := (3738895740771703877/3739375000000000000 : ℝ)) (alpha := (7010988197551/2393200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3738895740771703877/3739375000000000000 : ℝ)*(X 0 2+X 1 2)+(7010988197551/2393200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4423/1024 : ℝ)) (lo := (547/25000 : ℝ)) (hi := (653/2500 : ℝ)) (c := (3738895740771703877/3739375000000000000 : ℝ)) (alpha := (7010988197551/2393200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1904785663/10000000000 : ℝ)*X 0 0+(5604584117/10000000000 : ℝ)*X 0 1+(5073400163/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2697808007/5000000000 : ℝ)*X 1 0+(-2186287113/10000000000 : ℝ)*X 1 1+(5073401351/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5395617007/10000000000 : ℝ)*X 2 0+(1014680053/2000000000 : ℝ)*X 2 1+(-2186287209/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2133534219/5000000000 : ℝ)*X 0 0+(232499517/625000000 : ℝ)*X 0 1+(976773839/2000000000 : ℝ)*X 0 2+(2133534219/5000000000 : ℝ)*X 1 0+(232499517/625000000 : ℝ)*X 1 1+(976773839/2000000000 : ℝ)*X 1 2+(2133534219/5000000000 : ℝ)*X 2 0+(232499517/625000000 : ℝ)*X 2 1+(976773839/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1905194807/10000000000 : ℝ)*X 0 0+(5079758571/10000000000 : ℝ)*X 0 1+(2799057787/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5256573851/10000000000 : ℝ)*X 1 0+(-332314537/2000000000 : ℝ)*X 1 1+(21867639/39062500 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((210262957/400000000 : ℝ)*X 2 0+(5598115543/10000000000 : ℝ)*X 2 1+(-10384829/62500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4267965347/10000000000 : ℝ)*X 0 0+(2434969111/5000000000 : ℝ)*X 0 1+(3734163753/10000000000 : ℝ)*X 0 2+(4267965347/10000000000 : ℝ)*X 1 0+(2434969111/5000000000 : ℝ)*X 1 1+(3734163753/10000000000 : ℝ)*X 1 2+(4267965347/10000000000 : ℝ)*X 2 0+(2434969111/5000000000 : ℝ)*X 2 1+(3734163753/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (620266204531767549116233527/93484375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (556174229/50000000000000 : ℝ)*(base19) + (727862549/50000000000000 : ℝ)*(base23) + (98749661/100000000000000 : ℝ)*(upper3) + (104393/6250000000000 : ℝ)*(upper4) + (128733013/100000000000000 : ℝ)*(upper5) + (685454482871439/50000000000000 : ℝ)*(major0) + (685454482871439/50000000000000 : ℝ)*(major1) + (685454482871439/50000000000000 : ℝ)*(major2) + (1882598273909011/100000000000000 : ℝ)*(sp0) + (941304992960713/50000000000000 : ℝ)*(sp1) + (941304821272393/50000000000000 : ℝ)*(sp2) + (214800455221199/25000000000000 : ℝ)*(sp3) + (12824360873/100000000000000 : ℝ)*(sp4) + (4791165341/100000000000000 : ℝ)*(sp7) + (859206612050137/100000000000000 : ℝ)*(f.failure) + (470652774567471/25000000000000 : ℝ)*(f.sum) + (32787406715041/59830000000000000000000000000 : ℝ)*base66 + (1834530265548358869/373937500000000000000000000000000 : ℝ)*base68 + (1378333210525358869/373937500000000000000000000000000 : ℝ)*base70 + (2743943257221171369/373937500000000000000000000000000 : ℝ)*base72 + (185157374188809/59830000000000000000000000000 : ℝ)*base73 + (950601671667421369/373937500000000000000000000000000 : ℝ)*base76 + (1782721783212046369/373937500000000000000000000000000 : ℝ)*base78 + (2505448000683358869/373937500000000000000000000000000 : ℝ)*base80 + (203499777798119/59830000000000000000000000000 : ℝ)*base81 + (741537/625000000000000000000 : ℝ)*base89 + (741537/625000000000000000000 : ℝ)*base91 + (741537/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3609906844028225205717/620000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1104397881/100000000000000 : ℝ)*(base19) + (1209046627/100000000000000 : ℝ)*(base23) + (9450223/6250000000000 : ℝ)*(upper3) + (30212071/100000000000000 : ℝ)*(lower4) + (129759081/100000000000000 : ℝ)*(upper5) + (1404814360748837/100000000000000 : ℝ)*(major0) + (1404814360748837/100000000000000 : ℝ)*(major1) + (1404814360748837/100000000000000 : ℝ)*(major2) + (6420042849/100000000000000 : ℝ)*(sp1) + (1435340977/20000000000000 : ℝ)*(sp2) + (1929171970766803/100000000000000 : ℝ)*(sp4) + (1929164446326073/100000000000000 : ℝ)*(sp5) + (192916358501529/10000000000000 : ℝ)*(sp6) + (440228278324927/50000000000000 : ℝ)*(sp7) + (440228278324927/50000000000000 : ℝ)*(f.failure) + (1929171970766803/100000000000000 : ℝ)*(f.sum) + (1453966411119/620000000000000000000000000 : ℝ)*base65 + (9492047004307039/3875000000000000000000000000000 : ℝ)*base68 + (3478023300932039/3875000000000000000000000000000 : ℝ)*base70 + (19044723042442961/3875000000000000000000000000000 : ℝ)*base71 + (1452396012861/620000000000000000000000000 : ℝ)*base74 + (10471703548307039/3875000000000000000000000000000 : ℝ)*base76 + (15617706227942961/3875000000000000000000000000000 : ℝ)*base77 + (16679980127942961/3875000000000000000000000000000 : ℝ)*base79 + (300350360481/620000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (270673/312500000000000000000 : ℝ)*base90 + (270673/312500000000000000000 : ℝ)*base92 + (270673/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1464_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9972201/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (653/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (547/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (479/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18891/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1464_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1464_s2_0 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-967692481/5000000000 : ℝ)*x 0 + (2737518343/5000000000 : ℝ)*x 1 + (1295807279/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (967692481/5000000000 : ℝ)^4425 ≤ (2360758868639/20000000000000 : ℝ)^3401 := by
    have hnat : (967692481 : ℕ)^4425*20000000000000^3401 ≤ 2360758868639^3401*5000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      967692481 5000000000 2360758868639 20000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2737518343/5000000000 : ℝ)^4425 ≤ (45668687555761/100000000000000 : ℝ)^3401 := by
    have hnat : (2737518343 : ℕ)^4425*100000000000000^3401 ≤ 45668687555761^3401*5000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2737518343 5000000000 45668687555761 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1295807279/2500000000 : ℝ)^4425 ≤ (21263759040559/50000000000000 : ℝ)^3401 := by
    have hnat : (1295807279 : ℕ)^4425*50000000000000^3401 ≤ 21263759040559^3401*2500000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295807279 2500000000 21263759040559 50000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-967692481/5000000000 : ℝ), (2737518343/5000000000 : ℝ), (1295807279/2500000000 : ℝ)] ![(2360758868639/20000000000000 : ℝ), (45668687555761/100000000000000 : ℝ), (21263759040559/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-967692481/5000000000 : ℝ)|^4425 ≤ (2360758868639/20000000000000 : ℝ)^3401
        have hw : |(-967692481/5000000000 : ℝ)|=(967692481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2737518343/5000000000 : ℝ)|^4425 ≤ (45668687555761/100000000000000 : ℝ)^3401
        have hw : |(2737518343/5000000000 : ℝ)|=(2737518343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1295807279/2500000000 : ℝ)|^4425 ≤ (21263759040559/50000000000000 : ℝ)^3401
        have hw : |(1295807279/2500000000 : ℝ)|=(1295807279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1464_s2_1 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2681614901/5000000000 : ℝ)*x 0 + (-2086088621/10000000000 : ℝ)*x 1 + (1295807627/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681614901/5000000000 : ℝ)^4425 ≤ (2222951414943/5000000000000 : ℝ)^3401 := by
    have hnat : (2681614901 : ℕ)^4425*5000000000000^3401 ≤ 2222951414943^3401*5000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681614901 5000000000 2222951414943 5000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2086088621/10000000000 : ℝ)^4425 ≤ (13013438741517/100000000000000 : ℝ)^3401 := by
    have hnat : (2086088621 : ℕ)^4425*100000000000000^3401 ≤ 13013438741517^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086088621 10000000000 13013438741517 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1295807627/2500000000 : ℝ)^4425 ≤ (21263766470503/50000000000000 : ℝ)^3401 := by
    have hnat : (1295807627 : ℕ)^4425*50000000000000^3401 ≤ 21263766470503^3401*2500000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295807627 2500000000 21263766470503 50000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681614901/5000000000 : ℝ), (-2086088621/10000000000 : ℝ), (1295807627/2500000000 : ℝ)] ![(2222951414943/5000000000000 : ℝ), (13013438741517/100000000000000 : ℝ), (21263766470503/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681614901/5000000000 : ℝ)|^4425 ≤ (2222951414943/5000000000000 : ℝ)^3401
        have hw : |(2681614901/5000000000 : ℝ)|=(2681614901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2086088621/10000000000 : ℝ)|^4425 ≤ (13013438741517/100000000000000 : ℝ)^3401
        have hw : |(-2086088621/10000000000 : ℝ)|=(2086088621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1295807627/2500000000 : ℝ)|^4425 ≤ (21263766470503/50000000000000 : ℝ)^3401
        have hw : |(1295807627/2500000000 : ℝ)|=(1295807627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1464_s2_2 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5363230769/10000000000 : ℝ)*x 0 + (2591614831/5000000000 : ℝ)*x 1 + (-2086088449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363230769/10000000000 : ℝ)^4425 ≤ (44459038728437/100000000000000 : ℝ)^3401 := by
    have hnat : (5363230769 : ℕ)^4425*100000000000000^3401 ≤ 44459038728437^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363230769 10000000000 44459038728437 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591614831/5000000000 : ℝ)^4425 ≤ (42527523909781/100000000000000 : ℝ)^3401 := by
    have hnat : (2591614831 : ℕ)^4425*100000000000000^3401 ≤ 42527523909781^3401*5000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591614831 5000000000 42527523909781 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086088449/10000000000 : ℝ)^4425 ≤ (813339834093/6250000000000 : ℝ)^3401 := by
    have hnat : (2086088449 : ℕ)^4425*6250000000000^3401 ≤ 813339834093^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086088449 10000000000 813339834093 6250000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363230769/10000000000 : ℝ), (2591614831/5000000000 : ℝ), (-2086088449/10000000000 : ℝ)] ![(44459038728437/100000000000000 : ℝ), (42527523909781/100000000000000 : ℝ), (813339834093/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363230769/10000000000 : ℝ)|^4425 ≤ (44459038728437/100000000000000 : ℝ)^3401
        have hw : |(5363230769/10000000000 : ℝ)|=(5363230769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591614831/5000000000 : ℝ)|^4425 ≤ (42527523909781/100000000000000 : ℝ)^3401
        have hw : |(2591614831/5000000000 : ℝ)|=(2591614831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2086088449/10000000000 : ℝ)|^4425 ≤ (813339834093/6250000000000 : ℝ)^3401
        have hw : |(-2086088449/10000000000 : ℝ)|=(2086088449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1464_s2_3 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2144418579/5000000000 : ℝ)*x 0 + (3979667121/10000000000 : ℝ)*x 1 + (461904699/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2144418579/5000000000 : ℝ)^4425 ≤ (33238501837877/100000000000000 : ℝ)^3401 := by
    have hnat : (2144418579 : ℕ)^4425*100000000000000^3401 ≤ 33238501837877^3401*5000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144418579 5000000000 33238501837877 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3979667121/10000000000 : ℝ)^4425 ≤ (30155423936131/100000000000000 : ℝ)^3401 := by
    have hnat : (3979667121 : ℕ)^4425*100000000000000^3401 ≤ 30155423936131^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3979667121 10000000000 30155423936131 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (461904699/1000000000 : ℝ)^4425 ≤ (571969909657/1562500000000 : ℝ)^3401 := by
    have hnat : (461904699 : ℕ)^4425*1562500000000^3401 ≤ 571969909657^3401*1000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      461904699 1000000000 571969909657 1562500000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2144418579/5000000000 : ℝ), (3979667121/10000000000 : ℝ), (461904699/1000000000 : ℝ)] ![(33238501837877/100000000000000 : ℝ), (30155423936131/100000000000000 : ℝ), (571969909657/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2144418579/5000000000 : ℝ)|^4425 ≤ (33238501837877/100000000000000 : ℝ)^3401
        have hw : |(2144418579/5000000000 : ℝ)|=(2144418579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3979667121/10000000000 : ℝ)|^4425 ≤ (30155423936131/100000000000000 : ℝ)^3401
        have hw : |(3979667121/10000000000 : ℝ)|=(3979667121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(461904699/1000000000 : ℝ)|^4425 ≤ (571969909657/1562500000000 : ℝ)^3401
        have hw : |(461904699/1000000000 : ℝ)|=(461904699/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1464_s2_4 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1935452589/10000000000 : ℝ)*x 0 + (5185158093/10000000000 : ℝ)*x 1 + (5473089601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1935452589/10000000000 : ℝ)^4425 ≤ (5902165491771/50000000000000 : ℝ)^3401 := by
    have hnat : (1935452589 : ℕ)^4425*50000000000000^3401 ≤ 5902165491771^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1935452589 10000000000 5902165491771 50000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5185158093/10000000000 : ℝ)^4425 ≤ (21274055731021/50000000000000 : ℝ)^3401 := by
    have hnat : (5185158093 : ℕ)^4425*50000000000000^3401 ≤ 21274055731021^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185158093 10000000000 21274055731021 50000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5473089601/10000000000 : ℝ)^4425 ≤ (45647557541133/100000000000000 : ℝ)^3401 := by
    have hnat : (5473089601 : ℕ)^4425*100000000000000^3401 ≤ 45647557541133^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5473089601 10000000000 45647557541133 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1935452589/10000000000 : ℝ), (5185158093/10000000000 : ℝ), (5473089601/10000000000 : ℝ)] ![(5902165491771/50000000000000 : ℝ), (21274055731021/50000000000000 : ℝ), (45647557541133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1935452589/10000000000 : ℝ)|^4425 ≤ (5902165491771/50000000000000 : ℝ)^3401
        have hw : |(-1935452589/10000000000 : ℝ)|=(1935452589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5185158093/10000000000 : ℝ)|^4425 ≤ (21274055731021/50000000000000 : ℝ)^3401
        have hw : |(5185158093/10000000000 : ℝ)|=(5185158093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5473089601/10000000000 : ℝ)|^4425 ≤ (45647557541133/100000000000000 : ℝ)^3401
        have hw : |(5473089601/10000000000 : ℝ)|=(5473089601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1464_s2_5 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (66089953/125000000 : ℝ)*x 0 + (-1796229237/10000000000 : ℝ)*x 1 + (684136209/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66089953/125000000 : ℝ)^4425 ≤ (21820362241019/50000000000000 : ℝ)^3401 := by
    have hnat : (66089953 : ℕ)^4425*50000000000000^3401 ≤ 21820362241019^3401*125000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66089953 125000000 21820362241019 50000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1796229237/10000000000 : ℝ)^4425 ≤ (10711717194507/100000000000000 : ℝ)^3401 := by
    have hnat : (1796229237 : ℕ)^4425*100000000000000^3401 ≤ 10711717194507^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1796229237 10000000000 10711717194507 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (684136209/1250000000 : ℝ)^4425 ≤ (45647558311593/100000000000000 : ℝ)^3401 := by
    have hnat : (684136209 : ℕ)^4425*100000000000000^3401 ≤ 45647558311593^3401*1250000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684136209 1250000000 45647558311593 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66089953/125000000 : ℝ), (-1796229237/10000000000 : ℝ), (684136209/1250000000 : ℝ)] ![(21820362241019/50000000000000 : ℝ), (10711717194507/100000000000000 : ℝ), (45647558311593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66089953/125000000 : ℝ)|^4425 ≤ (21820362241019/50000000000000 : ℝ)^3401
        have hw : |(66089953/125000000 : ℝ)|=(66089953/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1796229237/10000000000 : ℝ)|^4425 ≤ (10711717194507/100000000000000 : ℝ)^3401
        have hw : |(-1796229237/10000000000 : ℝ)|=(1796229237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(684136209/1250000000 : ℝ)|^4425 ≤ (45647558311593/100000000000000 : ℝ)^3401
        have hw : |(684136209/1250000000 : ℝ)|=(684136209/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1464_s2_6 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (211487861/400000000 : ℝ)*x 0 + (5473089687/10000000000 : ℝ)*x 1 + (-898114411/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211487861/400000000 : ℝ)^4425 ≤ (43640727542719/100000000000000 : ℝ)^3401 := by
    have hnat : (211487861 : ℕ)^4425*100000000000000^3401 ≤ 43640727542719^3401*400000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211487861 400000000 43640727542719 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5473089687/10000000000 : ℝ)^4425 ≤ (22823779237183/50000000000000 : ℝ)^3401 := by
    have hnat : (5473089687 : ℕ)^4425*50000000000000^3401 ≤ 22823779237183^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5473089687 10000000000 22823779237183 50000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (898114411/5000000000 : ℝ)^4425 ≤ (2142342794907/20000000000000 : ℝ)^3401 := by
    have hnat : (898114411 : ℕ)^4425*20000000000000^3401 ≤ 2142342794907^3401*5000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898114411 5000000000 2142342794907 20000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211487861/400000000 : ℝ), (5473089687/10000000000 : ℝ), (-898114411/5000000000 : ℝ)] ![(43640727542719/100000000000000 : ℝ), (22823779237183/50000000000000 : ℝ), (2142342794907/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211487861/400000000 : ℝ)|^4425 ≤ (43640727542719/100000000000000 : ℝ)^3401
        have hw : |(211487861/400000000 : ℝ)|=(211487861/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5473089687/10000000000 : ℝ)|^4425 ≤ (22823779237183/50000000000000 : ℝ)^3401
        have hw : |(5473089687/10000000000 : ℝ)|=(5473089687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-898114411/5000000000 : ℝ)|^4425 ≤ (2142342794907/20000000000000 : ℝ)^3401
        have hw : |(-898114411/5000000000 : ℝ)|=(898114411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1464_s2_7 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (857797333/2000000000 : ℝ)*x 0 + (4614820847/10000000000 : ℝ)*x 1 + (79678659/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (857797333/2000000000 : ℝ)^4425 ≤ (33240009389987/100000000000000 : ℝ)^3401 := by
    have hnat : (857797333 : ℕ)^4425*100000000000000^3401 ≤ 33240009389987^3401*2000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      857797333 2000000000 33240009389987 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4614820847/10000000000 : ℝ)^4425 ≤ (36562503795589/100000000000000 : ℝ)^3401 := by
    have hnat : (4614820847 : ℕ)^4425*100000000000000^3401 ≤ 36562503795589^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4614820847 10000000000 36562503795589 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (79678659/200000000 : ℝ)^4425 ≤ (15098743399841/50000000000000 : ℝ)^3401 := by
    have hnat : (79678659 : ℕ)^4425*50000000000000^3401 ≤ 15098743399841^3401*200000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79678659 200000000 15098743399841 50000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(857797333/2000000000 : ℝ), (4614820847/10000000000 : ℝ), (79678659/200000000 : ℝ)] ![(33240009389987/100000000000000 : ℝ), (36562503795589/100000000000000 : ℝ), (15098743399841/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(857797333/2000000000 : ℝ)|^4425 ≤ (33240009389987/100000000000000 : ℝ)^3401
        have hw : |(857797333/2000000000 : ℝ)|=(857797333/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4614820847/10000000000 : ℝ)|^4425 ≤ (36562503795589/100000000000000 : ℝ)^3401
        have hw : |(4614820847/10000000000 : ℝ)|=(4614820847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(79678659/200000000 : ℝ)|^4425 ≤ (15098743399841/50000000000000 : ℝ)^3401
        have hw : |(79678659/200000000 : ℝ)|=(79678659/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1464_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9972201/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18891/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (479/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (10039/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16209/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18891/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (479/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18891/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (479/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18891/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (479/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18891/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (479/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18891/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (479/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18891/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (479/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (479/6250 : ℝ) ^ (4423/1024 : ℝ) ≤ (151910759232677/10000000000000000000 : ℝ) := by
    have hpowers : (479/6250 : ℝ)^4423 ≤ (151910759232677/10000000000000000000 : ℝ)^1024 := by
      have hnat : (479 : ℕ)^4423*10000000000000000000^1024 ≤ 151910759232677^1024*6250^4423 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        479 6250 151910759232677 10000000000000000000 4423 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (479/6250 : ℝ)) (X := (151910759232677/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4423 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18891/100000 : ℝ) ^ (4423/1024 : ℝ) ≤ (37400033545732833/50000000000000000000 : ℝ) := by
    have hpowers : (18891/100000 : ℝ)^4423 ≤ (37400033545732833/50000000000000000000 : ℝ)^1024 := by
      have hnat : (18891 : ℕ)^4423*50000000000000000000^1024 ≤ 37400033545732833^1024*100000^4423 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18891 100000 37400033545732833 50000000000000000000 4423 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18891/100000 : ℝ)) (X := (37400033545732833/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4423 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000151910759232677/5000000000000000000 : ℝ) ≤ (5000035169523289/5000000000000000 : ℝ) ^ (4423/1024 : ℝ) := by
    have hpowers : (5000151910759232677/5000000000000000000 : ℝ)^1024 ≤ (5000035169523289/5000000000000000 : ℝ)^4423 := by
      have hnat : (5000151910759232677 : ℕ)^1024*5000000000000000^4423 ≤ 5000035169523289^4423*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000151910759232677 5000000000000000000 5000035169523289 5000000000000000 1024 4423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000035169523289/5000000000000000 : ℝ)) (X := (5000151910759232677/5000000000000000000 : ℝ)) (by norm_num) 4423 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25019079793670948109/25000000000000000000 : ℝ) ≤ (10001766401253803/10000000000000000 : ℝ) ^ (4423/1024 : ℝ) := by
    have hpowers : (25019079793670948109/25000000000000000000 : ℝ)^1024 ≤ (10001766401253803/10000000000000000 : ℝ)^4423 := by
      have hnat : (25019079793670948109 : ℕ)^1024*10000000000000000^4423 ≤ 10001766401253803^4423*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25019079793670948109 25000000000000000000 10001766401253803 10000000000000000 1024 4423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001766401253803/10000000000000000 : ℝ)) (X := (25019079793670948109/25000000000000000000 : ℝ)) (by norm_num) 4423 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25037400033545732833/25000000000000000000 : ℝ) ≤ (2500865615865257/2500000000000000 : ℝ) ^ (4423/1024 : ℝ) := by
    have hpowers : (25037400033545732833/25000000000000000000 : ℝ)^1024 ≤ (2500865615865257/2500000000000000 : ℝ)^4423 := by
      have hnat : (25037400033545732833 : ℕ)^1024*2500000000000000^4423 ≤ 2500865615865257^4423*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25037400033545732833 25000000000000000000 2500865615865257 2500000000000000 1024 4423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500865615865257/2500000000000000 : ℝ)) (X := (25037400033545732833/25000000000000000000 : ℝ)) (by norm_num) 4423 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(151910759232677/10000000000000000000 : ℝ) ≤ ((56122396227481793203/56135000000000000000 : ℝ)+2*(67842488289/44908000000000 : ℝ)*(479/6250 : ℝ))^(4423/1024 : ℝ) := by
    rw [show (56122396227481793203/56135000000000000000 : ℝ)+2*(67842488289/44908000000000 : ℝ)*(479/6250 : ℝ)=(5000035169523289/5000000000000000 : ℝ) by norm_num, show 1+2*(151910759232677/10000000000000000000 : ℝ)=(5000151910759232677/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37400033545732833/50000000000000000000 : ℝ)+(151910759232677/10000000000000000000 : ℝ) ≤ ((56122396227481793203/56135000000000000000 : ℝ)+(67842488289/44908000000000 : ℝ)*((18891/100000 : ℝ)+(479/6250 : ℝ)))^(4423/1024 : ℝ) := by
    rw [show (56122396227481793203/56135000000000000000 : ℝ)+(67842488289/44908000000000 : ℝ)*((18891/100000 : ℝ)+(479/6250 : ℝ))=(10001766401253803/10000000000000000 : ℝ) by norm_num, show 1+(37400033545732833/50000000000000000000 : ℝ)+(151910759232677/10000000000000000000 : ℝ)=(25019079793670948109/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37400033545732833/50000000000000000000 : ℝ) ≤ ((56122396227481793203/56135000000000000000 : ℝ)+2*(67842488289/44908000000000 : ℝ)*(18891/100000 : ℝ))^(4423/1024 : ℝ) := by
    rw [show (56122396227481793203/56135000000000000000 : ℝ)+2*(67842488289/44908000000000 : ℝ)*(18891/100000 : ℝ)=(2500865615865257/2500000000000000 : ℝ) by norm_num, show 1+2*(37400033545732833/50000000000000000000 : ℝ)=(25037400033545732833/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (56122396227481793203/56135000000000000000 : ℝ)*(X 1 0+X 2 0)+(67842488289/44908000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4423/1024 : ℝ)) (lo := (479/6250 : ℝ)) (hi := (18891/100000 : ℝ)) (c := (56122396227481793203/56135000000000000000 : ℝ)) (alpha := (67842488289/44908000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (56122396227481793203/56135000000000000000 : ℝ)*(X 0 1+X 2 1)+(67842488289/44908000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4423/1024 : ℝ)) (lo := (479/6250 : ℝ)) (hi := (18891/100000 : ℝ)) (c := (56122396227481793203/56135000000000000000 : ℝ)) (alpha := (67842488289/44908000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (56122396227481793203/56135000000000000000 : ℝ)*(X 0 2+X 1 2)+(67842488289/44908000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4423/1024 : ℝ)) (lo := (479/6250 : ℝ)) (hi := (18891/100000 : ℝ)) (c := (56122396227481793203/56135000000000000000 : ℝ)) (alpha := (67842488289/44908000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-967692481/5000000000 : ℝ)*X 0 0+(2737518343/5000000000 : ℝ)*X 0 1+(1295807279/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2681614901/5000000000 : ℝ)*X 1 0+(-2086088621/10000000000 : ℝ)*X 1 1+(1295807627/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5363230769/10000000000 : ℝ)*X 2 0+(2591614831/5000000000 : ℝ)*X 2 1+(-2086088449/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2144418579/5000000000 : ℝ)*X 0 0+(3979667121/10000000000 : ℝ)*X 0 1+(461904699/1000000000 : ℝ)*X 0 2+(2144418579/5000000000 : ℝ)*X 1 0+(3979667121/10000000000 : ℝ)*X 1 1+(461904699/1000000000 : ℝ)*X 1 2+(2144418579/5000000000 : ℝ)*X 2 0+(3979667121/10000000000 : ℝ)*X 2 1+(461904699/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1935452589/10000000000 : ℝ)*X 0 0+(5185158093/10000000000 : ℝ)*X 0 1+(5473089601/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((66089953/125000000 : ℝ)*X 1 0+(-1796229237/10000000000 : ℝ)*X 1 1+(684136209/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((211487861/400000000 : ℝ)*X 2 0+(5473089687/10000000000 : ℝ)*X 2 1+(-898114411/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((857797333/2000000000 : ℝ)*X 0 0+(4614820847/10000000000 : ℝ)*X 0 1+(79678659/200000000 : ℝ)*X 0 2+(857797333/2000000000 : ℝ)*X 1 0+(4614820847/10000000000 : ℝ)*X 1 1+(79678659/200000000 : ℝ)*X 1 2+(857797333/2000000000 : ℝ)*X 2 0+(4614820847/10000000000 : ℝ)*X 2 1+(79678659/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1214509896339560355816011769/175421875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (264848559/25000000000000 : ℝ)*(base19) + (1414459283/100000000000000 : ℝ)*(base23) + (140815689/100000000000000 : ℝ)*(upper3) + (17619767/12500000000000 : ℝ)*(upper4) + (191053283/100000000000000 : ℝ)*(upper5) + (311937837857991/12500000000000 : ℝ)*(major0) + (311937837857991/12500000000000 : ℝ)*(major1) + (311937837857991/12500000000000 : ℝ)*(major2) + (342693891520269/10000000000000 : ℝ)*(sp0) + (3426967059653083/100000000000000 : ℝ)*(sp1) + (856741676147009/25000000000000 : ℝ)*(sp2) + (1564025534178893/100000000000000 : ℝ)*(sp3) + (7300961157/25000000000000 : ℝ)*(sp4) + (11521722763/100000000000000 : ℝ)*(sp7) + (195504631987707/12500000000000 : ℝ)*(f.failure) + (1713484059523659/50000000000000 : ℝ)*(f.sum) + (10512200693499/11227000000000000000000000000 : ℝ)*base66 + (2488396554256410173/701687500000000000000000000000000 : ℝ)*base67 + (3427657995237964827/701687500000000000000000000000000 : ℝ)*base70 + (1407768195388527327/701687500000000000000000000000000 : ℝ)*base72 + (19016190743943/11227000000000000000000000000 : ℝ)*base73 + (7024382304862464827/701687500000000000000000000000000 : ℝ)*base76 + (2542888146937652327/701687500000000000000000000000000 : ℝ)*base78 + (3981768515492089827/701687500000000000000000000000000 : ℝ)*base80 + (6680943351587/2806750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (16893/78125000000000000000 : ℝ)*base90 + (16893/78125000000000000000 : ℝ)*base92 + (16893/78125000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4042407112016458989076620363/701687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (282201941/50000000000000 : ℝ)*(base19) + (480460877/50000000000000 : ℝ)*(base23) + (115742209/100000000000000 : ℝ)*(upper3) + (29879611/50000000000000 : ℝ)*(lower4) + (124815247/100000000000000 : ℝ)*(upper5) + (1264529215535907/50000000000000 : ℝ)*(major0) + (1264529215535907/50000000000000 : ℝ)*(major1) + (1264529215535907/50000000000000 : ℝ)*(major2) + (2836153441/50000000000000 : ℝ)*(sp1) + (6183678569/50000000000000 : ℝ)*(sp2) + (1736524410288087/50000000000000 : ℝ)*(sp4) + (347304258386541/10000000000000 : ℝ)*(sp5) + (1736517746148641/50000000000000 : ℝ)*(sp6) + (792533924767403/50000000000000 : ℝ)*(sp7) + (792533924767403/50000000000000 : ℝ)*(f.failure) + (1736524410288087/50000000000000 : ℝ)*(f.sum) + (23033597251911/5613500000000000000000000000 : ℝ)*base65 + (19094231110633209879/2806750000000000000000000000000000 : ℝ)*base68 + (32224340678650709879/2806750000000000000000000000000000 : ℝ)*base70 + (17563493171359290121/2806750000000000000000000000000000 : ℝ)*base71 + (487799600759/112270000000000000000000000 : ℝ)*base73 + (54908592420514209879/2806750000000000000000000000000000 : ℝ)*base76 + (14266647207794709879/2806750000000000000000000000000000 : ℝ)*base78 + (9950630855912209879/2806750000000000000000000000000000 : ℝ)*base80 + (6779707913303/2806750000000000000000000000 : ℝ)*base81 + (2214003/312500000000000000000 : ℝ)*base89 + (2214003/312500000000000000000 : ℝ)*base91 + (2214003/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1464_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9972201/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18891/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (479/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10039/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16209/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1464_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1464_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9972201/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10039/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16209/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1464_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1464_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1464_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9972201/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10039/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16209/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1464_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

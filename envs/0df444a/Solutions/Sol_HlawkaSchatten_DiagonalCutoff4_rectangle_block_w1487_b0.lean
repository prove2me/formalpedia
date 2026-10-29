-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1487_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:14:53.340076+00:00
-- url     : https://prove2.me/submissions/af760cee-fb35-4881-baf0-c143da8c4511

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
theorem support_rectangle_w1487_s0_0 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-342534687/2000000000 : ℝ)*x 0 + (1483084619/2500000000 : ℝ)*x 1 + (2422239737/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (342534687/2000000000 : ℝ)^4471 ≤ (10139635143313/100000000000000 : ℝ)^3447 := by
    have hnat : (342534687 : ℕ)^4471*100000000000000^3447 ≤ 10139635143313^3447*2000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342534687 2000000000 10139635143313 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1483084619/2500000000 : ℝ)^4471 ≤ (50799351247263/100000000000000 : ℝ)^3447 := by
    have hnat : (1483084619 : ℕ)^4471*100000000000000^3447 ≤ 50799351247263^3447*2500000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1483084619 2500000000 50799351247263 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2422239737/5000000000 : ℝ)^4471 ≤ (610328337413/1562500000000 : ℝ)^3447 := by
    have hnat : (2422239737 : ℕ)^4471*1562500000000^3447 ≤ 610328337413^3447*5000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2422239737 5000000000 610328337413 1562500000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-342534687/2000000000 : ℝ), (1483084619/2500000000 : ℝ), (2422239737/5000000000 : ℝ)] ![(10139635143313/100000000000000 : ℝ), (50799351247263/100000000000000 : ℝ), (610328337413/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-342534687/2000000000 : ℝ)|^4471 ≤ (10139635143313/100000000000000 : ℝ)^3447
        have hw : |(-342534687/2000000000 : ℝ)|=(342534687/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1483084619/2500000000 : ℝ)|^4471 ≤ (50799351247263/100000000000000 : ℝ)^3447
        have hw : |(1483084619/2500000000 : ℝ)|=(1483084619/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2422239737/5000000000 : ℝ)|^4471 ≤ (610328337413/1562500000000 : ℝ)^3447
        have hw : |(2422239737/5000000000 : ℝ)|=(2422239737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_s0_1 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (219337609/400000000 : ℝ)*x 0 + (-145277121/625000000 : ℝ)*x 1 + (4844479473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (219337609/400000000 : ℝ)^4471 ≤ (45870517946647/100000000000000 : ℝ)^3447 := by
    have hnat : (219337609 : ℕ)^4471*100000000000000^3447 ≤ 45870517946647^3447*400000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219337609 400000000 45870517946647 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (145277121/625000000 : ℝ)^4471 ≤ (15068468462233/100000000000000 : ℝ)^3447 := by
    have hnat : (145277121 : ℕ)^4471*100000000000000^3447 ≤ 15068468462233^3447*625000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      145277121 625000000 15068468462233 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4844479473/10000000000 : ℝ)^4471 ≤ (39061013583973/100000000000000 : ℝ)^3447 := by
    have hnat : (4844479473 : ℕ)^4471*100000000000000^3447 ≤ 39061013583973^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4844479473 10000000000 39061013583973 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(219337609/400000000 : ℝ), (-145277121/625000000 : ℝ), (4844479473/10000000000 : ℝ)] ![(45870517946647/100000000000000 : ℝ), (15068468462233/100000000000000 : ℝ), (39061013583973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(219337609/400000000 : ℝ)|^4471 ≤ (45870517946647/100000000000000 : ℝ)^3447
        have hw : |(219337609/400000000 : ℝ)|=(219337609/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-145277121/625000000 : ℝ)|^4471 ≤ (15068468462233/100000000000000 : ℝ)^3447
        have hw : |(-145277121/625000000 : ℝ)|=(145277121/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4844479473/10000000000 : ℝ)|^4471 ≤ (39061013583973/100000000000000 : ℝ)^3447
        have hw : |(4844479473/10000000000 : ℝ)|=(4844479473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_s0_2 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5483440211/10000000000 : ℝ)*x 0 + (4844479507/10000000000 : ℝ)*x 1 + (-2324433911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5483440211/10000000000 : ℝ)^4471 ≤ (22935258897371/50000000000000 : ℝ)^3447 := by
    have hnat : (5483440211 : ℕ)^4471*50000000000000^3447 ≤ 22935258897371^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5483440211 10000000000 22935258897371 50000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4844479507/10000000000 : ℝ)^4471 ≤ (7812202787911/20000000000000 : ℝ)^3447 := by
    have hnat : (4844479507 : ℕ)^4471*20000000000000^3447 ≤ 7812202787911^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4844479507 10000000000 7812202787911 20000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2324433911/10000000000 : ℝ)^4471 ≤ (7534234126011/50000000000000 : ℝ)^3447 := by
    have hnat : (2324433911 : ℕ)^4471*50000000000000^3447 ≤ 7534234126011^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2324433911 10000000000 7534234126011 50000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5483440211/10000000000 : ℝ), (4844479507/10000000000 : ℝ), (-2324433911/10000000000 : ℝ)] ![(22935258897371/50000000000000 : ℝ), (7812202787911/20000000000000 : ℝ), (7534234126011/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5483440211/10000000000 : ℝ)|^4471 ≤ (22935258897371/50000000000000 : ℝ)^3447
        have hw : |(5483440211/10000000000 : ℝ)|=(5483440211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4844479507/10000000000 : ℝ)|^4471 ≤ (7812202787911/20000000000000 : ℝ)^3447
        have hw : |(4844479507/10000000000 : ℝ)|=(4844479507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2324433911/10000000000 : ℝ)|^4471 ≤ (7534234126011/50000000000000 : ℝ)^3447
        have hw : |(-2324433911/10000000000 : ℝ)|=(2324433911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_s0_3 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (518994307/1250000000 : ℝ)*x 0 + (386418939/1250000000 : ℝ)*x 1 + (2757385629/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (518994307/1250000000 : ℝ)^4471 ≤ (31977676692569/100000000000000 : ℝ)^3447 := by
    have hnat : (518994307 : ℕ)^4471*100000000000000^3447 ≤ 31977676692569^3447*1250000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518994307 1250000000 31977676692569 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (386418939/1250000000 : ℝ)^4471 ≤ (2181156441279/10000000000000 : ℝ)^3447 := by
    have hnat : (386418939 : ℕ)^4471*10000000000000^3447 ≤ 2181156441279^3447*1250000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      386418939 1250000000 2181156441279 10000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2757385629/5000000000 : ℝ)^4471 ≤ (23105379441591/50000000000000 : ℝ)^3447 := by
    have hnat : (2757385629 : ℕ)^4471*50000000000000^3447 ≤ 23105379441591^3447*5000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757385629 5000000000 23105379441591 50000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(518994307/1250000000 : ℝ), (386418939/1250000000 : ℝ), (2757385629/5000000000 : ℝ)] ![(31977676692569/100000000000000 : ℝ), (2181156441279/10000000000000 : ℝ), (23105379441591/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(518994307/1250000000 : ℝ)|^4471 ≤ (31977676692569/100000000000000 : ℝ)^3447
        have hw : |(518994307/1250000000 : ℝ)|=(518994307/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(386418939/1250000000 : ℝ)|^4471 ≤ (2181156441279/10000000000000 : ℝ)^3447
        have hw : |(386418939/1250000000 : ℝ)|=(386418939/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2757385629/5000000000 : ℝ)|^4471 ≤ (23105379441591/50000000000000 : ℝ)^3447
        have hw : |(2757385629/5000000000 : ℝ)|=(2757385629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_s0_4 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-858206651/5000000000 : ℝ)*x 0 + (4872354489/10000000000 : ℝ)*x 1 + (5903461697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (858206651/5000000000 : ℝ)^4471 ≤ (2542090830247/25000000000000 : ℝ)^3447 := by
    have hnat : (858206651 : ℕ)^4471*25000000000000^3447 ≤ 2542090830247^3447*5000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      858206651 5000000000 2542090830247 25000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4872354489/10000000000 : ℝ)^4471 ≤ (39352786798333/100000000000000 : ℝ)^3447 := by
    have hnat : (4872354489 : ℕ)^4471*100000000000000^3447 ≤ 39352786798333^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4872354489 10000000000 39352786798333 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5903461697/10000000000 : ℝ)^4471 ≤ (50478849868457/100000000000000 : ℝ)^3447 := by
    have hnat : (5903461697 : ℕ)^4471*100000000000000^3447 ≤ 50478849868457^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5903461697 10000000000 50478849868457 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-858206651/5000000000 : ℝ), (4872354489/10000000000 : ℝ), (5903461697/10000000000 : ℝ)] ![(2542090830247/25000000000000 : ℝ), (39352786798333/100000000000000 : ℝ), (50478849868457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-858206651/5000000000 : ℝ)|^4471 ≤ (2542090830247/25000000000000 : ℝ)^3447
        have hw : |(-858206651/5000000000 : ℝ)|=(858206651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4872354489/10000000000 : ℝ)|^4471 ≤ (39352786798333/100000000000000 : ℝ)^3447
        have hw : |(4872354489/10000000000 : ℝ)|=(4872354489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5903461697/10000000000 : ℝ)|^4471 ≤ (50478849868457/100000000000000 : ℝ)^3447
        have hw : |(5903461697/10000000000 : ℝ)|=(5903461697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_s0_5 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (324147511/625000000 : ℝ)*x 0 + (-1265451611/10000000000 : ℝ)*x 1 + (1475865437/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (324147511/625000000 : ℝ)^4471 ≤ (4267337108417/10000000000000 : ℝ)^3447 := by
    have hnat : (324147511 : ℕ)^4471*10000000000000^3447 ≤ 4267337108417^3447*625000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324147511 625000000 4267337108417 10000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1265451611/10000000000 : ℝ)^4471 ≤ (3423889233717/50000000000000 : ℝ)^3447 := by
    have hnat : (1265451611 : ℕ)^4471*50000000000000^3447 ≤ 3423889233717^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1265451611 10000000000 3423889233717 50000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1475865437/2500000000 : ℝ)^4471 ≤ (12619712608523/25000000000000 : ℝ)^3447 := by
    have hnat : (1475865437 : ℕ)^4471*25000000000000^3447 ≤ 12619712608523^3447*2500000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1475865437 2500000000 12619712608523 25000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(324147511/625000000 : ℝ), (-1265451611/10000000000 : ℝ), (1475865437/2500000000 : ℝ)] ![(4267337108417/10000000000000 : ℝ), (3423889233717/50000000000000 : ℝ), (12619712608523/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(324147511/625000000 : ℝ)|^4471 ≤ (4267337108417/10000000000000 : ℝ)^3447
        have hw : |(324147511/625000000 : ℝ)|=(324147511/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1265451611/10000000000 : ℝ)|^4471 ≤ (3423889233717/50000000000000 : ℝ)^3447
        have hw : |(-1265451611/10000000000 : ℝ)|=(1265451611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1475865437/2500000000 : ℝ)|^4471 ≤ (12619712608523/25000000000000 : ℝ)^3447
        have hw : |(1475865437/2500000000 : ℝ)|=(1475865437/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_s0_6 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1037272047/2000000000 : ℝ)*x 0 + (5903461621/10000000000 : ℝ)*x 1 + (-632725861/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1037272047/2000000000 : ℝ)^4471 ≤ (8534674342767/20000000000000 : ℝ)^3447 := by
    have hnat : (1037272047 : ℕ)^4471*20000000000000^3447 ≤ 8534674342767^3447*2000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037272047 2000000000 8534674342767 20000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5903461621/10000000000 : ℝ)^4471 ≤ (1009576980511/2000000000000 : ℝ)^3447 := by
    have hnat : (5903461621 : ℕ)^4471*2000000000000^3447 ≤ 1009576980511^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5903461621 10000000000 1009576980511 2000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (632725861/5000000000 : ℝ)^4471 ≤ (6847779246529/100000000000000 : ℝ)^3447 := by
    have hnat : (632725861 : ℕ)^4471*100000000000000^3447 ≤ 6847779246529^3447*5000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      632725861 5000000000 6847779246529 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1037272047/2000000000 : ℝ), (5903461621/10000000000 : ℝ), (-632725861/5000000000 : ℝ)] ![(8534674342767/20000000000000 : ℝ), (1009576980511/2000000000000 : ℝ), (6847779246529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1037272047/2000000000 : ℝ)|^4471 ≤ (8534674342767/20000000000000 : ℝ)^3447
        have hw : |(1037272047/2000000000 : ℝ)|=(1037272047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5903461621/10000000000 : ℝ)|^4471 ≤ (1009576980511/2000000000000 : ℝ)^3447
        have hw : |(5903461621/10000000000 : ℝ)|=(5903461621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-632725861/5000000000 : ℝ)|^4471 ≤ (6847779246529/100000000000000 : ℝ)^3447
        have hw : |(-632725861/5000000000 : ℝ)|=(632725861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_s0_7 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (260017881/625000000 : ℝ)*x 0 + (545267417/1000000000 : ℝ)*x 1 + (1577840143/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (260017881/625000000 : ℝ)^4471 ≤ (32060933082533/100000000000000 : ℝ)^3447 := by
    have hnat : (260017881 : ℕ)^4471*100000000000000^3447 ≤ 32060933082533^3447*625000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260017881 625000000 32060933082533 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (545267417/1000000000 : ℝ)^4471 ≤ (5692121740251/12500000000000 : ℝ)^3447 := by
    have hnat : (545267417 : ℕ)^4471*12500000000000^3447 ≤ 5692121740251^3447*1000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545267417 1000000000 5692121740251 12500000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1577840143/5000000000 : ℝ)^4471 ≤ (11201046489421/50000000000000 : ℝ)^3447 := by
    have hnat : (1577840143 : ℕ)^4471*50000000000000^3447 ≤ 11201046489421^3447*5000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1577840143 5000000000 11201046489421 50000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(260017881/625000000 : ℝ), (545267417/1000000000 : ℝ), (1577840143/5000000000 : ℝ)] ![(32060933082533/100000000000000 : ℝ), (5692121740251/12500000000000 : ℝ), (11201046489421/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(260017881/625000000 : ℝ)|^4471 ≤ (32060933082533/100000000000000 : ℝ)^3447
        have hw : |(260017881/625000000 : ℝ)|=(260017881/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(545267417/1000000000 : ℝ)|^4471 ≤ (5692121740251/12500000000000 : ℝ)^3447
        have hw : |(545267417/1000000000 : ℝ)|=(545267417/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1577840143/5000000000 : ℝ)|^4471 ≤ (11201046489421/50000000000000 : ℝ)^3447
        have hw : |(1577840143/5000000000 : ℝ)|=(1577840143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1487_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80692417/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1/40 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6453/25000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4469/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4469 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4469*1^1024 ≤ 0^1024*1^4469 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4469 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4469 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4469/1024 : ℝ) ≤ (1833526571926763861/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4469 ≤ (1833526571926763861/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4469*100000000000000000000^1024 ≤ 1833526571926763861^1024*5^4469 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1833526571926763861 100000000000000000000 4469 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1833526571926763861/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4469 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4469/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4469 := by
      have hnat : (1 : ℕ)^1024*1^4469 ≤ 1^4469*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4469 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4469 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101833526571926763861/100000000000000000000 : ℝ) ≤ (2510429651342101/2500000000000000 : ℝ) ^ (4469/1024 : ℝ) := by
    have hpowers : (101833526571926763861/100000000000000000000 : ℝ)^1024 ≤ (2510429651342101/2500000000000000 : ℝ)^4469 := by
      have hnat : (101833526571926763861 : ℕ)^1024*2500000000000000^4469 ≤ 2510429651342101^4469*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101833526571926763861 100000000000000000000 2510429651342101 2500000000000000 1024 4469 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2510429651342101/2500000000000000 : ℝ)) (X := (101833526571926763861/100000000000000000000 : ℝ)) (by norm_num) 4469 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51833526571926763861/50000000000000000000 : ℝ) ≤ (1260429651342101/1250000000000000 : ℝ) ^ (4469/1024 : ℝ) := by
    have hpowers : (51833526571926763861/50000000000000000000 : ℝ)^1024 ≤ (1260429651342101/1250000000000000 : ℝ)^4469 := by
      have hnat : (51833526571926763861 : ℕ)^1024*1250000000000000^4469 ≤ 1260429651342101^4469*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51833526571926763861 50000000000000000000 1260429651342101 1250000000000000 1024 4469 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1260429651342101/1250000000000000 : ℝ)) (X := (51833526571926763861/50000000000000000000 : ℝ)) (by norm_num) 4469 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(10429651342101/1000000000000000 : ℝ)*(0 : ℝ))^(4469/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(10429651342101/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1833526571926763861/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(10429651342101/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4469/1024 : ℝ) := by
    rw [show (1 : ℝ)+(10429651342101/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2510429651342101/2500000000000000 : ℝ) by norm_num, show 1+(1833526571926763861/100000000000000000000 : ℝ)+(0 : ℝ)=(101833526571926763861/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1833526571926763861/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(10429651342101/1000000000000000 : ℝ)*(2/5 : ℝ))^(4469/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(10429651342101/1000000000000000 : ℝ)*(2/5 : ℝ)=(1260429651342101/1250000000000000 : ℝ) by norm_num, show 1+2*(1833526571926763861/100000000000000000000 : ℝ)=(51833526571926763861/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(10429651342101/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4469/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (10429651342101/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(10429651342101/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4469/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (10429651342101/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(10429651342101/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4469/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (10429651342101/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-342534687/2000000000 : ℝ)*X 0 0+(1483084619/2500000000 : ℝ)*X 0 1+(2422239737/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((219337609/400000000 : ℝ)*X 1 0+(-145277121/625000000 : ℝ)*X 1 1+(4844479473/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5483440211/10000000000 : ℝ)*X 2 0+(4844479507/10000000000 : ℝ)*X 2 1+(-2324433911/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((518994307/1250000000 : ℝ)*X 0 0+(386418939/1250000000 : ℝ)*X 0 1+(2757385629/5000000000 : ℝ)*X 0 2+(518994307/1250000000 : ℝ)*X 1 0+(386418939/1250000000 : ℝ)*X 1 1+(2757385629/5000000000 : ℝ)*X 1 2+(518994307/1250000000 : ℝ)*X 2 0+(386418939/1250000000 : ℝ)*X 2 1+(2757385629/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-858206651/5000000000 : ℝ)*X 0 0+(4872354489/10000000000 : ℝ)*X 0 1+(5903461697/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((324147511/625000000 : ℝ)*X 1 0+(-1265451611/10000000000 : ℝ)*X 1 1+(1475865437/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1037272047/2000000000 : ℝ)*X 2 0+(5903461621/10000000000 : ℝ)*X 2 1+(-632725861/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((260017881/625000000 : ℝ)*X 0 0+(545267417/1000000000 : ℝ)*X 0 1+(1577840143/5000000000 : ℝ)*X 0 2+(260017881/625000000 : ℝ)*X 1 0+(545267417/1000000000 : ℝ)*X 1 1+(1577840143/5000000000 : ℝ)*X 1 2+(260017881/625000000 : ℝ)*X 2 0+(545267417/1000000000 : ℝ)*X 2 1+(1577840143/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (122930506626199979709651/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (25355151/100000000000000 : ℝ)*(base1) + (110051279/20000000000000 : ℝ)*(base19) + (109581889/20000000000000 : ℝ)*(base23) + (64997041/100000000000000 : ℝ)*(upper3) + (71110387/100000000000000 : ℝ)*(upper5) + (665941153062483/100000000000000 : ℝ)*(major0) + (665941153062483/100000000000000 : ℝ)*(major1) + (665941153062483/100000000000000 : ℝ)*(major2) + (229809645600129/25000000000000 : ℝ)*(sp0) + (229809988753573/25000000000000 : ℝ)*(sp1) + (459619978680621/50000000000000 : ℝ)*(sp2) + (206320424717219/50000000000000 : ℝ)*(sp3) + (1948225323/100000000000000 : ℝ)*(sp4) + (844111013/100000000000000 : ℝ)*(sp7) + (206320859450301/50000000000000 : ℝ)*(f.failure) + (28726265789709/3125000000000 : ℝ)*(f.sum) + (27932337003217/50000000000000000000000000000 : ℝ)*base66 + (106748958596783/100000000000000000000000000000 : ℝ)*base67 + (388946182203217/100000000000000000000000000000 : ℝ)*base70 + (413184593896783/100000000000000000000000000000 : ℝ)*base71 + (25087703796783/50000000000000000000000000000 : ℝ)*base73 + (395987177696783/100000000000000000000000000000 : ℝ)*base75 + (349883957696783/100000000000000000000000000000 : ℝ)*base77 + (601400045496783/100000000000000000000000000000 : ℝ)*base79 + (195487501503217/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (4067517/2500000000000000000000 : ℝ)*base89 + (4067517/2500000000000000000000 : ℝ)*base91 + (4067517/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (95176685667254366415489/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1686939261/100000000000000 : ℝ)*(base19) + (1709786227/100000000000000 : ℝ)*(base23) + (35897539/25000000000000 : ℝ)*(base32) + (126753/50000000000 : ℝ)*(upper3) + (162648541/100000000000000 : ℝ)*(upper5) + (175647783929879/25000000000000 : ℝ)*(major0) + (175647783929879/25000000000000 : ℝ)*(major1) + (175647783929879/25000000000000 : ℝ)*(major2) + (4178552061/100000000000000 : ℝ)*(sp1) + (4384802903/100000000000000 : ℝ)*(sp2) + (484915308348559/50000000000000 : ℝ)*(sp4) + (242456187801449/25000000000000 : ℝ)*(sp5) + (969824522107989/100000000000000 : ℝ)*(sp6) + (87070251469451/20000000000000 : ℝ)*(sp7) + (435351400937411/100000000000000 : ℝ)*(f.failure) + (484915308348559/50000000000000 : ℝ)*(f.sum) + (1722388985779/12500000000000000000000000000 : ℝ)*base65 + (46483273235779/25000000000000000000000000000 : ℝ)*base67 + (178397320135779/25000000000000000000000000000 : ℝ)*base69 + (210994917010779/25000000000000000000000000000 : ℝ)*base71 + (13365374189221/12500000000000000000000000000 : ℝ)*base74 + (49023669760779/25000000000000000000000000000 : ℝ)*base75 + (54837013835779/25000000000000000000000000000 : ℝ)*base77 + (44915133964221/25000000000000000000000000000 : ℝ)*base80 + (44906621548279/12500000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (40687613/5000000000000000000000 : ℝ)*base90 + (40687613/5000000000000000000000 : ℝ)*base92 + (40687613/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1487_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80692417/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1/40 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6453/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1487_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1487_s1_0 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-936578409/5000000000 : ℝ)*x 0 + (2793857347/5000000000 : ℝ)*x 1 + (5086065897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (936578409/5000000000 : ℝ)^4471 ≤ (5694397787811/50000000000000 : ℝ)^3447 := by
    have hnat : (936578409 : ℕ)^4471*50000000000000^3447 ≤ 5694397787811^3447*5000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      936578409 5000000000 5694397787811 50000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2793857347/5000000000 : ℝ)^4471 ≤ (47005114516979/100000000000000 : ℝ)^3447 := by
    have hnat : (2793857347 : ℕ)^4471*100000000000000^3447 ≤ 47005114516979^3447*5000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2793857347 5000000000 47005114516979 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5086065897/10000000000 : ℝ)^4471 ≤ (2600380618421/6250000000000 : ℝ)^3447 := by
    have hnat : (5086065897 : ℕ)^4471*6250000000000^3447 ≤ 2600380618421^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5086065897 10000000000 2600380618421 6250000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-936578409/5000000000 : ℝ), (2793857347/5000000000 : ℝ), (5086065897/10000000000 : ℝ)] ![(5694397787811/50000000000000 : ℝ), (47005114516979/100000000000000 : ℝ), (2600380618421/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-936578409/5000000000 : ℝ)|^4471 ≤ (5694397787811/50000000000000 : ℝ)^3447
        have hw : |(-936578409/5000000000 : ℝ)|=(936578409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2793857347/5000000000 : ℝ)|^4471 ≤ (47005114516979/100000000000000 : ℝ)^3447
        have hw : |(2793857347/5000000000 : ℝ)|=(2793857347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5086065897/10000000000 : ℝ)|^4471 ≤ (2600380618421/6250000000000 : ℝ)^3447
        have hw : |(5086065897/10000000000 : ℝ)|=(5086065897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_s1_1 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1078248901/2000000000 : ℝ)*x 0 + (-534539701/2500000000 : ℝ)*x 1 + (635758803/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078248901/2000000000 : ℝ)^4471 ≤ (44872669918533/100000000000000 : ℝ)^3447 := by
    have hnat : (1078248901 : ℕ)^4471*100000000000000^3447 ≤ 44872669918533^3447*2000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078248901 2000000000 44872669918533 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (534539701/2500000000 : ℝ)^4471 ≤ (3380298035323/25000000000000 : ℝ)^3447 := by
    have hnat : (534539701 : ℕ)^4471*25000000000000^3447 ≤ 3380298035323^3447*2500000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534539701 2500000000 3380298035323 25000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (635758803/1250000000 : ℝ)^4471 ≤ (41606137928747/100000000000000 : ℝ)^3447 := by
    have hnat : (635758803 : ℕ)^4471*100000000000000^3447 ≤ 41606137928747^3447*1250000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      635758803 1250000000 41606137928747 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1078248901/2000000000 : ℝ), (-534539701/2500000000 : ℝ), (635758803/1250000000 : ℝ)] ![(44872669918533/100000000000000 : ℝ), (3380298035323/25000000000000 : ℝ), (41606137928747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1078248901/2000000000 : ℝ)|^4471 ≤ (44872669918533/100000000000000 : ℝ)^3447
        have hw : |(1078248901/2000000000 : ℝ)|=(1078248901/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-534539701/2500000000 : ℝ)|^4471 ≤ (3380298035323/25000000000000 : ℝ)^3447
        have hw : |(-534539701/2500000000 : ℝ)|=(534539701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(635758803/1250000000 : ℝ)|^4471 ≤ (41606137928747/100000000000000 : ℝ)^3447
        have hw : |(635758803/1250000000 : ℝ)|=(635758803/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_s1_2 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5391247761/10000000000 : ℝ)*x 0 + (1017213317/2000000000 : ℝ)*x 1 + (-2138159483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5391247761/10000000000 : ℝ)^4471 ≤ (22436352534889/50000000000000 : ℝ)^3447 := by
    have hnat : (5391247761 : ℕ)^4471*50000000000000^3447 ≤ 22436352534889^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391247761 10000000000 22436352534889 50000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1017213317/2000000000 : ℝ)^4471 ≤ (41606097194801/100000000000000 : ℝ)^3447 := by
    have hnat : (1017213317 : ℕ)^4471*100000000000000^3447 ≤ 41606097194801^3447*2000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1017213317 2000000000 41606097194801 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2138159483/10000000000 : ℝ)^4471 ≤ (1352119771069/10000000000000 : ℝ)^3447 := by
    have hnat : (2138159483 : ℕ)^4471*10000000000000^3447 ≤ 1352119771069^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138159483 10000000000 1352119771069 10000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5391247761/10000000000 : ℝ), (1017213317/2000000000 : ℝ), (-2138159483/10000000000 : ℝ)] ![(22436352534889/50000000000000 : ℝ), (41606097194801/100000000000000 : ℝ), (1352119771069/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5391247761/10000000000 : ℝ)|^4471 ≤ (22436352534889/50000000000000 : ℝ)^3447
        have hw : |(5391247761/10000000000 : ℝ)|=(5391247761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1017213317/2000000000 : ℝ)|^4471 ≤ (41606097194801/100000000000000 : ℝ)^3447
        have hw : |(1017213317/2000000000 : ℝ)|=(1017213317/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2138159483/10000000000 : ℝ)|^4471 ≤ (1352119771069/10000000000000 : ℝ)^3447
        have hw : |(-2138159483/10000000000 : ℝ)|=(2138159483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_s1_3 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4258717757/10000000000 : ℝ)*x 0 + (3731557631/10000000000 : ℝ)*x 1 + (4849068319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4258717757/10000000000 : ℝ)^4471 ≤ (16524136145161/50000000000000 : ℝ)^3447 := by
    have hnat : (4258717757 : ℕ)^4471*50000000000000^3447 ≤ 16524136145161^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4258717757 10000000000 16524136145161 50000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3731557631/10000000000 : ℝ)^4471 ≤ (27842715979303/100000000000000 : ℝ)^3447 := by
    have hnat : (3731557631 : ℕ)^4471*100000000000000^3447 ≤ 27842715979303^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3731557631 10000000000 27842715979303 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4849068319/10000000000 : ℝ)^4471 ≤ (4888626464613/12500000000000 : ℝ)^3447 := by
    have hnat : (4849068319 : ℕ)^4471*12500000000000^3447 ≤ 4888626464613^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4849068319 10000000000 4888626464613 12500000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4258717757/10000000000 : ℝ), (3731557631/10000000000 : ℝ), (4849068319/10000000000 : ℝ)] ![(16524136145161/50000000000000 : ℝ), (27842715979303/100000000000000 : ℝ), (4888626464613/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4258717757/10000000000 : ℝ)|^4471 ≤ (16524136145161/50000000000000 : ℝ)^3447
        have hw : |(4258717757/10000000000 : ℝ)|=(4258717757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3731557631/10000000000 : ℝ)|^4471 ≤ (27842715979303/100000000000000 : ℝ)^3447
        have hw : |(3731557631/10000000000 : ℝ)|=(3731557631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4849068319/10000000000 : ℝ)|^4471 ≤ (4888626464613/12500000000000 : ℝ)^3447
        have hw : |(4849068319/10000000000 : ℝ)|=(4849068319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_s1_4 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1873510051/10000000000 : ℝ)*x 0 + (5091879951/10000000000 : ℝ)*x 1 + (5581803661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1873510051/10000000000 : ℝ)^4471 ≤ (5695790657491/50000000000000 : ℝ)^3447 := by
    have hnat : (1873510051 : ℕ)^4471*50000000000000^3447 ≤ 5695790657491^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1873510051 10000000000 5695790657491 50000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5091879951/10000000000 : ℝ)^4471 ≤ (5208473841957/12500000000000 : ℝ)^3447 := by
    have hnat : (5091879951 : ℕ)^4471*12500000000000^3447 ≤ 5208473841957^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5091879951 10000000000 5208473841957 12500000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5581803661/10000000000 : ℝ)^4471 ≤ (46940627928887/100000000000000 : ℝ)^3447 := by
    have hnat : (5581803661 : ℕ)^4471*100000000000000^3447 ≤ 46940627928887^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5581803661 10000000000 46940627928887 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1873510051/10000000000 : ℝ), (5091879951/10000000000 : ℝ), (5581803661/10000000000 : ℝ)] ![(5695790657491/50000000000000 : ℝ), (5208473841957/12500000000000 : ℝ), (46940627928887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1873510051/10000000000 : ℝ)|^4471 ≤ (5695790657491/50000000000000 : ℝ)^3447
        have hw : |(-1873510051/10000000000 : ℝ)|=(1873510051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5091879951/10000000000 : ℝ)|^4471 ≤ (5208473841957/12500000000000 : ℝ)^3447
        have hw : |(5091879951/10000000000 : ℝ)|=(5091879951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5581803661/10000000000 : ℝ)|^4471 ≤ (46940627928887/100000000000000 : ℝ)^3447
        have hw : |(5581803661/10000000000 : ℝ)|=(5581803661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_s1_5 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1314881963/2500000000 : ℝ)*x 0 + (-328484857/2000000000 : ℝ)*x 1 + (1395450931/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314881963/2500000000 : ℝ)^4471 ≤ (5431983593281/12500000000000 : ℝ)^3447 := by
    have hnat : (1314881963 : ℕ)^4471*12500000000000^3447 ≤ 5431983593281^3447*2500000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314881963 2500000000 5431983593281 12500000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (328484857/2000000000 : ℝ)^4471 ≤ (9603502620033/100000000000000 : ℝ)^3447 := by
    have hnat : (328484857 : ℕ)^4471*100000000000000^3447 ≤ 9603502620033^3447*2000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328484857 2000000000 9603502620033 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1395450931/2500000000 : ℝ)^4471 ≤ (586757857701/1250000000000 : ℝ)^3447 := by
    have hnat : (1395450931 : ℕ)^4471*1250000000000^3447 ≤ 586757857701^3447*2500000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1395450931 2500000000 586757857701 1250000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314881963/2500000000 : ℝ), (-328484857/2000000000 : ℝ), (1395450931/2500000000 : ℝ)] ![(5431983593281/12500000000000 : ℝ), (9603502620033/100000000000000 : ℝ), (586757857701/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314881963/2500000000 : ℝ)|^4471 ≤ (5431983593281/12500000000000 : ℝ)^3447
        have hw : |(1314881963/2500000000 : ℝ)|=(1314881963/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-328484857/2000000000 : ℝ)|^4471 ≤ (9603502620033/100000000000000 : ℝ)^3447
        have hw : |(-328484857/2000000000 : ℝ)|=(328484857/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1395450931/2500000000 : ℝ)|^4471 ≤ (586757857701/1250000000000 : ℝ)^3447
        have hw : |(1395450931/2500000000 : ℝ)|=(1395450931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_s1_6 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1314881959/2500000000 : ℝ)*x 0 + (1395450927/2500000000 : ℝ)*x 1 + (-1642424331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314881959/2500000000 : ℝ)^4471 ≤ (43455868574779/100000000000000 : ℝ)^3447 := by
    have hnat : (1314881959 : ℕ)^4471*100000000000000^3447 ≤ 43455868574779^3447*2500000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314881959 2500000000 43455868574779 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1395450927/2500000000 : ℝ)^4471 ≤ (23470314220777/50000000000000 : ℝ)^3447 := by
    have hnat : (1395450927 : ℕ)^4471*50000000000000^3447 ≤ 23470314220777^3447*2500000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1395450927 2500000000 23470314220777 50000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1642424331/10000000000 : ℝ)^4471 ≤ (1200437871113/12500000000000 : ℝ)^3447 := by
    have hnat : (1642424331 : ℕ)^4471*12500000000000^3447 ≤ 1200437871113^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1642424331 10000000000 1200437871113 12500000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314881959/2500000000 : ℝ), (1395450927/2500000000 : ℝ), (-1642424331/10000000000 : ℝ)] ![(43455868574779/100000000000000 : ℝ), (23470314220777/50000000000000 : ℝ), (1200437871113/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314881959/2500000000 : ℝ)|^4471 ≤ (43455868574779/100000000000000 : ℝ)^3447
        have hw : |(1314881959/2500000000 : ℝ)|=(1314881959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1395450927/2500000000 : ℝ)|^4471 ≤ (23470314220777/50000000000000 : ℝ)^3447
        have hw : |(1395450927/2500000000 : ℝ)|=(1395450927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1642424331/10000000000 : ℝ)|^4471 ≤ (1200437871113/12500000000000 : ℝ)^3447
        have hw : |(-1642424331/10000000000 : ℝ)|=(1642424331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_s1_7 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4259507693/10000000000 : ℝ)*x 0 + (1209030227/2500000000 : ℝ)*x 1 + (234044927/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4259507693/10000000000 : ℝ)^4471 ≤ (4132027946547/12500000000000 : ℝ)^3447 := by
    have hnat : (4259507693 : ℕ)^4471*12500000000000^3447 ≤ 4132027946547^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4259507693 10000000000 4132027946547 12500000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1209030227/2500000000 : ℝ)^4471 ≤ (38973619881453/100000000000000 : ℝ)^3447 := by
    have hnat : (1209030227 : ℕ)^4471*100000000000000^3447 ≤ 38973619881453^3447*2500000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1209030227 2500000000 38973619881453 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (234044927/625000000 : ℝ)^4471 ≤ (874067391423/3125000000000 : ℝ)^3447 := by
    have hnat : (234044927 : ℕ)^4471*3125000000000^3447 ≤ 874067391423^3447*625000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234044927 625000000 874067391423 3125000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4259507693/10000000000 : ℝ), (1209030227/2500000000 : ℝ), (234044927/625000000 : ℝ)] ![(4132027946547/12500000000000 : ℝ), (38973619881453/100000000000000 : ℝ), (874067391423/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4259507693/10000000000 : ℝ)|^4471 ≤ (4132027946547/12500000000000 : ℝ)^3447
        have hw : |(4259507693/10000000000 : ℝ)|=(4259507693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1209030227/2500000000 : ℝ)|^4471 ≤ (38973619881453/100000000000000 : ℝ)^3447
        have hw : |(1209030227/2500000000 : ℝ)|=(1209030227/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(234044927/625000000 : ℝ)|^4471 ≤ (874067391423/3125000000000 : ℝ)^3447
        have hw : |(234044927/625000000 : ℝ)|=(234044927/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1487_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80692417/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6453/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1/40 : ℝ)*pair X i i ≤ pair X i h) :
    (1001/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9307/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6453/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1/40 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6453/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1/40 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6453/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1/40 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6453/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1/40 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6453/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1/40 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6453/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1/40 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1/40 : ℝ) ^ (4469/1024 : ℝ) ≤ (10190539266321/100000000000000000000 : ℝ) := by
    have hpowers : (1/40 : ℝ)^4469 ≤ (10190539266321/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1 : ℕ)^4469*100000000000000000000^1024 ≤ 10190539266321^1024*40^4469 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 40 10190539266321 100000000000000000000 4469 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1/40 : ℝ)) (X := (10190539266321/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4469 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (6453/25000 : ℝ) ^ (4469/1024 : ℝ) ≤ (271042920958447679/100000000000000000000 : ℝ) := by
    have hpowers : (6453/25000 : ℝ)^4469 ≤ (271042920958447679/100000000000000000000 : ℝ)^1024 := by
      have hnat : (6453 : ℕ)^4469*100000000000000000000^1024 ≤ 271042920958447679^1024*25000^4469 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6453 25000 271042920958447679 100000000000000000000 4469 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6453/25000 : ℝ)) (X := (271042920958447679/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4469 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000010190539266321/50000000000000000000 : ℝ) ≤ (10000000466999839/10000000000000000 : ℝ) ^ (4469/1024 : ℝ) := by
    have hpowers : (50000010190539266321/50000000000000000000 : ℝ)^1024 ≤ (10000000466999839/10000000000000000 : ℝ)^4469 := by
      have hnat : (50000010190539266321 : ℕ)^1024*10000000000000000^4469 ≤ 10000000466999839^4469*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000010190539266321 50000000000000000000 10000000466999839 10000000000000000 1024 4469 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000466999839/10000000000000000 : ℝ)) (X := (50000010190539266321/50000000000000000000 : ℝ)) (by norm_num) 4469 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50135526555748857/50000000000000000 : ℝ) ≤ (10006204271116953/10000000000000000 : ℝ) ^ (4469/1024 : ℝ) := by
    have hpowers : (50135526555748857/50000000000000000 : ℝ)^1024 ≤ (10006204271116953/10000000000000000 : ℝ)^4469 := by
      have hnat : (50135526555748857 : ℕ)^1024*10000000000000000^4469 ≤ 10006204271116953^4469*50000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50135526555748857 50000000000000000 10006204271116953 10000000000000000 1024 4469 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006204271116953/10000000000000000 : ℝ)) (X := (50135526555748857/50000000000000000 : ℝ)) (by norm_num) 4469 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50271042920958447679/50000000000000000000 : ℝ) ≤ (10012408075234067/10000000000000000 : ℝ) ^ (4469/1024 : ℝ) := by
    have hpowers : (50271042920958447679/50000000000000000000 : ℝ)^1024 ≤ (10012408075234067/10000000000000000 : ℝ)^4469 := by
      have hnat : (50271042920958447679 : ℕ)^1024*10000000000000000^4469 ≤ 10012408075234067^4469*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50271042920958447679 50000000000000000000 10012408075234067 10000000000000000 1024 4469 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10012408075234067/10000000000000000 : ℝ)) (X := (50271042920958447679/50000000000000000000 : ℝ)) (by norm_num) 4469 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10190539266321/100000000000000000000 : ℝ) ≤ ((7284030995816083649/7285000000000000000 : ℝ)+2*(3101902058557/1165600000000000 : ℝ)*(1/40 : ℝ))^(4469/1024 : ℝ) := by
    rw [show (7284030995816083649/7285000000000000000 : ℝ)+2*(3101902058557/1165600000000000 : ℝ)*(1/40 : ℝ)=(10000000466999839/10000000000000000 : ℝ) by norm_num, show 1+2*(10190539266321/100000000000000000000 : ℝ)=(50000010190539266321/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(271042920958447679/100000000000000000000 : ℝ)+(10190539266321/100000000000000000000 : ℝ) ≤ ((7284030995816083649/7285000000000000000 : ℝ)+(3101902058557/1165600000000000 : ℝ)*((6453/25000 : ℝ)+(1/40 : ℝ)))^(4469/1024 : ℝ) := by
    rw [show (7284030995816083649/7285000000000000000 : ℝ)+(3101902058557/1165600000000000 : ℝ)*((6453/25000 : ℝ)+(1/40 : ℝ))=(10006204271116953/10000000000000000 : ℝ) by norm_num, show 1+(271042920958447679/100000000000000000000 : ℝ)+(10190539266321/100000000000000000000 : ℝ)=(50135526555748857/50000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(271042920958447679/100000000000000000000 : ℝ) ≤ ((7284030995816083649/7285000000000000000 : ℝ)+2*(3101902058557/1165600000000000 : ℝ)*(6453/25000 : ℝ))^(4469/1024 : ℝ) := by
    rw [show (7284030995816083649/7285000000000000000 : ℝ)+2*(3101902058557/1165600000000000 : ℝ)*(6453/25000 : ℝ)=(10012408075234067/10000000000000000 : ℝ) by norm_num, show 1+2*(271042920958447679/100000000000000000000 : ℝ)=(50271042920958447679/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7284030995816083649/7285000000000000000 : ℝ)*(X 1 0+X 2 0)+(3101902058557/1165600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4469/1024 : ℝ)) (lo := (1/40 : ℝ)) (hi := (6453/25000 : ℝ)) (c := (7284030995816083649/7285000000000000000 : ℝ)) (alpha := (3101902058557/1165600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7284030995816083649/7285000000000000000 : ℝ)*(X 0 1+X 2 1)+(3101902058557/1165600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4469/1024 : ℝ)) (lo := (1/40 : ℝ)) (hi := (6453/25000 : ℝ)) (c := (7284030995816083649/7285000000000000000 : ℝ)) (alpha := (3101902058557/1165600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7284030995816083649/7285000000000000000 : ℝ)*(X 0 2+X 1 2)+(3101902058557/1165600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4469/1024 : ℝ)) (lo := (1/40 : ℝ)) (hi := (6453/25000 : ℝ)) (c := (7284030995816083649/7285000000000000000 : ℝ)) (alpha := (3101902058557/1165600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-936578409/5000000000 : ℝ)*X 0 0+(2793857347/5000000000 : ℝ)*X 0 1+(5086065897/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1078248901/2000000000 : ℝ)*X 1 0+(-534539701/2500000000 : ℝ)*X 1 1+(635758803/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5391247761/10000000000 : ℝ)*X 2 0+(1017213317/2000000000 : ℝ)*X 2 1+(-2138159483/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4258717757/10000000000 : ℝ)*X 0 0+(3731557631/10000000000 : ℝ)*X 0 1+(4849068319/10000000000 : ℝ)*X 0 2+(4258717757/10000000000 : ℝ)*X 1 0+(3731557631/10000000000 : ℝ)*X 1 1+(4849068319/10000000000 : ℝ)*X 1 2+(4258717757/10000000000 : ℝ)*X 2 0+(3731557631/10000000000 : ℝ)*X 2 1+(4849068319/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1873510051/10000000000 : ℝ)*X 0 0+(5091879951/10000000000 : ℝ)*X 0 1+(5581803661/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1314881963/2500000000 : ℝ)*X 1 0+(-328484857/2000000000 : ℝ)*X 1 1+(1395450931/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1314881959/2500000000 : ℝ)*X 2 0+(1395450927/2500000000 : ℝ)*X 2 1+(-1642424331/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4259507693/10000000000 : ℝ)*X 0 0+(1209030227/2500000000 : ℝ)*X 0 1+(234044927/625000000 : ℝ)*X 0 2+(4259507693/10000000000 : ℝ)*X 1 0+(1209030227/2500000000 : ℝ)*X 1 1+(234044927/625000000 : ℝ)*X 1 2+(4259507693/10000000000 : ℝ)*X 2 0+(1209030227/2500000000 : ℝ)*X 2 1+(234044927/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8352328065674110770021327/1821250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (128524431/50000000000000 : ℝ)*(base19) + (379843073/25000000000000 : ℝ)*(base23) + (35460977/25000000000000 : ℝ)*(upper2) + (25030821/100000000000000 : ℝ)*(upper3) + (22073181/20000000000000 : ℝ)*(upper4) + (7220796784597/500000000000 : ℝ)*(major0) + (7220796784597/500000000000 : ℝ)*(major1) + (7220796784597/500000000000 : ℝ)*(major2) + (996721935605661/50000000000000 : ℝ)*(sp0) + (996731930602767/50000000000000 : ℝ)*(sp1) + (249182824860263/12500000000000 : ℝ)*(sp2) + (55928091438183/6250000000000 : ℝ)*(sp3) + (10123521537/50000000000000 : ℝ)*(sp4) + (4979705419/100000000000000 : ℝ)*(sp7) + (447427221358173/50000000000000 : ℝ)*(f.failure) + (498366029563599/25000000000000 : ℝ)*(f.sum) + (159339823809/91062500000000000000000000 : ℝ)*base65 + (37209357117274297/3642500000000000000000000000000 : ℝ)*base68 + (50957439835729297/3642500000000000000000000000000 : ℝ)*base70 + (26415393611391797/3642500000000000000000000000000 : ℝ)*base72 + (5573431053943/1457000000000000000000000000 : ℝ)*base74 + (42507374073919297/3642500000000000000000000000000 : ℝ)*base76 + (13447650952936797/3642500000000000000000000000000 : ℝ)*base78 + (53441502709989297/3642500000000000000000000000000 : ℝ)*base80 + (7387072197811/1457000000000000000000000000 : ℝ)*base82 + (2074141/2500000000000000000000 : ℝ)*base89 + (2074141/2500000000000000000000 : ℝ)*base91 + (2074141/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (58123533194685831886521303/7285000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1528483937/100000000000000 : ℝ)*(base19) + (324415487/20000000000000 : ℝ)*(base23) + (53339477/25000000000000 : ℝ)*(upper3) + (41138083/100000000000000 : ℝ)*(lower4) + (78103041/50000000000000 : ℝ)*(upper5) + (29573861090751/2000000000000 : ℝ)*(major0) + (29573861090751/2000000000000 : ℝ)*(major1) + (29573861090751/2000000000000 : ℝ)*(major2) + (299313811/3125000000000 : ℝ)*(sp1) + (10439745609/100000000000000 : ℝ)*(sp2) + (1020566523347603/50000000000000 : ℝ)*(sp4) + (2041121940169317/100000000000000 : ℝ)*(sp5) + (1020560492436081/50000000000000 : ℝ)*(sp6) + (183250559285831/20000000000000 : ℝ)*(sp7) + (183250559285831/20000000000000 : ℝ)*(f.failure) + (1020566523347603/50000000000000 : ℝ)*(f.sum) + (3231547589883/5828000000000000000000000000 : ℝ)*base65 + (62778453108429149/14570000000000000000000000000000 : ℝ)*base67 + (45476770445170851/14570000000000000000000000000000 : ℝ)*base70 + (18443507737019149/14570000000000000000000000000000 : ℝ)*base71 + (12812837415299/5828000000000000000000000000 : ℝ)*base73 + (14003579150529149/14570000000000000000000000000000 : ℝ)*base75 + (45623230257929149/14570000000000000000000000000000 : ℝ)*base77 + (44365495782920851/14570000000000000000000000000000 : ℝ)*base80 + (28359355345613/5828000000000000000000000000 : ℝ)*base82 + (2756473/1000000000000000000000 : ℝ)*base90 + (2756473/1000000000000000000000 : ℝ)*base92 + (2756473/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1487_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80692417/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6453/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1/40 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1001/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9307/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1487_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1487_s2_0 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-475174829/2500000000 : ℝ)*x 0 + (1366594403/2500000000 : ℝ)*x 1 + (1297402519/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (475174829/2500000000 : ℝ)^4471 ≤ (11606473610953/100000000000000 : ℝ)^3447 := by
    have hnat : (475174829 : ℕ)^4471*100000000000000^3447 ≤ 11606473610953^3447*2500000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      475174829 2500000000 11606473610953 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1366594403/2500000000 : ℝ)^4471 ≤ (22842734090887/50000000000000 : ℝ)^3447 := by
    have hnat : (1366594403 : ℕ)^4471*50000000000000^3447 ≤ 22842734090887^3447*2500000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366594403 2500000000 22842734090887 50000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1297402519/2500000000 : ℝ)^4471 ≤ (854161163819/2000000000000 : ℝ)^3447 := by
    have hnat : (1297402519 : ℕ)^4471*2000000000000^3447 ≤ 854161163819^3447*2500000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1297402519 2500000000 854161163819 2000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-475174829/2500000000 : ℝ), (1366594403/2500000000 : ℝ), (1297402519/2500000000 : ℝ)] ![(11606473610953/100000000000000 : ℝ), (22842734090887/50000000000000 : ℝ), (854161163819/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-475174829/2500000000 : ℝ)|^4471 ≤ (11606473610953/100000000000000 : ℝ)^3447
        have hw : |(-475174829/2500000000 : ℝ)|=(475174829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1366594403/2500000000 : ℝ)|^4471 ≤ (22842734090887/50000000000000 : ℝ)^3447
        have hw : |(1366594403/2500000000 : ℝ)|=(1366594403/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1297402519/2500000000 : ℝ)|^4471 ≤ (854161163819/2000000000000 : ℝ)^3447
        have hw : |(1297402519/2500000000 : ℝ)|=(1297402519/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_s2_1 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1072133021/2000000000 : ℝ)*x 0 + (-408680101/2000000000 : ℝ)*x 1 + (648701281/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072133021/2000000000 : ℝ)^4471 ≤ (22271409121501/50000000000000 : ℝ)^3447 := by
    have hnat : (1072133021 : ℕ)^4471*50000000000000^3447 ≤ 22271409121501^3447*2000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072133021 2000000000 22271409121501 50000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (408680101/2000000000 : ℝ)^4471 ≤ (3187280430531/25000000000000 : ℝ)^3447 := by
    have hnat : (408680101 : ℕ)^4471*25000000000000^3447 ≤ 3187280430531^3447*2000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408680101 2000000000 3187280430531 25000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (648701281/1250000000 : ℝ)^4471 ≤ (21354030013463/50000000000000 : ℝ)^3447 := by
    have hnat : (648701281 : ℕ)^4471*50000000000000^3447 ≤ 21354030013463^3447*1250000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      648701281 1250000000 21354030013463 50000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072133021/2000000000 : ℝ), (-408680101/2000000000 : ℝ), (648701281/1250000000 : ℝ)] ![(22271409121501/50000000000000 : ℝ), (3187280430531/25000000000000 : ℝ), (21354030013463/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072133021/2000000000 : ℝ)|^4471 ≤ (22271409121501/50000000000000 : ℝ)^3447
        have hw : |(1072133021/2000000000 : ℝ)|=(1072133021/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-408680101/2000000000 : ℝ)|^4471 ≤ (3187280430531/25000000000000 : ℝ)^3447
        have hw : |(-408680101/2000000000 : ℝ)|=(408680101/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(648701281/1250000000 : ℝ)|^4471 ≤ (21354030013463/50000000000000 : ℝ)^3447
        have hw : |(648701281/1250000000 : ℝ)|=(648701281/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_s2_2 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5360665311/10000000000 : ℝ)*x 0 + (5189610149/10000000000 : ℝ)*x 1 + (-51085009/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5360665311/10000000000 : ℝ)^4471 ≤ (4454282046319/10000000000000 : ℝ)^3447 := by
    have hnat : (5360665311 : ℕ)^4471*10000000000000^3447 ≤ 4454282046319^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5360665311 10000000000 4454282046319 10000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5189610149/10000000000 : ℝ)^4471 ≤ (10677014742543/25000000000000 : ℝ)^3447 := by
    have hnat : (5189610149 : ℕ)^4471*25000000000000^3447 ≤ 10677014742543^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5189610149 10000000000 10677014742543 25000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51085009/250000000 : ℝ)^4471 ≤ (12749120548691/100000000000000 : ℝ)^3447 := by
    have hnat : (51085009 : ℕ)^4471*100000000000000^3447 ≤ 12749120548691^3447*250000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51085009 250000000 12749120548691 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5360665311/10000000000 : ℝ), (5189610149/10000000000 : ℝ), (-51085009/250000000 : ℝ)] ![(4454282046319/10000000000000 : ℝ), (10677014742543/25000000000000 : ℝ), (12749120548691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5360665311/10000000000 : ℝ)|^4471 ≤ (4454282046319/10000000000000 : ℝ)^3447
        have hw : |(5360665311/10000000000 : ℝ)|=(5360665311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5189610149/10000000000 : ℝ)|^4471 ≤ (10677014742543/25000000000000 : ℝ)^3447
        have hw : |(5189610149/10000000000 : ℝ)|=(5189610149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-51085009/250000000 : ℝ)|^4471 ≤ (12749120548691/100000000000000 : ℝ)^3447
        have hw : |(-51085009/250000000 : ℝ)|=(51085009/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_s2_3 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4278402331/10000000000 : ℝ)*x 0 + (1989871073/5000000000 : ℝ)*x 1 + (91925939/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4278402331/10000000000 : ℝ)^4471 ≤ (16623271155457/50000000000000 : ℝ)^3447 := by
    have hnat : (4278402331 : ℕ)^4471*50000000000000^3447 ≤ 16623271155457^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4278402331 10000000000 16623271155457 50000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1989871073/5000000000 : ℝ)^4471 ≤ (30268010318153/100000000000000 : ℝ)^3447 := by
    have hnat : (1989871073 : ℕ)^4471*100000000000000^3447 ≤ 30268010318153^3447*5000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989871073 5000000000 30268010318153 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (91925939/200000000 : ℝ)^4471 ≤ (18242723676687/50000000000000 : ℝ)^3447 := by
    have hnat : (91925939 : ℕ)^4471*50000000000000^3447 ≤ 18242723676687^3447*200000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91925939 200000000 18242723676687 50000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4278402331/10000000000 : ℝ), (1989871073/5000000000 : ℝ), (91925939/200000000 : ℝ)] ![(16623271155457/50000000000000 : ℝ), (30268010318153/100000000000000 : ℝ), (18242723676687/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4278402331/10000000000 : ℝ)|^4471 ≤ (16623271155457/50000000000000 : ℝ)^3447
        have hw : |(4278402331/10000000000 : ℝ)|=(4278402331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1989871073/5000000000 : ℝ)|^4471 ≤ (30268010318153/100000000000000 : ℝ)^3447
        have hw : |(1989871073/5000000000 : ℝ)|=(1989871073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(91925939/200000000 : ℝ)|^4471 ≤ (18242723676687/50000000000000 : ℝ)^3447
        have hw : |(91925939/200000000 : ℝ)|=(91925939/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_s2_4 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1900758929/10000000000 : ℝ)*x 0 + (1297847047/2500000000 : ℝ)*x 1 + (2732291501/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1900758929/10000000000 : ℝ)^4471 ≤ (11606945775373/100000000000000 : ℝ)^3447 := by
    have hnat : (1900758929 : ℕ)^4471*100000000000000^3447 ≤ 11606945775373^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1900758929 10000000000 11606945775373 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1297847047/2500000000 : ℝ)^4471 ≤ (21363519608757/50000000000000 : ℝ)^3447 := by
    have hnat : (1297847047 : ℕ)^4471*50000000000000^3447 ≤ 21363519608757^3447*2500000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1297847047 2500000000 21363519608757 50000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2732291501/5000000000 : ℝ)^4471 ≤ (178382871077/390625000000 : ℝ)^3447 := by
    have hnat : (2732291501 : ℕ)^4471*390625000000^3447 ≤ 178382871077^3447*5000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732291501 5000000000 178382871077 390625000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1900758929/10000000000 : ℝ), (1297847047/2500000000 : ℝ), (2732291501/5000000000 : ℝ)] ![(11606945775373/100000000000000 : ℝ), (21363519608757/50000000000000 : ℝ), (178382871077/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1900758929/10000000000 : ℝ)|^4471 ≤ (11606945775373/100000000000000 : ℝ)^3447
        have hw : |(-1900758929/10000000000 : ℝ)|=(1900758929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1297847047/2500000000 : ℝ)|^4471 ≤ (21363519608757/50000000000000 : ℝ)^3447
        have hw : |(1297847047/2500000000 : ℝ)|=(1297847047/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2732291501/5000000000 : ℝ)|^4471 ≤ (178382871077/390625000000 : ℝ)^3447
        have hw : |(2732291501/5000000000 : ℝ)|=(2732291501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_s2_5 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1322067719/2500000000 : ℝ)*x 0 + (-1768427747/10000000000 : ℝ)*x 1 + (5464582979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322067719/2500000000 : ℝ)^4471 ≤ (21882075831863/50000000000000 : ℝ)^3447 := by
    have hnat : (1322067719 : ℕ)^4471*50000000000000^3447 ≤ 21882075831863^3447*2500000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322067719 2500000000 21882075831863 50000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1768427747/10000000000 : ℝ)^4471 ≤ (10569833569537/100000000000000 : ℝ)^3447 := by
    have hnat : (1768427747 : ℕ)^4471*100000000000000^3447 ≤ 10569833569537^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1768427747 10000000000 10569833569537 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5464582979/10000000000 : ℝ)^4471 ≤ (45666014746409/100000000000000 : ℝ)^3447 := by
    have hnat : (5464582979 : ℕ)^4471*100000000000000^3447 ≤ 45666014746409^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5464582979 10000000000 45666014746409 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322067719/2500000000 : ℝ), (-1768427747/10000000000 : ℝ), (5464582979/10000000000 : ℝ)] ![(21882075831863/50000000000000 : ℝ), (10569833569537/100000000000000 : ℝ), (45666014746409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322067719/2500000000 : ℝ)|^4471 ≤ (21882075831863/50000000000000 : ℝ)^3447
        have hw : |(1322067719/2500000000 : ℝ)|=(1322067719/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1768427747/10000000000 : ℝ)|^4471 ≤ (10569833569537/100000000000000 : ℝ)^3447
        have hw : |(-1768427747/10000000000 : ℝ)|=(1768427747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5464582979/10000000000 : ℝ)|^4471 ≤ (45666014746409/100000000000000 : ℝ)^3447
        have hw : |(5464582979/10000000000 : ℝ)|=(5464582979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_s2_6 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5288271081/10000000000 : ℝ)*x 0 + (1092916601/2000000000 : ℝ)*x 1 + (-1768427427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288271081/10000000000 : ℝ)^4471 ≤ (43764153864229/100000000000000 : ℝ)^3447 := by
    have hnat : (5288271081 : ℕ)^4471*100000000000000^3447 ≤ 43764153864229^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288271081 10000000000 43764153864229 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1092916601/2000000000 : ℝ)^4471 ≤ (45666015028229/100000000000000 : ℝ)^3447 := by
    have hnat : (1092916601 : ℕ)^4471*100000000000000^3447 ≤ 45666015028229^3447*2000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092916601 2000000000 45666015028229 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1768427427/10000000000 : ℝ)^4471 ≤ (10569831088723/100000000000000 : ℝ)^3447 := by
    have hnat : (1768427427 : ℕ)^4471*100000000000000^3447 ≤ 10569831088723^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1768427427 10000000000 10569831088723 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288271081/10000000000 : ℝ), (1092916601/2000000000 : ℝ), (-1768427427/10000000000 : ℝ)] ![(43764153864229/100000000000000 : ℝ), (45666015028229/100000000000000 : ℝ), (10569831088723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288271081/10000000000 : ℝ)|^4471 ≤ (43764153864229/100000000000000 : ℝ)^3447
        have hw : |(5288271081/10000000000 : ℝ)|=(5288271081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1092916601/2000000000 : ℝ)|^4471 ≤ (45666015028229/100000000000000 : ℝ)^3447
        have hw : |(1092916601/2000000000 : ℝ)|=(1092916601/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1768427427/10000000000 : ℝ)|^4471 ≤ (10569831088723/100000000000000 : ℝ)^3447
        have hw : |(-1768427427/10000000000 : ℝ)|=(1768427427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_s2_7 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (855706953/2000000000 : ℝ)*x 0 + (4592335233/10000000000 : ℝ)*x 1 + (1991870309/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (855706953/2000000000 : ℝ)^4471 ≤ (33247877152543/100000000000000 : ℝ)^3447 := by
    have hnat : (855706953 : ℕ)^4471*100000000000000^3447 ≤ 33247877152543^3447*2000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      855706953 2000000000 33247877152543 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4592335233/10000000000 : ℝ)^4471 ≤ (7288932426559/20000000000000 : ℝ)^3447 := by
    have hnat : (4592335233 : ℕ)^4471*20000000000000^3447 ≤ 7288932426559^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4592335233 10000000000 7288932426559 20000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1991870309/5000000000 : ℝ)^4471 ≤ (30307460696807/100000000000000 : ℝ)^3447 := by
    have hnat : (1991870309 : ℕ)^4471*100000000000000^3447 ≤ 30307460696807^3447*5000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1991870309 5000000000 30307460696807 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(855706953/2000000000 : ℝ), (4592335233/10000000000 : ℝ), (1991870309/5000000000 : ℝ)] ![(33247877152543/100000000000000 : ℝ), (7288932426559/20000000000000 : ℝ), (30307460696807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(855706953/2000000000 : ℝ)|^4471 ≤ (33247877152543/100000000000000 : ℝ)^3447
        have hw : |(855706953/2000000000 : ℝ)|=(855706953/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4592335233/10000000000 : ℝ)|^4471 ≤ (7288932426559/20000000000000 : ℝ)^3447
        have hw : |(4592335233/10000000000 : ℝ)|=(4592335233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1991870309/5000000000 : ℝ)|^4471 ≤ (30307460696807/100000000000000 : ℝ)^3447
        have hw : |(1991870309/5000000000 : ℝ)|=(1991870309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1487_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80692417/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9307/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1001/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (2561/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16099/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9307/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1001/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9307/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1001/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9307/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1001/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9307/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1001/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9307/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1001/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9307/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1001/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1001/12500 : ℝ) ^ (4469/1024 : ℝ) ≤ (163944303923043/10000000000000000000 : ℝ) := by
    have hpowers : (1001/12500 : ℝ)^4469 ≤ (163944303923043/10000000000000000000 : ℝ)^1024 := by
      have hnat : (1001 : ℕ)^4469*10000000000000000000^1024 ≤ 163944303923043^1024*12500^4469 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1001 12500 163944303923043 10000000000000000000 4469 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1001/12500 : ℝ)) (X := (163944303923043/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4469 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9307/50000 : ℝ) ^ (4469/1024 : ℝ) ≤ (13014342855993033/20000000000000000000 : ℝ) := by
    have hpowers : (9307/50000 : ℝ)^4469 ≤ (13014342855993033/20000000000000000000 : ℝ)^1024 := by
      have hnat : (9307 : ℕ)^4469*20000000000000000000^1024 ≤ 13014342855993033^1024*50000^4469 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9307 50000 13014342855993033 20000000000000000000 4469 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9307/50000 : ℝ)) (X := (13014342855993033/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4469 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000163944303923043/5000000000000000000 : ℝ) ≤ (625004695593131/625000000000000 : ℝ) ^ (4469/1024 : ℝ) := by
    have hpowers : (5000163944303923043/5000000000000000000 : ℝ)^1024 ≤ (625004695593131/625000000000000 : ℝ)^4469 := by
      have hnat : (5000163944303923043 : ℕ)^1024*625000000000000^4469 ≤ 625004695593131^4469*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000163944303923043 5000000000000000000 625004695593131 625000000000000 1024 4469 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625004695593131/625000000000000 : ℝ)) (X := (5000163944303923043/5000000000000000000 : ℝ)) (by norm_num) 4469 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20013342231463839119/20000000000000000000 : ℝ) ≤ (5000764093388951/5000000000000000 : ℝ) ^ (4469/1024 : ℝ) := by
    have hpowers : (20013342231463839119/20000000000000000000 : ℝ)^1024 ≤ (5000764093388951/5000000000000000 : ℝ)^4469 := by
      have hnat : (20013342231463839119 : ℕ)^1024*5000000000000000^4469 ≤ 5000764093388951^4469*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20013342231463839119 20000000000000000000 5000764093388951 5000000000000000 1024 4469 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000764093388951/5000000000000000 : ℝ)) (X := (20013342231463839119/20000000000000000000 : ℝ)) (by norm_num) 4469 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10013014342855993033/10000000000000000000 : ℝ) ≤ (2500745311016427/2500000000000000 : ℝ) ^ (4469/1024 : ℝ) := by
    have hpowers : (10013014342855993033/10000000000000000000 : ℝ)^1024 ≤ (2500745311016427/2500000000000000 : ℝ)^4469 := by
      have hnat : (10013014342855993033 : ℕ)^1024*2500000000000000^4469 ≤ 2500745311016427^4469*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10013014342855993033 10000000000000000000 2500745311016427 2500000000000000 1024 4469 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500745311016427/2500000000000000 : ℝ)) (X := (10013014342855993033/10000000000000000000 : ℝ)) (by norm_num) 4469 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(163944303923043/10000000000000000000 : ℝ) ≤ ((331367264555782679/331437500000000000 : ℝ)+2*(726528643903/530300000000000 : ℝ)*(1001/12500 : ℝ))^(4469/1024 : ℝ) := by
    rw [show (331367264555782679/331437500000000000 : ℝ)+2*(726528643903/530300000000000 : ℝ)*(1001/12500 : ℝ)=(625004695593131/625000000000000 : ℝ) by norm_num, show 1+2*(163944303923043/10000000000000000000 : ℝ)=(5000163944303923043/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13014342855993033/20000000000000000000 : ℝ)+(163944303923043/10000000000000000000 : ℝ) ≤ ((331367264555782679/331437500000000000 : ℝ)+(726528643903/530300000000000 : ℝ)*((9307/50000 : ℝ)+(1001/12500 : ℝ)))^(4469/1024 : ℝ) := by
    rw [show (331367264555782679/331437500000000000 : ℝ)+(726528643903/530300000000000 : ℝ)*((9307/50000 : ℝ)+(1001/12500 : ℝ))=(5000764093388951/5000000000000000 : ℝ) by norm_num, show 1+(13014342855993033/20000000000000000000 : ℝ)+(163944303923043/10000000000000000000 : ℝ)=(20013342231463839119/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13014342855993033/20000000000000000000 : ℝ) ≤ ((331367264555782679/331437500000000000 : ℝ)+2*(726528643903/530300000000000 : ℝ)*(9307/50000 : ℝ))^(4469/1024 : ℝ) := by
    rw [show (331367264555782679/331437500000000000 : ℝ)+2*(726528643903/530300000000000 : ℝ)*(9307/50000 : ℝ)=(2500745311016427/2500000000000000 : ℝ) by norm_num, show 1+2*(13014342855993033/20000000000000000000 : ℝ)=(10013014342855993033/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (331367264555782679/331437500000000000 : ℝ)*(X 1 0+X 2 0)+(726528643903/530300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4469/1024 : ℝ)) (lo := (1001/12500 : ℝ)) (hi := (9307/50000 : ℝ)) (c := (331367264555782679/331437500000000000 : ℝ)) (alpha := (726528643903/530300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (331367264555782679/331437500000000000 : ℝ)*(X 0 1+X 2 1)+(726528643903/530300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4469/1024 : ℝ)) (lo := (1001/12500 : ℝ)) (hi := (9307/50000 : ℝ)) (c := (331367264555782679/331437500000000000 : ℝ)) (alpha := (726528643903/530300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (331367264555782679/331437500000000000 : ℝ)*(X 0 2+X 1 2)+(726528643903/530300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4469/1024 : ℝ)) (lo := (1001/12500 : ℝ)) (hi := (9307/50000 : ℝ)) (c := (331367264555782679/331437500000000000 : ℝ)) (alpha := (726528643903/530300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-475174829/2500000000 : ℝ)*X 0 0+(1366594403/2500000000 : ℝ)*X 0 1+(1297402519/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1072133021/2000000000 : ℝ)*X 1 0+(-408680101/2000000000 : ℝ)*X 1 1+(648701281/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5360665311/10000000000 : ℝ)*X 2 0+(5189610149/10000000000 : ℝ)*X 2 1+(-51085009/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4278402331/10000000000 : ℝ)*X 0 0+(1989871073/5000000000 : ℝ)*X 0 1+(91925939/200000000 : ℝ)*X 0 2+(4278402331/10000000000 : ℝ)*X 1 0+(1989871073/5000000000 : ℝ)*X 1 1+(91925939/200000000 : ℝ)*X 1 2+(4278402331/10000000000 : ℝ)*X 2 0+(1989871073/5000000000 : ℝ)*X 2 1+(91925939/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1900758929/10000000000 : ℝ)*X 0 0+(1297847047/2500000000 : ℝ)*X 0 1+(2732291501/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1322067719/2500000000 : ℝ)*X 1 0+(-1768427747/10000000000 : ℝ)*X 1 1+(5464582979/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5288271081/10000000000 : ℝ)*X 2 0+(1092916601/2000000000 : ℝ)*X 2 1+(-1768427427/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((855706953/2000000000 : ℝ)*X 0 0+(4592335233/10000000000 : ℝ)*X 0 1+(1991870309/5000000000 : ℝ)*X 0 2+(855706953/2000000000 : ℝ)*X 1 0+(4592335233/10000000000 : ℝ)*X 1 1+(1991870309/5000000000 : ℝ)*X 1 2+(855706953/2000000000 : ℝ)*X 2 0+(4592335233/10000000000 : ℝ)*X 2 1+(1991870309/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15040427111842113606356337/1657187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (321098823/25000000000000 : ℝ)*(base19) + (619150383/50000000000000 : ℝ)*(base23) + (3098159/3125000000000 : ℝ)*(lower2) + (24247239/12500000000000 : ℝ)*(upper3) + (185337103/100000000000000 : ℝ)*(upper5) + (523510690066323/20000000000000 : ℝ)*(major0) + (523510690066323/20000000000000 : ℝ)*(major1) + (523510690066323/20000000000000 : ℝ)*(major2) + (903289047303657/25000000000000 : ℝ)*(sp0) + (3613172579754829/100000000000000 : ℝ)*(sp1) + (722634525169871/20000000000000 : ℝ)*(sp2) + (405480952129133/25000000000000 : ℝ)*(sp3) + (17674935493/100000000000000 : ℝ)*(sp4) + (892546739/10000000000000 : ℝ)*(sp7) + (810966366991961/50000000000000 : ℝ)*(f.failure) + (1806586932075061/50000000000000 : ℝ)*(f.sum) + (6894644534711/2651500000000000000000000000 : ℝ)*base66 + (2021584521714971/3314375000000000000000000000000 : ℝ)*base67 + (19542923317767471/3314375000000000000000000000000 : ℝ)*base69 + (68291145255119/207148437500000000000000000000 : ℝ)*base72 + (5724889969061/2651500000000000000000000000 : ℝ)*base74 + (1591585960871221/3314375000000000000000000000000 : ℝ)*base75 + (698357509874137/414296875000000000000000000000 : ℝ)*base77 + (2417661662306577/1657187500000000000000000000000 : ℝ)*base80 + (4205016922809/5303000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (22340263/2500000000000000000000 : ℝ)*base90 + (22340263/2500000000000000000000 : ℝ)*base92 + (22340263/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (87440695294873893501182151/16571875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (34802161/6250000000000 : ℝ)*(base19) + (778876377/100000000000000 : ℝ)*(base23) + (72926761/100000000000000 : ℝ)*(upper3) + (3878779/25000000000000 : ℝ)*(lower4) + (37052707/25000000000000 : ℝ)*(upper5) + (1325880941350867/50000000000000 : ℝ)*(major0) + (1325880941350867/50000000000000 : ℝ)*(major1) + (1325880941350867/50000000000000 : ℝ)*(major2) + (6226145907/100000000000000 : ℝ)*(sp1) + (9937565993/100000000000000 : ℝ)*(sp2) + (3660394048178511/100000000000000 : ℝ)*(sp4) + (915096816299507/25000000000000 : ℝ)*(sp5) + (1830191665868071/50000000000000 : ℝ)*(sp6) + (164312954134323/10000000000000 : ℝ)*(sp7) + (164312954134323/10000000000000 : ℝ)*(f.failure) + (3660394048178511/100000000000000 : ℝ)*(f.sum) + (26599131737163/26515000000000000000000000000 : ℝ)*base66 + (11898669953344267/4142968750000000000000000000000 : ℝ)*base67 + (19000814189506767/4142968750000000000000000000000 : ℝ)*base69 + (60513317201923943/16571875000000000000000000000000 : ℝ)*base71 + (57341694155283/26515000000000000000000000000 : ℝ)*base74 + (61936799037172909/8285937500000000000000000000000 : ℝ)*base75 + (34479389419780193/16571875000000000000000000000000 : ℝ)*base77 + (90239059252448943/16571875000000000000000000000000 : ℝ)*base79 + (49116725514603/6628750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (4471309/500000000000000000000 : ℝ)*base90 + (4471309/500000000000000000000 : ℝ)*base92 + (4471309/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1487_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80692417/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9307/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1001/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2561/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16099/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1487_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1487_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80692417/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2561/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16099/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1487_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1487_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1487_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80692417/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2561/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16099/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1487_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

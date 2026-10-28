-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_w1013_box
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:02:38.170511+00:00
-- url     : https://prove2.me/submissions/30799a76-0ca2-4d79-8d53-86291ff082be

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
theorem support_rectangle_w1013_box_0 (p : ℝ) (hpa : (8205/2048 : ℝ) ≤ p) (hpb : p ≤ (4103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2098820859/10000000000 : ℝ)*x 0 + (1075613943/2000000000 : ℝ)*x 1 + (5378068573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2098820859/10000000000 : ℝ)^4103 ≤ (12487657655297/100000000000000 : ℝ)^3079 := by
    have hnat : (2098820859 : ℕ)^4103*100000000000000^3079 ≤ 12487657655297^3079*10000000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098820859 10000000000 12487657655297 100000000000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1075613943/2000000000 : ℝ)^4103 ≤ (43756177355753/100000000000000 : ℝ)^3079 := by
    have hnat : (1075613943 : ℕ)^4103*100000000000000^3079 ≤ 43756177355753^3079*2000000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075613943 2000000000 43756177355753 100000000000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5378068573/10000000000 : ℝ)^4103 ≤ (43756164974321/100000000000000 : ℝ)^3079 := by
    have hnat : (5378068573 : ℕ)^4103*100000000000000^3079 ≤ 43756164974321^3079*10000000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378068573 10000000000 43756164974321 100000000000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4103/1024 : ℝ)) 4103 3079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2098820859/10000000000 : ℝ), (1075613943/2000000000 : ℝ), (5378068573/10000000000 : ℝ)] ![(12487657655297/100000000000000 : ℝ), (43756177355753/100000000000000 : ℝ), (43756164974321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2098820859/10000000000 : ℝ)|^4103 ≤ (12487657655297/100000000000000 : ℝ)^3079
        have hw : |(-2098820859/10000000000 : ℝ)|=(2098820859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1075613943/2000000000 : ℝ)|^4103 ≤ (43756177355753/100000000000000 : ℝ)^3079
        have hw : |(1075613943/2000000000 : ℝ)|=(1075613943/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5378068573/10000000000 : ℝ)|^4103 ≤ (43756164974321/100000000000000 : ℝ)^3079
        have hw : |(5378068573/10000000000 : ℝ)|=(5378068573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1013_box_1 (p : ℝ) (hpa : (8205/2048 : ℝ) ≤ p) (hpb : p ≤ (4103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323641731/2500000000 : ℝ)*x 0 + (-1105855281/5000000000 : ℝ)*x 1 + (2689034793/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323641731/2500000000 : ℝ)^4103 ≤ (21426597655941/50000000000000 : ℝ)^3079 := by
    have hnat : (1323641731 : ℕ)^4103*50000000000000^3079 ≤ 21426597655941^3079*2500000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323641731 2500000000 21426597655941 50000000000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1105855281/5000000000 : ℝ)^4103 ≤ (2678125742869/20000000000000 : ℝ)^3079 := by
    have hnat : (1105855281 : ℕ)^4103*20000000000000^3079 ≤ 2678125742869^3079*5000000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105855281 5000000000 2678125742869 20000000000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2689034793/5000000000 : ℝ)^4103 ≤ (875123519143/2000000000000 : ℝ)^3079 := by
    have hnat : (2689034793 : ℕ)^4103*2000000000000^3079 ≤ 875123519143^3079*5000000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689034793 5000000000 875123519143 2000000000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4103/1024 : ℝ)) 4103 3079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323641731/2500000000 : ℝ), (-1105855281/5000000000 : ℝ), (2689034793/5000000000 : ℝ)] ![(21426597655941/50000000000000 : ℝ), (2678125742869/20000000000000 : ℝ), (875123519143/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323641731/2500000000 : ℝ)|^4103 ≤ (21426597655941/50000000000000 : ℝ)^3079
        have hw : |(1323641731/2500000000 : ℝ)|=(1323641731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1105855281/5000000000 : ℝ)|^4103 ≤ (2678125742869/20000000000000 : ℝ)^3079
        have hw : |(-1105855281/5000000000 : ℝ)|=(1105855281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2689034793/5000000000 : ℝ)|^4103 ≤ (875123519143/2000000000000 : ℝ)^3079
        have hw : |(2689034793/5000000000 : ℝ)|=(2689034793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1013_box_2 (p : ℝ) (hpa : (8205/2048 : ℝ) ≤ p) (hpb : p ≤ (4103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323641721/2500000000 : ℝ)*x 0 + (2689035037/5000000000 : ℝ)*x 1 + (-2211709959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323641721/2500000000 : ℝ)^4103 ≤ (42853194880457/100000000000000 : ℝ)^3079 := by
    have hnat : (1323641721 : ℕ)^4103*100000000000000^3079 ≤ 42853194880457^3079*2500000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323641721 2500000000 42853194880457 100000000000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2689035037/5000000000 : ℝ)^4103 ≤ (43756181247989/100000000000000 : ℝ)^3079 := by
    have hnat : (2689035037 : ℕ)^4103*100000000000000^3079 ≤ 43756181247989^3079*5000000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689035037 5000000000 43756181247989 100000000000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2211709959/10000000000 : ℝ)^4103 ≤ (3347655962339/25000000000000 : ℝ)^3079 := by
    have hnat : (2211709959 : ℕ)^4103*25000000000000^3079 ≤ 3347655962339^3079*10000000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2211709959 10000000000 3347655962339 25000000000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4103/1024 : ℝ)) 4103 3079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323641721/2500000000 : ℝ), (2689035037/5000000000 : ℝ), (-2211709959/10000000000 : ℝ)] ![(42853194880457/100000000000000 : ℝ), (43756181247989/100000000000000 : ℝ), (3347655962339/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323641721/2500000000 : ℝ)|^4103 ≤ (42853194880457/100000000000000 : ℝ)^3079
        have hw : |(1323641721/2500000000 : ℝ)|=(1323641721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2689035037/5000000000 : ℝ)|^4103 ≤ (43756181247989/100000000000000 : ℝ)^3079
        have hw : |(2689035037/5000000000 : ℝ)|=(2689035037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2211709959/10000000000 : ℝ)|^4103 ≤ (3347655962339/25000000000000 : ℝ)^3079
        have hw : |(-2211709959/10000000000 : ℝ)|=(2211709959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1013_box_3 (p : ℝ) (hpa : (8205/2048 : ℝ) ≤ p) (hpb : p ≤ (4103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4492177493/10000000000 : ℝ)*x 0 + (4330870959/10000000000 : ℝ)*x 1 + (2165435101/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4492177493/10000000000 : ℝ)^4103 ≤ (34424891953577/100000000000000 : ℝ)^3079 := by
    have hnat : (4492177493 : ℕ)^4103*100000000000000^3079 ≤ 34424891953577^3079*10000000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492177493 10000000000 34424891953577 100000000000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4330870959/10000000000 : ℝ)^4103 ≤ (16393778917621/50000000000000 : ℝ)^3079 := by
    have hnat : (4330870959 : ℕ)^4103*50000000000000^3079 ≤ 16393778917621^3079*10000000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4330870959 10000000000 16393778917621 50000000000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2165435101/5000000000 : ℝ)^4103 ≤ (4098443774783/12500000000000 : ℝ)^3079 := by
    have hnat : (2165435101 : ℕ)^4103*12500000000000^3079 ≤ 4098443774783^3079*5000000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165435101 5000000000 4098443774783 12500000000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4103/1024 : ℝ)) 4103 3079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4492177493/10000000000 : ℝ), (4330870959/10000000000 : ℝ), (2165435101/5000000000 : ℝ)] ![(34424891953577/100000000000000 : ℝ), (16393778917621/50000000000000 : ℝ), (4098443774783/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4492177493/10000000000 : ℝ)|^4103 ≤ (34424891953577/100000000000000 : ℝ)^3079
        have hw : |(4492177493/10000000000 : ℝ)|=(4492177493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4330870959/10000000000 : ℝ)|^4103 ≤ (16393778917621/50000000000000 : ℝ)^3079
        have hw : |(4330870959/10000000000 : ℝ)|=(4330870959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2165435101/5000000000 : ℝ)|^4103 ≤ (4098443774783/12500000000000 : ℝ)^3079
        have hw : |(2165435101/5000000000 : ℝ)|=(2165435101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1013_box_4 (p : ℝ) (hpa : (8205/2048 : ℝ) ≤ p) (hpb : p ≤ (4103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2362848413/10000000000 : ℝ)*x 0 + (5279259251/10000000000 : ℝ)*x 1 + (1055851837/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2362848413/10000000000 : ℝ)^4103 ≤ (14623656307227/100000000000000 : ℝ)^3079 := by
    have hnat : (2362848413 : ℕ)^4103*100000000000000^3079 ≤ 14623656307227^3079*10000000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2362848413 10000000000 14623656307227 100000000000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5279259251/10000000000 : ℝ)^4103 ≤ (333501345257/781250000000 : ℝ)^3079 := by
    have hnat : (5279259251 : ℕ)^4103*781250000000^3079 ≤ 333501345257^3079*10000000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279259251 10000000000 333501345257 781250000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1055851837/2000000000 : ℝ)^4103 ≤ (42688171481731/100000000000000 : ℝ)^3079 := by
    have hnat : (1055851837 : ℕ)^4103*100000000000000^3079 ≤ 42688171481731^3079*2000000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055851837 2000000000 42688171481731 100000000000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4103/1024 : ℝ)) 4103 3079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2362848413/10000000000 : ℝ), (5279259251/10000000000 : ℝ), (1055851837/2000000000 : ℝ)] ![(14623656307227/100000000000000 : ℝ), (333501345257/781250000000 : ℝ), (42688171481731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2362848413/10000000000 : ℝ)|^4103 ≤ (14623656307227/100000000000000 : ℝ)^3079
        have hw : |(-2362848413/10000000000 : ℝ)|=(2362848413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5279259251/10000000000 : ℝ)|^4103 ≤ (333501345257/781250000000 : ℝ)^3079
        have hw : |(5279259251/10000000000 : ℝ)|=(5279259251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1055851837/2000000000 : ℝ)|^4103 ≤ (42688171481731/100000000000000 : ℝ)^3079
        have hw : |(1055851837/2000000000 : ℝ)|=(1055851837/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1013_box_5 (p : ℝ) (hpa : (8205/2048 : ℝ) ≤ p) (hpb : p ≤ (4103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (214583319/400000000 : ℝ)*x 0 + (-2250170381/10000000000 : ℝ)*x 1 + (5279258857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214583319/400000000 : ℝ)^4103 ≤ (2725626043013/6250000000000 : ℝ)^3079 := by
    have hnat : (214583319 : ℕ)^4103*6250000000000^3079 ≤ 2725626043013^3079*400000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214583319 400000000 2725626043013 6250000000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2250170381/10000000000 : ℝ)^4103 ≤ (1712726917889/12500000000000 : ℝ)^3079 := by
    have hnat : (2250170381 : ℕ)^4103*12500000000000^3079 ≤ 1712726917889^3079*10000000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250170381 10000000000 1712726917889 12500000000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5279258857/10000000000 : ℝ)^4103 ≤ (667002624179/1562500000000 : ℝ)^3079 := by
    have hnat : (5279258857 : ℕ)^4103*1562500000000^3079 ≤ 667002624179^3079*10000000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279258857 10000000000 667002624179 1562500000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4103/1024 : ℝ)) 4103 3079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214583319/400000000 : ℝ), (-2250170381/10000000000 : ℝ), (5279258857/10000000000 : ℝ)] ![(2725626043013/6250000000000 : ℝ), (1712726917889/12500000000000 : ℝ), (667002624179/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214583319/400000000 : ℝ)|^4103 ≤ (2725626043013/6250000000000 : ℝ)^3079
        have hw : |(214583319/400000000 : ℝ)|=(214583319/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2250170381/10000000000 : ℝ)|^4103 ≤ (1712726917889/12500000000000 : ℝ)^3079
        have hw : |(-2250170381/10000000000 : ℝ)|=(2250170381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5279258857/10000000000 : ℝ)|^4103 ≤ (667002624179/1562500000000 : ℝ)^3079
        have hw : |(5279258857/10000000000 : ℝ)|=(5279258857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1013_box_6 (p : ℝ) (hpa : (8205/2048 : ℝ) ≤ p) (hpb : p ≤ (4103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5364582047/10000000000 : ℝ)*x 0 + (5279259623/10000000000 : ℝ)*x 1 + (-562542651/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364582047/10000000000 : ℝ)^4103 ≤ (21805003317669/50000000000000 : ℝ)^3079 := by
    have hnat : (5364582047 : ℕ)^4103*50000000000000^3079 ≤ 21805003317669^3079*10000000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364582047 10000000000 21805003317669 50000000000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5279259623/10000000000 : ℝ)^4103 ≤ (133400550629/312500000000 : ℝ)^3079 := by
    have hnat : (5279259623 : ℕ)^4103*312500000000^3079 ≤ 133400550629^3079*10000000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279259623 10000000000 133400550629 312500000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (562542651/2500000000 : ℝ)^4103 ≤ (1712727144077/12500000000000 : ℝ)^3079 := by
    have hnat : (562542651 : ℕ)^4103*12500000000000^3079 ≤ 1712727144077^3079*2500000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562542651 2500000000 1712727144077 12500000000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4103/1024 : ℝ)) 4103 3079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364582047/10000000000 : ℝ), (5279259623/10000000000 : ℝ), (-562542651/2500000000 : ℝ)] ![(21805003317669/50000000000000 : ℝ), (133400550629/312500000000 : ℝ), (1712727144077/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364582047/10000000000 : ℝ)|^4103 ≤ (21805003317669/50000000000000 : ℝ)^3079
        have hw : |(5364582047/10000000000 : ℝ)|=(5364582047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5279259623/10000000000 : ℝ)|^4103 ≤ (133400550629/312500000000 : ℝ)^3079
        have hw : |(5279259623/10000000000 : ℝ)|=(5279259623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-562542651/2500000000 : ℝ)|^4103 ≤ (1712727144077/12500000000000 : ℝ)^3079
        have hw : |(-562542651/2500000000 : ℝ)|=(562542651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1013_box_7 (p : ℝ) (hpa : (8205/2048 : ℝ) ≤ p) (hpb : p ≤ (4103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (213692997/500000000 : ℝ)*x 0 + (4440007183/10000000000 : ℝ)*x 1 + (4440007693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213692997/500000000 : ℝ)^4103 ≤ (32213666135797/100000000000000 : ℝ)^3079 := by
    have hnat : (213692997 : ℕ)^4103*100000000000000^3079 ≤ 32213666135797^3079*500000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213692997 500000000 32213666135797 100000000000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4440007183/10000000000 : ℝ)^4103 ≤ (33893164330449/100000000000000 : ℝ)^3079 := by
    have hnat : (4440007183 : ℕ)^4103*100000000000000^3079 ≤ 33893164330449^3079*10000000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4440007183 10000000000 33893164330449 100000000000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4440007693/10000000000 : ℝ)^4103 ≤ (6778633903667/20000000000000 : ℝ)^3079 := by
    have hnat : (4440007693 : ℕ)^4103*20000000000000^3079 ≤ 6778633903667^3079*10000000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4440007693 10000000000 6778633903667 20000000000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4103/1024 : ℝ)) 4103 3079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213692997/500000000 : ℝ), (4440007183/10000000000 : ℝ), (4440007693/10000000000 : ℝ)] ![(32213666135797/100000000000000 : ℝ), (33893164330449/100000000000000 : ℝ), (6778633903667/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213692997/500000000 : ℝ)|^4103 ≤ (32213666135797/100000000000000 : ℝ)^3079
        have hw : |(213692997/500000000 : ℝ)|=(213692997/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4440007183/10000000000 : ℝ)|^4103 ≤ (33893164330449/100000000000000 : ℝ)^3079
        have hw : |(4440007183/10000000000 : ℝ)|=(4440007183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4440007693/10000000000 : ℝ)|^4103 ≤ (6778633903667/20000000000000 : ℝ)^3079
        have hw : |(4440007693/10000000000 : ℝ)|=(4440007693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1013_box_8 (p : ℝ) (hpa : (8205/2048 : ℝ) ≤ p) (hpb : p ≤ (4103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-461559913/2000000000 : ℝ)*x 0 + (4072123/7812500 : ℝ)*x 1 + (2693830503/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (461559913/2000000000 : ℝ)^4103 ≤ (1771427482811/12500000000000 : ℝ)^3079 := by
    have hnat : (461559913 : ℕ)^4103*12500000000000^3079 ≤ 1771427482811^3079*2000000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      461559913 2000000000 1771427482811 12500000000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4072123/7812500 : ℝ)^4103 ≤ (20984192137267/50000000000000 : ℝ)^3079 := by
    have hnat : (4072123 : ℕ)^4103*50000000000000^3079 ≤ 20984192137267^3079*7812500^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4072123 7812500 20984192137267 50000000000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693830503/5000000000 : ℝ)^4103 ≤ (8772039170151/20000000000000 : ℝ)^3079 := by
    have hnat : (2693830503 : ℕ)^4103*20000000000000^3079 ≤ 8772039170151^3079*5000000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693830503 5000000000 8772039170151 20000000000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4103/1024 : ℝ)) 4103 3079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-461559913/2000000000 : ℝ), (4072123/7812500 : ℝ), (2693830503/5000000000 : ℝ)] ![(1771427482811/12500000000000 : ℝ), (20984192137267/50000000000000 : ℝ), (8772039170151/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-461559913/2000000000 : ℝ)|^4103 ≤ (1771427482811/12500000000000 : ℝ)^3079
        have hw : |(-461559913/2000000000 : ℝ)|=(461559913/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4072123/7812500 : ℝ)|^4103 ≤ (20984192137267/50000000000000 : ℝ)^3079
        have hw : |(4072123/7812500 : ℝ)|=(4072123/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693830503/5000000000 : ℝ)|^4103 ≤ (8772039170151/20000000000000 : ℝ)^3079
        have hw : |(2693830503/5000000000 : ℝ)|=(2693830503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1013_box_9 (p : ℝ) (hpa : (8205/2048 : ℝ) ≤ p) (hpb : p ≤ (4103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1321941609/2500000000 : ℝ)*x 0 + (-2207905613/10000000000 : ℝ)*x 1 + (5387661123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321941609/2500000000 : ℝ)^4103 ≤ (5347482948813/12500000000000 : ℝ)^3079 := by
    have hnat : (1321941609 : ℕ)^4103*12500000000000^3079 ≤ 5347482948813^3079*2500000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321941609 2500000000 5347482948813 12500000000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2207905613/10000000000 : ℝ)^4103 ≤ (13359939269089/100000000000000 : ℝ)^3079 := by
    have hnat : (2207905613 : ℕ)^4103*100000000000000^3079 ≤ 13359939269089^3079*10000000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2207905613 10000000000 13359939269089 100000000000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5387661123/10000000000 : ℝ)^4103 ≤ (43860197120007/100000000000000 : ℝ)^3079 := by
    have hnat : (5387661123 : ℕ)^4103*100000000000000^3079 ≤ 43860197120007^3079*10000000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387661123 10000000000 43860197120007 100000000000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4103/1024 : ℝ)) 4103 3079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321941609/2500000000 : ℝ), (-2207905613/10000000000 : ℝ), (5387661123/10000000000 : ℝ)] ![(5347482948813/12500000000000 : ℝ), (13359939269089/100000000000000 : ℝ), (43860197120007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321941609/2500000000 : ℝ)|^4103 ≤ (5347482948813/12500000000000 : ℝ)^3079
        have hw : |(1321941609/2500000000 : ℝ)|=(1321941609/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2207905613/10000000000 : ℝ)|^4103 ≤ (13359939269089/100000000000000 : ℝ)^3079
        have hw : |(-2207905613/10000000000 : ℝ)|=(2207905613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5387661123/10000000000 : ℝ)|^4103 ≤ (43860197120007/100000000000000 : ℝ)^3079
        have hw : |(5387661123/10000000000 : ℝ)|=(5387661123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1013_box_10 (p : ℝ) (hpa : (8205/2048 : ℝ) ≤ p) (hpb : p ≤ (4103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5287766913/10000000000 : ℝ)*x 0 + (1346915267/2500000000 : ℝ)*x 1 + (-2207905049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287766913/10000000000 : ℝ)^4103 ≤ (534748359163/1250000000000 : ℝ)^3079 := by
    have hnat : (5287766913 : ℕ)^4103*1250000000000^3079 ≤ 534748359163^3079*10000000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287766913 10000000000 534748359163 1250000000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1346915267/2500000000 : ℝ)^4103 ≤ (877203930467/2000000000000 : ℝ)^3079 := by
    have hnat : (1346915267 : ℕ)^4103*2000000000000^3079 ≤ 877203930467^3079*2500000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346915267 2500000000 877203930467 2000000000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2207905049/10000000000 : ℝ)^4103 ≤ (13359934721357/100000000000000 : ℝ)^3079 := by
    have hnat : (2207905049 : ℕ)^4103*100000000000000^3079 ≤ 13359934721357^3079*10000000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2207905049 10000000000 13359934721357 100000000000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4103/1024 : ℝ)) 4103 3079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287766913/10000000000 : ℝ), (1346915267/2500000000 : ℝ), (-2207905049/10000000000 : ℝ)] ![(534748359163/1250000000000 : ℝ), (877203930467/2000000000000 : ℝ), (13359934721357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287766913/10000000000 : ℝ)|^4103 ≤ (534748359163/1250000000000 : ℝ)^3079
        have hw : |(5287766913/10000000000 : ℝ)|=(5287766913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1346915267/2500000000 : ℝ)|^4103 ≤ (877203930467/2000000000000 : ℝ)^3079
        have hw : |(1346915267/2500000000 : ℝ)|=(1346915267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2207905049/10000000000 : ℝ)|^4103 ≤ (13359934721357/100000000000000 : ℝ)^3079
        have hw : |(-2207905049/10000000000 : ℝ)|=(2207905049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1013_box_11 (p : ℝ) (hpa : (8205/2048 : ℝ) ≤ p) (hpb : p ≤ (4103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2256548543/5000000000 : ℝ)*x 0 + (4320270533/10000000000 : ℝ)*x 1 + (1080067511/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2256548543/5000000000 : ℝ)^4103 ≤ (34638686474219/100000000000000 : ℝ)^3079 := by
    have hnat : (2256548543 : ℕ)^4103*100000000000000^3079 ≤ 34638686474219^3079*5000000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2256548543 5000000000 34638686474219 100000000000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4320270533/10000000000 : ℝ)^4103 ≤ (3268065922069/10000000000000 : ℝ)^3079 := by
    have hnat : (4320270533 : ℕ)^4103*10000000000000^3079 ≤ 3268065922069^3079*10000000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320270533 10000000000 3268065922069 10000000000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1080067511/2500000000 : ℝ)^4103 ≤ (32680654291443/100000000000000 : ℝ)^3079 := by
    have hnat : (1080067511 : ℕ)^4103*100000000000000^3079 ≤ 32680654291443^3079*2500000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080067511 2500000000 32680654291443 100000000000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4103/1024 : ℝ)) 4103 3079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2256548543/5000000000 : ℝ), (4320270533/10000000000 : ℝ), (1080067511/2500000000 : ℝ)] ![(34638686474219/100000000000000 : ℝ), (3268065922069/10000000000000 : ℝ), (32680654291443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2256548543/5000000000 : ℝ)|^4103 ≤ (34638686474219/100000000000000 : ℝ)^3079
        have hw : |(2256548543/5000000000 : ℝ)|=(2256548543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4320270533/10000000000 : ℝ)|^4103 ≤ (3268065922069/10000000000000 : ℝ)^3079
        have hw : |(4320270533/10000000000 : ℝ)|=(4320270533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1080067511/2500000000 : ℝ)|^4103 ≤ (32680654291443/100000000000000 : ℝ)^3079
        have hw : |(1080067511/2500000000 : ℝ)|=(1080067511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1013_box_12 (p : ℝ) (hpa : (8205/2048 : ℝ) ≤ p) (hpb : p ≤ (4103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-86170961/400000000 : ℝ)*x 0 + (340227083/625000000 : ℝ)*x 1 + (1317822131/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86170961/400000000 : ℝ)^4103 ≤ (202019453427/1562500000000 : ℝ)^3079 := by
    have hnat : (86170961 : ℕ)^4103*1562500000000^3079 ≤ 202019453427^3079*400000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86170961 400000000 202019453427 1562500000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (340227083/625000000 : ℝ)^4103 ≤ (22234223792461/50000000000000 : ℝ)^3079 := by
    have hnat : (340227083 : ℕ)^4103*50000000000000^3079 ≤ 22234223792461^3079*625000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340227083 625000000 22234223792461 50000000000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1317822131/2500000000 : ℝ)^4103 ≤ (10650576844077/25000000000000 : ℝ)^3079 := by
    have hnat : (1317822131 : ℕ)^4103*25000000000000^3079 ≤ 10650576844077^3079*2500000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317822131 2500000000 10650576844077 25000000000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4103/1024 : ℝ)) 4103 3079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-86170961/400000000 : ℝ), (340227083/625000000 : ℝ), (1317822131/2500000000 : ℝ)] ![(202019453427/1562500000000 : ℝ), (22234223792461/50000000000000 : ℝ), (10650576844077/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-86170961/400000000 : ℝ)|^4103 ≤ (202019453427/1562500000000 : ℝ)^3079
        have hw : |(-86170961/400000000 : ℝ)|=(86170961/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(340227083/625000000 : ℝ)|^4103 ≤ (22234223792461/50000000000000 : ℝ)^3079
        have hw : |(340227083/625000000 : ℝ)|=(340227083/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1317822131/2500000000 : ℝ)|^4103 ≤ (10650576844077/25000000000000 : ℝ)^3079
        have hw : |(1317822131/2500000000 : ℝ)|=(1317822131/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1013_box_13 (p : ℝ) (hpa : (8205/2048 : ℝ) ≤ p) (hpb : p ≤ (4103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5370228043/10000000000 : ℝ)*x 0 + (-1126606423/5000000000 : ℝ)*x 1 + (1317822237/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370228043/10000000000 : ℝ)^4103 ≤ (43671179474413/100000000000000 : ℝ)^3079 := by
    have hnat : (5370228043 : ℕ)^4103*100000000000000^3079 ≤ 43671179474413^3079*10000000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370228043 10000000000 43671179474413 100000000000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1126606423/5000000000 : ℝ)^4103 ≤ (13726508563427/100000000000000 : ℝ)^3079 := by
    have hnat : (1126606423 : ℕ)^4103*100000000000000^3079 ≤ 13726508563427^3079*5000000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126606423 5000000000 13726508563427 100000000000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1317822237/2500000000 : ℝ)^4103 ≤ (10650577985677/25000000000000 : ℝ)^3079 := by
    have hnat : (1317822237 : ℕ)^4103*25000000000000^3079 ≤ 10650577985677^3079*2500000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317822237 2500000000 10650577985677 25000000000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4103/1024 : ℝ)) 4103 3079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370228043/10000000000 : ℝ), (-1126606423/5000000000 : ℝ), (1317822237/2500000000 : ℝ)] ![(43671179474413/100000000000000 : ℝ), (13726508563427/100000000000000 : ℝ), (10650577985677/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370228043/10000000000 : ℝ)|^4103 ≤ (43671179474413/100000000000000 : ℝ)^3079
        have hw : |(5370228043/10000000000 : ℝ)|=(5370228043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1126606423/5000000000 : ℝ)|^4103 ≤ (13726508563427/100000000000000 : ℝ)^3079
        have hw : |(-1126606423/5000000000 : ℝ)|=(1126606423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1317822237/2500000000 : ℝ)|^4103 ≤ (10650577985677/25000000000000 : ℝ)^3079
        have hw : |(1317822237/2500000000 : ℝ)|=(1317822237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1013_box_14 (p : ℝ) (hpa : (8205/2048 : ℝ) ≤ p) (hpb : p ≤ (4103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1074045507/2000000000 : ℝ)*x 0 + (5271289067/10000000000 : ℝ)*x 1 + (-1126606683/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074045507/2000000000 : ℝ)^4103 ≤ (85295261659/195312500000 : ℝ)^3079 := by
    have hnat : (1074045507 : ℕ)^4103*195312500000^3079 ≤ 85295261659^3079*2000000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074045507 2000000000 85295261659 195312500000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5271289067/10000000000 : ℝ)^4103 ≤ (10650578306079/25000000000000 : ℝ)^3079 := by
    have hnat : (5271289067 : ℕ)^4103*25000000000000^3079 ≤ 10650578306079^3079*10000000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271289067 10000000000 10650578306079 25000000000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1126606683/5000000000 : ℝ)^4103 ≤ (6863256392397/50000000000000 : ℝ)^3079 := by
    have hnat : (1126606683 : ℕ)^4103*50000000000000^3079 ≤ 6863256392397^3079*5000000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126606683 5000000000 6863256392397 50000000000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4103/1024 : ℝ)) 4103 3079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074045507/2000000000 : ℝ), (5271289067/10000000000 : ℝ), (-1126606683/5000000000 : ℝ)] ![(85295261659/195312500000 : ℝ), (10650578306079/25000000000000 : ℝ), (6863256392397/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074045507/2000000000 : ℝ)|^4103 ≤ (85295261659/195312500000 : ℝ)^3079
        have hw : |(1074045507/2000000000 : ℝ)|=(1074045507/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5271289067/10000000000 : ℝ)|^4103 ≤ (10650578306079/25000000000000 : ℝ)^3079
        have hw : |(5271289067/10000000000 : ℝ)|=(5271289067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1126606683/5000000000 : ℝ)|^4103 ≤ (6863256392397/50000000000000 : ℝ)^3079
        have hw : |(-1126606683/5000000000 : ℝ)|=(1126606683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1013_box_15 (p : ℝ) (hpa : (8205/2048 : ℝ) ≤ p) (hpb : p ≤ (4103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (851203951/2000000000 : ℝ)*x 0 + (278050403/625000000 : ℝ)*x 1 + (2224402861/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (851203951/2000000000 : ℝ)^4103 ≤ (1281384070151/4000000000000 : ℝ)^3079 := by
    have hnat : (851203951 : ℕ)^4103*4000000000000^3079 ≤ 1281384070151^3079*2000000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      851203951 2000000000 1281384070151 4000000000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (278050403/625000000 : ℝ)^4103 ≤ (16991351403983/50000000000000 : ℝ)^3079 := by
    have hnat : (278050403 : ℕ)^4103*50000000000000^3079 ≤ 16991351403983^3079*625000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278050403 625000000 16991351403983 50000000000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2224402861/5000000000 : ℝ)^4103 ≤ (33982695417993/100000000000000 : ℝ)^3079 := by
    have hnat : (2224402861 : ℕ)^4103*100000000000000^3079 ≤ 33982695417993^3079*5000000000^4103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2224402861 5000000000 33982695417993 100000000000000 4103 3079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4103/1024 : ℝ)) 4103 3079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(851203951/2000000000 : ℝ), (278050403/625000000 : ℝ), (2224402861/5000000000 : ℝ)] ![(1281384070151/4000000000000 : ℝ), (16991351403983/50000000000000 : ℝ), (33982695417993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(851203951/2000000000 : ℝ)|^4103 ≤ (1281384070151/4000000000000 : ℝ)^3079
        have hw : |(851203951/2000000000 : ℝ)|=(851203951/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(278050403/625000000 : ℝ)|^4103 ≤ (16991351403983/50000000000000 : ℝ)^3079
        have hw : |(278050403/625000000 : ℝ)|=(278050403/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2224402861/5000000000 : ℝ)|^4103 ≤ (33982695417993/100000000000000 : ℝ)^3079
        have hw : |(2224402861/5000000000 : ℝ)|=(2224402861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1013_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8205/2048 : ℝ) ≤ p) (hpb : p ≤ (4103/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (146963097/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (873/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11177/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62223/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29601/50000 : ℝ) ∧ (19851/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (8283/10000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (873/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11177/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (873/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11177/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (873/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11177/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (873/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11177/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (873/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11177/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (873/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11177/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11177/100000 : ℝ) ^ (8205/2048 : ℝ) ≤ (15390761191194231/100000000000000000000 : ℝ) := by
    have hpowers : (11177/100000 : ℝ)^8205 ≤ (15390761191194231/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11177 : ℕ)^8205*100000000000000000000^2048 ≤ 15390761191194231^2048*100000^8205 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11177 100000 15390761191194231 100000000000000000000 8205 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11177/100000 : ℝ)) (X := (15390761191194231/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8205 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (873/6250 : ℝ) ^ (8205/2048 : ℝ) ≤ (18796652636829509/50000000000000000000 : ℝ) := by
    have hpowers : (873/6250 : ℝ)^8205 ≤ (18796652636829509/50000000000000000000 : ℝ)^2048 := by
      have hnat : (873 : ℕ)^8205*50000000000000000000^2048 ≤ 18796652636829509^2048*6250^8205 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        873 6250 18796652636829509 50000000000000000000 8205 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (873/6250 : ℝ)) (X := (18796652636829509/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8205 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50015390761191194231/50000000000000000000 : ℝ) ≤ (2500192057521289/2500000000000000 : ℝ) ^ (8205/2048 : ℝ) := by
    have hpowers : (50015390761191194231/50000000000000000000 : ℝ)^2048 ≤ (2500192057521289/2500000000000000 : ℝ)^8205 := by
      have hnat : (50015390761191194231 : ℕ)^2048*2500000000000000^8205 ≤ 2500192057521289^8205*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015390761191194231 50000000000000000000 2500192057521289 2500000000000000 2048 8205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500192057521289/2500000000000000 : ℝ)) (X := (50015390761191194231/50000000000000000000 : ℝ)) (by norm_num) 8205 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100052984066464853249/100000000000000000000 : ℝ) ≤ (5000661120068549/5000000000000000 : ℝ) ^ (8205/2048 : ℝ) := by
    have hpowers : (100052984066464853249/100000000000000000000 : ℝ)^2048 ≤ (5000661120068549/5000000000000000 : ℝ)^8205 := by
      have hnat : (100052984066464853249 : ℕ)^2048*5000000000000000^8205 ≤ 5000661120068549^8205*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052984066464853249 100000000000000000000 5000661120068549 5000000000000000 2048 8205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000661120068549/5000000000000000 : ℝ)) (X := (100052984066464853249/100000000000000000000 : ℝ)) (by norm_num) 8205 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018796652636829509/25000000000000000000 : ℝ) ≤ (125023453127363/125000000000000 : ℝ) ^ (8205/2048 : ℝ) := by
    have hpowers : (25018796652636829509/25000000000000000000 : ℝ)^2048 ≤ (125023453127363/125000000000000 : ℝ)^8205 := by
      have hnat : (25018796652636829509 : ℕ)^2048*125000000000000^8205 ≤ 125023453127363^8205*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018796652636829509 25000000000000000000 125023453127363 125000000000000 2048 8205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125023453127363/125000000000000 : ℝ)) (X := (25018796652636829509/25000000000000000000 : ℝ)) (by norm_num) 8205 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15390761191194231/100000000000000000000 : ℝ) ≤ ((1743734986841659933/1744375000000000000 : ℝ)+2*(277005025971/139550000000000 : ℝ)*(11177/100000 : ℝ))^(8205/2048 : ℝ) := by
    rw [show (1743734986841659933/1744375000000000000 : ℝ)+2*(277005025971/139550000000000 : ℝ)*(11177/100000 : ℝ)=(2500192057521289/2500000000000000 : ℝ) by norm_num, show 1+2*(15390761191194231/100000000000000000000 : ℝ)=(50015390761191194231/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18796652636829509/50000000000000000000 : ℝ)+(15390761191194231/100000000000000000000 : ℝ) ≤ ((1743734986841659933/1744375000000000000 : ℝ)+(277005025971/139550000000000 : ℝ)*((873/6250 : ℝ)+(11177/100000 : ℝ)))^(8205/2048 : ℝ) := by
    rw [show (1743734986841659933/1744375000000000000 : ℝ)+(277005025971/139550000000000 : ℝ)*((873/6250 : ℝ)+(11177/100000 : ℝ))=(5000661120068549/5000000000000000 : ℝ) by norm_num, show 1+(18796652636829509/50000000000000000000 : ℝ)+(15390761191194231/100000000000000000000 : ℝ)=(100052984066464853249/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18796652636829509/50000000000000000000 : ℝ) ≤ ((1743734986841659933/1744375000000000000 : ℝ)+2*(277005025971/139550000000000 : ℝ)*(873/6250 : ℝ))^(8205/2048 : ℝ) := by
    rw [show (1743734986841659933/1744375000000000000 : ℝ)+2*(277005025971/139550000000000 : ℝ)*(873/6250 : ℝ)=(125023453127363/125000000000000 : ℝ) by norm_num, show 1+2*(18796652636829509/50000000000000000000 : ℝ)=(25018796652636829509/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1743734986841659933/1744375000000000000 : ℝ)*(X 1 0+X 2 0)+(277005025971/139550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8205/2048 : ℝ)) (lo := (11177/100000 : ℝ)) (hi := (873/6250 : ℝ)) (c := (1743734986841659933/1744375000000000000 : ℝ)) (alpha := (277005025971/139550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1743734986841659933/1744375000000000000 : ℝ)*(X 0 1+X 2 1)+(277005025971/139550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8205/2048 : ℝ)) (lo := (11177/100000 : ℝ)) (hi := (873/6250 : ℝ)) (c := (1743734986841659933/1744375000000000000 : ℝ)) (alpha := (277005025971/139550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1743734986841659933/1744375000000000000 : ℝ)*(X 0 2+X 1 2)+(277005025971/139550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8205/2048 : ℝ)) (lo := (11177/100000 : ℝ)) (hi := (873/6250 : ℝ)) (c := (1743734986841659933/1744375000000000000 : ℝ)) (alpha := (277005025971/139550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2098820859/10000000000 : ℝ)*X 0 0+(1075613943/2000000000 : ℝ)*X 0 1+(5378068573/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1013_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1323641731/2500000000 : ℝ)*X 1 0+(-1105855281/5000000000 : ℝ)*X 1 1+(2689034793/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1013_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1323641721/2500000000 : ℝ)*X 2 0+(2689035037/5000000000 : ℝ)*X 2 1+(-2211709959/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1013_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4492177493/10000000000 : ℝ)*X 0 0+(4330870959/10000000000 : ℝ)*X 0 1+(2165435101/5000000000 : ℝ)*X 0 2+(4492177493/10000000000 : ℝ)*X 1 0+(4330870959/10000000000 : ℝ)*X 1 1+(2165435101/5000000000 : ℝ)*X 1 2+(4492177493/10000000000 : ℝ)*X 2 0+(4330870959/10000000000 : ℝ)*X 2 1+(2165435101/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1013_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2362848413/10000000000 : ℝ)*X 0 0+(5279259251/10000000000 : ℝ)*X 0 1+(1055851837/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1013_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((214583319/400000000 : ℝ)*X 1 0+(-2250170381/10000000000 : ℝ)*X 1 1+(5279258857/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1013_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5364582047/10000000000 : ℝ)*X 2 0+(5279259623/10000000000 : ℝ)*X 2 1+(-562542651/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1013_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((213692997/500000000 : ℝ)*X 0 0+(4440007183/10000000000 : ℝ)*X 0 1+(4440007693/10000000000 : ℝ)*X 0 2+(213692997/500000000 : ℝ)*X 1 0+(4440007183/10000000000 : ℝ)*X 1 1+(4440007693/10000000000 : ℝ)*X 1 2+(213692997/500000000 : ℝ)*X 2 0+(4440007183/10000000000 : ℝ)*X 2 1+(4440007693/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1013_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-461559913/2000000000 : ℝ)*X 0 0+(4072123/7812500 : ℝ)*X 0 1+(2693830503/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1013_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1321941609/2500000000 : ℝ)*X 1 0+(-2207905613/10000000000 : ℝ)*X 1 1+(5387661123/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1013_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5287766913/10000000000 : ℝ)*X 2 0+(1346915267/2500000000 : ℝ)*X 2 1+(-2207905049/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1013_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2256548543/5000000000 : ℝ)*X 0 0+(4320270533/10000000000 : ℝ)*X 0 1+(1080067511/2500000000 : ℝ)*X 0 2+(2256548543/5000000000 : ℝ)*X 1 0+(4320270533/10000000000 : ℝ)*X 1 1+(1080067511/2500000000 : ℝ)*X 1 2+(2256548543/5000000000 : ℝ)*X 2 0+(4320270533/10000000000 : ℝ)*X 2 1+(1080067511/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1013_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-86170961/400000000 : ℝ)*X 0 0+(340227083/625000000 : ℝ)*X 0 1+(1317822131/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1013_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5370228043/10000000000 : ℝ)*X 1 0+(-1126606423/5000000000 : ℝ)*X 1 1+(1317822237/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1013_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1074045507/2000000000 : ℝ)*X 2 0+(5271289067/10000000000 : ℝ)*X 2 1+(-1126606683/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1013_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((851203951/2000000000 : ℝ)*X 0 0+(278050403/625000000 : ℝ)*X 0 1+(2224402861/5000000000 : ℝ)*X 0 2+(851203951/2000000000 : ℝ)*X 1 0+(278050403/625000000 : ℝ)*X 1 1+(2224402861/5000000000 : ℝ)*X 1 2+(851203951/2000000000 : ℝ)*X 2 0+(278050403/625000000 : ℝ)*X 2 1+(2224402861/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1013_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62223/100000 : ℝ) ≤ (-27133895063789188051381863342909/43609375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (143206877/100000000000000 : ℝ)*(upper1) + (238722843/100000000000000 : ℝ)*(upper2) + (87688823/50000000000000 : ℝ)*(lower4) + (33318077/25000000000000 : ℝ)*(upper5) + (476460245814543/12500000000000 : ℝ)*(major0) + (476460245814543/12500000000000 : ℝ)*(major1) + (476460245814543/12500000000000 : ℝ)*(major2) + (2271879303/100000000000000 : ℝ)*(sp1) + (1086068521/12500000000000 : ℝ)*(sp3) + (5050472004418437/100000000000000 : ℝ)*(sp4) + (2525234866269567/50000000000000 : ℝ)*(sp5) + (5050403495708601/100000000000000 : ℝ)*(sp6) + (324202918569829/12500000000000 : ℝ)*(sp7) + (17127177459/25000000000000 : ℝ)*(sp14) + (6484080092767/250000000000 : ℝ)*(f.failure) + (5050472004418437/100000000000000 : ℝ)*(f.sum) + (6468696767083/13955000000000000000000000000 : ℝ)*base65 + (690076693600795613/43609375000000000000000000000000 : ℝ)*base67 + (669819166337014363/43609375000000000000000000000000 : ℝ)*base69 + (4572001395663747/10902343750000000000000000000000 : ℝ)*base71 + (16174248694327/3488750000000000000000000000 : ℝ)*base73 + (276468778544749369/21804687500000000000000000000000 : ℝ)*base75 + (614907739144608113/43609375000000000000000000000000 : ℝ)*base77 + (803109151934108113/43609375000000000000000000000000 : ℝ)*base79 + (23823701118497/3488750000000000000000000000 : ℝ)*base81 + (380601/25000000000000000000 : ℝ)*base90 + (380601/25000000000000000000 : ℝ)*base92 + (380601/25000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (29601/50000 : ℝ) ≤ (12909319351732871689982130704853/21804687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (3564579/100000000000000 : ℝ)*(upper3) + (161267529/50000000000000 : ℝ)*(upper4) + (3091761/4000000000000 : ℝ)*(lower5) + (484221844117843/12500000000000 : ℝ)*(major0) + (484221844117843/12500000000000 : ℝ)*(major1) + (484221844117843/12500000000000 : ℝ)*(major2) + (127297252873613/2500000000000 : ℝ)*(sp0) + (1272971082092897/25000000000000 : ℝ)*(sp1) + (2545917676131119/50000000000000 : ℝ)*(sp2) + (263585558889163/10000000000000 : ℝ)*(sp3) + (23883015283/50000000000000 : ℝ)*(sp5) + (24185534979/25000000000000 : ℝ)*(sp6) + (2704560589/10000000000000 : ℝ)*(sp7) + (20989728817/50000000000000 : ℝ)*(sp8) + (2635882634497519/100000000000000 : ℝ)*(f.failure) + (2545966047201077/50000000000000 : ℝ)*(f.sum) + (17988398141913/3488750000000000000000000000 : ℝ)*base66 + (42681735339290481/21804687500000000000000000000000 : ℝ)*base68 + (13799148084806241/1362792968750000000000000000000 : ℝ)*base70 + (58792555023915481/21804687500000000000000000000000 : ℝ)*base72 + (64178767245471/6977500000000000000000000000 : ℝ)*base74 + (101134638283678269/21804687500000000000000000000000 : ℝ)*base75 + (5263574438596857/2725585937500000000000000000000 : ℝ)*base78 + (90367028302727981/21804687500000000000000000000000 : ℝ)*base80 + (16249623367143/3488750000000000000000000000 : ℝ)*base82 + (31056343/10000000000000000000000 : ℝ)*base89 + (31056343/10000000000000000000000 : ℝ)*base91 + (31056343/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (19851/25000 : ℝ) ≤ (6925715417753917184104267924881/8721875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19591601/100000000000000 : ℝ)*(upper0) + (3141923/4000000000000 : ℝ)*(lower3) + (206638319/50000000000000 : ℝ)*(upper4) + (434204407148403/10000000000000 : ℝ)*(major0) + (434204407148403/10000000000000 : ℝ)*(major1) + (434204407148403/10000000000000 : ℝ)*(major2) + (19610671777/12500000000000 : ℝ)*(sp1) + (4557522779/1250000000000 : ℝ)*(sp2) + (57758067579/25000000000000 : ℝ)*(sp3) + (479952103/100000000000000 : ℝ)*(sp4) + (2851552863244629/50000000000000 : ℝ)*(sp8) + (1140589864213429/20000000000000 : ℝ)*(sp9) + (5702741604619041/100000000000000 : ℝ)*(sp10) + (295428214833041/10000000000000 : ℝ)*(sp11) + (1477256590300363/50000000000000 : ℝ)*(f.failure) + (5703106206441361/100000000000000 : ℝ)*(f.sum) + (11012670742297/2791000000000000000000000000 : ℝ)*base66 + (221398408093468249/17443750000000000000000000000000 : ℝ)*base67 + (9745094351918249/17443750000000000000000000000000 : ℝ)*base69 + (22287009899375501/17443750000000000000000000000000 : ℝ)*base72 + (280279017253/111640000000000000000000000 : ℝ)*base73 + (244188940707368249/17443750000000000000000000000000 : ℝ)*base75 + (81254476071755749/17443750000000000000000000000000 : ℝ)*base77 + (186881882667561999/17443750000000000000000000000000 : ℝ)*base79 + (10980828904301/2791000000000000000000000000 : ℝ)*base82 + (6704211/5000000000000000000000 : ℝ)*base89 + (6704211/5000000000000000000000 : ℝ)*base91 + (6704211/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-8283/10000 : ℝ) ≤ (-18060381382845450038943144888897/21804687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (18615597/6250000000000 : ℝ)*(lower0) + (38027857/20000000000000 : ℝ)*(upper3) + (350242393/100000000000000 : ℝ)*(lower4) + (547032239682157/12500000000000 : ℝ)*(major0) + (547032239682157/12500000000000 : ℝ)*(major1) + (547032239682157/12500000000000 : ℝ)*(major2) + (7385885833/100000000000000 : ℝ)*(sp0) + (5768436593/20000000000000 : ℝ)*(sp5) + (63560107657/50000000000000 : ℝ)*(sp6) + (31746666343/25000000000000 : ℝ)*(sp7) + (290116201215899/5000000000000 : ℝ)*(sp12) + (362643910501303/6250000000000 : ℝ)*(sp13) + (5802204289988499/100000000000000 : ℝ)*(sp14) + (1488833381730193/50000000000000 : ℝ)*(sp15) + (1488896875062879/50000000000000 : ℝ)*(f.failure) + (5802331410203813/100000000000000 : ℝ)*(f.sum) + (80595842746987/13955000000000000000000000000 : ℝ)*base65 + (316425998642365337/43609375000000000000000000000000 : ℝ)*base67 + (149880425699790913/43609375000000000000000000000000 : ℝ)*base70 + (722282603684396587/43609375000000000000000000000000 : ℝ)*base71 + (572318135910953/13955000000000000000000000000 : ℝ)*base74 + (270397465170834087/43609375000000000000000000000000 : ℝ)*base75 + (390427192157146587/43609375000000000000000000000000 : ℝ)*base77 + (1568083875863927837/43609375000000000000000000000000 : ℝ)*base79 + (6785929894031/6977500000000000000000000000 : ℝ)*base81 + (32423737/5000000000000000000000 : ℝ)*base90 + (32423737/5000000000000000000000 : ℝ)*base92 + (32423737/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1013_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8205/2048 : ℝ) ≤ p) (hpb : p ≤ (4103/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (146963097/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (873/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11177/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29601/50000 : ℝ) else (19851/25000 : ℝ) ≤ X j i ∧ X j i ≤ (8283/10000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1013_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8205/2048 : ℝ) ≤ p) (hpb : p ≤ (4103/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (146963097/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (873/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11177/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29601/50000 : ℝ) else (19851/25000 : ℝ) ≤ X j i ∧ X j i ≤ (8283/10000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_w1013_box p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

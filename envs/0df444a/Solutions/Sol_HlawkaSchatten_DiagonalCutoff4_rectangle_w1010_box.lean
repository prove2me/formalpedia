-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_w1010_box
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T12:59:13.366773+00:00
-- url     : https://prove2.me/submissions/e601d1a5-37ef-44c0-a40f-c646893be52f

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
theorem support_rectangle_w1010_box_0 (p : ℝ) (hpa : (4101/1024 : ℝ) ≤ p) (hpb : p ≤ (8203/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-84008963/400000000 : ℝ)*x 0 + (33613173/62500000 : ℝ)*x 1 + (5378107429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84008963/400000000 : ℝ)^8203 ≤ (12495623112041/100000000000000 : ℝ)^6155 := by
    have hnat : (84008963 : ℕ)^8203*100000000000000^6155 ≤ 12495623112041^6155*400000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84008963 400000000 12495623112041 100000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33613173/62500000 : ℝ)^8203 ≤ (43752189797579/100000000000000 : ℝ)^6155 := by
    have hnat : (33613173 : ℕ)^8203*100000000000000^6155 ≤ 43752189797579^6155*62500000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33613173 62500000 43752189797579 100000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5378107429/10000000000 : ℝ)^8203 ≤ (21876093538101/50000000000000 : ℝ)^6155 := by
    have hnat : (5378107429 : ℕ)^8203*50000000000000^6155 ≤ 21876093538101^6155*10000000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378107429 10000000000 21876093538101 50000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8203/2048 : ℝ)) 8203 6155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-84008963/400000000 : ℝ), (33613173/62500000 : ℝ), (5378107429/10000000000 : ℝ)] ![(12495623112041/100000000000000 : ℝ), (43752189797579/100000000000000 : ℝ), (21876093538101/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-84008963/400000000 : ℝ)|^8203 ≤ (12495623112041/100000000000000 : ℝ)^6155
        have hw : |(-84008963/400000000 : ℝ)|=(84008963/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(33613173/62500000 : ℝ)|^8203 ≤ (43752189797579/100000000000000 : ℝ)^6155
        have hw : |(33613173/62500000 : ℝ)|=(33613173/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5378107429/10000000000 : ℝ)|^8203 ≤ (21876093538101/50000000000000 : ℝ)^6155
        have hw : |(5378107429/10000000000 : ℝ)|=(5378107429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1010_box_1 (p : ℝ) (hpa : (4101/1024 : ℝ) ≤ p) (hpb : p ≤ (8203/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (165454067/312500000 : ℝ)*x 0 + (-2213207379/10000000000 : ℝ)*x 1 + (5378107539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165454067/312500000 : ℝ)^8203 ≤ (21424190762529/50000000000000 : ℝ)^6155 := by
    have hnat : (165454067 : ℕ)^8203*50000000000000^6155 ≤ 21424190762529^6155*312500000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165454067 312500000 21424190762529 50000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2213207379/10000000000 : ℝ)^8203 ≤ (6699715096707/50000000000000 : ℝ)^6155 := by
    have hnat : (2213207379 : ℕ)^8203*50000000000000^6155 ≤ 6699715096707^6155*10000000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2213207379 10000000000 6699715096707 50000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5378107539/10000000000 : ℝ)^8203 ≤ (21876094134419/50000000000000 : ℝ)^6155 := by
    have hnat : (5378107539 : ℕ)^8203*50000000000000^6155 ≤ 21876094134419^6155*10000000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378107539 10000000000 21876094134419 50000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8203/2048 : ℝ)) 8203 6155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165454067/312500000 : ℝ), (-2213207379/10000000000 : ℝ), (5378107539/10000000000 : ℝ)] ![(21424190762529/50000000000000 : ℝ), (6699715096707/50000000000000 : ℝ), (21876094134419/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165454067/312500000 : ℝ)|^8203 ≤ (21424190762529/50000000000000 : ℝ)^6155
        have hw : |(165454067/312500000 : ℝ)|=(165454067/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2213207379/10000000000 : ℝ)|^8203 ≤ (6699715096707/50000000000000 : ℝ)^6155
        have hw : |(-2213207379/10000000000 : ℝ)|=(2213207379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5378107539/10000000000 : ℝ)|^8203 ≤ (21876094134419/50000000000000 : ℝ)^6155
        have hw : |(5378107539/10000000000 : ℝ)|=(5378107539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1010_box_2 (p : ℝ) (hpa : (4101/1024 : ℝ) ≤ p) (hpb : p ≤ (8203/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1323632523/2500000000 : ℝ)*x 0 + (672263453/1250000000 : ℝ)*x 1 + (-2213207333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323632523/2500000000 : ℝ)^8203 ≤ (42848380964197/100000000000000 : ℝ)^6155 := by
    have hnat : (1323632523 : ℕ)^8203*100000000000000^6155 ≤ 42848380964197^6155*2500000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323632523 2500000000 42848380964197 100000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (672263453/1250000000 : ℝ)^8203 ≤ (43752189190419/100000000000000 : ℝ)^6155 := by
    have hnat : (672263453 : ℕ)^8203*100000000000000^6155 ≤ 43752189190419^6155*1250000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672263453 1250000000 43752189190419 100000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2213207333/10000000000 : ℝ)^8203 ≤ (13399429822249/100000000000000 : ℝ)^6155 := by
    have hnat : (2213207333 : ℕ)^8203*100000000000000^6155 ≤ 13399429822249^6155*10000000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2213207333 10000000000 13399429822249 100000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8203/2048 : ℝ)) 8203 6155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323632523/2500000000 : ℝ), (672263453/1250000000 : ℝ), (-2213207333/10000000000 : ℝ)] ![(42848380964197/100000000000000 : ℝ), (43752189190419/100000000000000 : ℝ), (13399429822249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323632523/2500000000 : ℝ)|^8203 ≤ (42848380964197/100000000000000 : ℝ)^6155
        have hw : |(1323632523/2500000000 : ℝ)|=(1323632523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(672263453/1250000000 : ℝ)|^8203 ≤ (43752189190419/100000000000000 : ℝ)^6155
        have hw : |(672263453/1250000000 : ℝ)|=(672263453/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2213207333/10000000000 : ℝ)|^8203 ≤ (13399429822249/100000000000000 : ℝ)^6155
        have hw : |(-2213207333/10000000000 : ℝ)|=(2213207333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1010_box_3 (p : ℝ) (hpa : (4101/1024 : ℝ) ≤ p) (hpb : p ≤ (8203/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4492649131/10000000000 : ℝ)*x 0 + (4331294041/10000000000 : ℝ)*x 1 + (4331293973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4492649131/10000000000 : ℝ)^8203 ≤ (34425243013077/100000000000000 : ℝ)^6155 := by
    have hnat : (4492649131 : ℕ)^8203*100000000000000^6155 ≤ 34425243013077^6155*10000000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492649131 10000000000 34425243013077 100000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4331294041/10000000000 : ℝ)^8203 ≤ (32787378830543/100000000000000 : ℝ)^6155 := by
    have hnat : (4331294041 : ℕ)^8203*100000000000000^6155 ≤ 32787378830543^6155*10000000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4331294041 10000000000 32787378830543 100000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4331293973/10000000000 : ℝ)^8203 ≤ (16393689072257/50000000000000 : ℝ)^6155 := by
    have hnat : (4331293973 : ℕ)^8203*50000000000000^6155 ≤ 16393689072257^6155*10000000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4331293973 10000000000 16393689072257 50000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8203/2048 : ℝ)) 8203 6155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4492649131/10000000000 : ℝ), (4331294041/10000000000 : ℝ), (4331293973/10000000000 : ℝ)] ![(34425243013077/100000000000000 : ℝ), (32787378830543/100000000000000 : ℝ), (16393689072257/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4492649131/10000000000 : ℝ)|^8203 ≤ (34425243013077/100000000000000 : ℝ)^6155
        have hw : |(4492649131/10000000000 : ℝ)|=(4492649131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4331294041/10000000000 : ℝ)|^8203 ≤ (32787378830543/100000000000000 : ℝ)^6155
        have hw : |(4331294041/10000000000 : ℝ)|=(4331294041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4331293973/10000000000 : ℝ)|^8203 ≤ (16393689072257/50000000000000 : ℝ)^6155
        have hw : |(4331293973/10000000000 : ℝ)|=(4331293973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1010_box_4 (p : ℝ) (hpa : (4101/1024 : ℝ) ≤ p) (hpb : p ≤ (8203/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-472892099/2000000000 : ℝ)*x 0 + (5279211091/10000000000 : ℝ)*x 1 + (131980281/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (472892099/2000000000 : ℝ)^8203 ≤ (14633532095037/100000000000000 : ℝ)^6155 := by
    have hnat : (472892099 : ℕ)^8203*100000000000000^6155 ≤ 14633532095037^6155*2000000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      472892099 2000000000 14633532095037 100000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5279211091/10000000000 : ℝ)^8203 ≤ (10670808285123/25000000000000 : ℝ)^6155 := by
    have hnat : (5279211091 : ℕ)^8203*25000000000000^6155 ≤ 10670808285123^6155*10000000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279211091 10000000000 10670808285123 25000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131980281/250000000 : ℝ)^8203 ≤ (1707329389841/4000000000000 : ℝ)^6155 := by
    have hnat : (131980281 : ℕ)^8203*4000000000000^6155 ≤ 1707329389841^6155*250000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131980281 250000000 1707329389841 4000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8203/2048 : ℝ)) 8203 6155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-472892099/2000000000 : ℝ), (5279211091/10000000000 : ℝ), (131980281/250000000 : ℝ)] ![(14633532095037/100000000000000 : ℝ), (10670808285123/25000000000000 : ℝ), (1707329389841/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-472892099/2000000000 : ℝ)|^8203 ≤ (14633532095037/100000000000000 : ℝ)^6155
        have hw : |(-472892099/2000000000 : ℝ)|=(472892099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5279211091/10000000000 : ℝ)|^8203 ≤ (10670808285123/25000000000000 : ℝ)^6155
        have hw : |(5279211091/10000000000 : ℝ)|=(5279211091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131980281/250000000 : ℝ)|^8203 ≤ (1707329389841/4000000000000 : ℝ)^6155
        have hw : |(131980281/250000000 : ℝ)|=(131980281/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1010_box_5 (p : ℝ) (hpa : (4101/1024 : ℝ) ≤ p) (hpb : p ≤ (8203/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (536461157/1000000000 : ℝ)*x 0 + (-18013533/80000000 : ℝ)*x 1 + (2639605357/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536461157/1000000000 : ℝ)^8203 ≤ (8721184845399/20000000000000 : ℝ)^6155 := by
    have hnat : (536461157 : ℕ)^8203*20000000000000^6155 ≤ 8721184845399^6155*1000000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536461157 1000000000 8721184845399 20000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (18013533/80000000 : ℝ)^8203 ≤ (6855423340459/50000000000000 : ℝ)^6155 := by
    have hnat : (18013533 : ℕ)^8203*50000000000000^6155 ≤ 6855423340459^6155*80000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18013533 80000000 6855423340459 50000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2639605357/5000000000 : ℝ)^8203 ≤ (42683229078171/100000000000000 : ℝ)^6155 := by
    have hnat : (2639605357 : ℕ)^8203*100000000000000^6155 ≤ 42683229078171^6155*5000000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639605357 5000000000 42683229078171 100000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8203/2048 : ℝ)) 8203 6155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536461157/1000000000 : ℝ), (-18013533/80000000 : ℝ), (2639605357/5000000000 : ℝ)] ![(8721184845399/20000000000000 : ℝ), (6855423340459/50000000000000 : ℝ), (42683229078171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536461157/1000000000 : ℝ)|^8203 ≤ (8721184845399/20000000000000 : ℝ)^6155
        have hw : |(536461157/1000000000 : ℝ)|=(536461157/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-18013533/80000000 : ℝ)|^8203 ≤ (6855423340459/50000000000000 : ℝ)^6155
        have hw : |(-18013533/80000000 : ℝ)|=(18013533/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2639605357/5000000000 : ℝ)|^8203 ≤ (42683229078171/100000000000000 : ℝ)^6155
        have hw : |(2639605357/5000000000 : ℝ)|=(2639605357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1010_box_6 (p : ℝ) (hpa : (4101/1024 : ℝ) ≤ p) (hpb : p ≤ (8203/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5364611211/10000000000 : ℝ)*x 0 + (5279211373/10000000000 : ℝ)*x 1 + (-225169123/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364611211/10000000000 : ℝ)^8203 ≤ (2129195329/4882812500 : ℝ)^6155 := by
    have hnat : (5364611211 : ℕ)^8203*4882812500^6155 ≤ 2129195329^6155*10000000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364611211 10000000000 2129195329 4882812500 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5279211373/10000000000 : ℝ)^8203 ≤ (2667702261197/6250000000000 : ℝ)^6155 := by
    have hnat : (5279211373 : ℕ)^8203*6250000000000^6155 ≤ 2667702261197^6155*10000000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279211373 10000000000 2667702261197 6250000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (225169123/1000000000 : ℝ)^8203 ≤ (856927717213/6250000000000 : ℝ)^6155 := by
    have hnat : (225169123 : ℕ)^8203*6250000000000^6155 ≤ 856927717213^6155*1000000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225169123 1000000000 856927717213 6250000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8203/2048 : ℝ)) 8203 6155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364611211/10000000000 : ℝ), (5279211373/10000000000 : ℝ), (-225169123/1000000000 : ℝ)] ![(2129195329/4882812500 : ℝ), (2667702261197/6250000000000 : ℝ), (856927717213/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364611211/10000000000 : ℝ)|^8203 ≤ (2129195329/4882812500 : ℝ)^6155
        have hw : |(5364611211/10000000000 : ℝ)|=(5364611211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5279211373/10000000000 : ℝ)|^8203 ≤ (2667702261197/6250000000000 : ℝ)^6155
        have hw : |(5279211373/10000000000 : ℝ)|=(5279211373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-225169123/1000000000 : ℝ)|^8203 ≤ (856927717213/6250000000000 : ℝ)^6155
        have hw : |(-225169123/1000000000 : ℝ)|=(225169123/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1010_box_7 (p : ℝ) (hpa : (4101/1024 : ℝ) ≤ p) (hpb : p ≤ (8203/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068566303/2500000000 : ℝ)*x 0 + (4440464077/10000000000 : ℝ)*x 1 + (2220231981/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068566303/2500000000 : ℝ)^8203 ≤ (16106649060331/50000000000000 : ℝ)^6155 := by
    have hnat : (1068566303 : ℕ)^8203*50000000000000^6155 ≤ 16106649060331^6155*2500000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068566303 2500000000 16106649060331 50000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4440464077/10000000000 : ℝ)^8203 ≤ (33893351522307/100000000000000 : ℝ)^6155 := by
    have hnat : (4440464077 : ℕ)^8203*100000000000000^6155 ≤ 33893351522307^6155*10000000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4440464077 10000000000 33893351522307 100000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2220231981/5000000000 : ℝ)^8203 ≤ (33893350352461/100000000000000 : ℝ)^6155 := by
    have hnat : (2220231981 : ℕ)^8203*100000000000000^6155 ≤ 33893350352461^6155*5000000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2220231981 5000000000 33893350352461 100000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8203/2048 : ℝ)) 8203 6155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068566303/2500000000 : ℝ), (4440464077/10000000000 : ℝ), (2220231981/5000000000 : ℝ)] ![(16106649060331/50000000000000 : ℝ), (33893351522307/100000000000000 : ℝ), (33893350352461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068566303/2500000000 : ℝ)|^8203 ≤ (16106649060331/50000000000000 : ℝ)^6155
        have hw : |(1068566303/2500000000 : ℝ)|=(1068566303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4440464077/10000000000 : ℝ)|^8203 ≤ (33893351522307/100000000000000 : ℝ)^6155
        have hw : |(4440464077/10000000000 : ℝ)|=(4440464077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2220231981/5000000000 : ℝ)|^8203 ≤ (33893350352461/100000000000000 : ℝ)^6155
        have hw : |(2220231981/5000000000 : ℝ)|=(2220231981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1010_box_8 (p : ℝ) (hpa : (4101/1024 : ℝ) ≤ p) (hpb : p ≤ (8203/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2309372339/10000000000 : ℝ)*x 0 + (5212216817/10000000000 : ℝ)*x 1 + (673462317/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2309372339/10000000000 : ℝ)^8203 ≤ (1418092172899/10000000000000 : ℝ)^6155 := by
    have hnat : (2309372339 : ℕ)^8203*10000000000000^6155 ≤ 1418092172899^6155*10000000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2309372339 10000000000 1418092172899 10000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5212216817/10000000000 : ℝ)^8203 ≤ (20981436115603/50000000000000 : ℝ)^6155 := by
    have hnat : (5212216817 : ℕ)^8203*50000000000000^6155 ≤ 20981436115603^6155*10000000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5212216817 10000000000 20981436115603 50000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673462317/1250000000 : ℝ)^8203 ≤ (8771241205343/20000000000000 : ℝ)^6155 := by
    have hnat : (673462317 : ℕ)^8203*20000000000000^6155 ≤ 8771241205343^6155*1250000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673462317 1250000000 8771241205343 20000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8203/2048 : ℝ)) 8203 6155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2309372339/10000000000 : ℝ), (5212216817/10000000000 : ℝ), (673462317/1250000000 : ℝ)] ![(1418092172899/10000000000000 : ℝ), (20981436115603/50000000000000 : ℝ), (8771241205343/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2309372339/10000000000 : ℝ)|^8203 ≤ (1418092172899/10000000000000 : ℝ)^6155
        have hw : |(-2309372339/10000000000 : ℝ)|=(2309372339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5212216817/10000000000 : ℝ)|^8203 ≤ (20981436115603/50000000000000 : ℝ)^6155
        have hw : |(5212216817/10000000000 : ℝ)|=(5212216817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673462317/1250000000 : ℝ)|^8203 ≤ (8771241205343/20000000000000 : ℝ)^6155
        have hw : |(673462317/1250000000 : ℝ)|=(673462317/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1010_box_9 (p : ℝ) (hpa : (4101/1024 : ℝ) ≤ p) (hpb : p ≤ (8203/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1321932289/2500000000 : ℝ)*x 0 + (-276175477/1250000000 : ℝ)*x 1 + (1077539743/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321932289/2500000000 : ℝ)^8203 ≤ (1336720100923/3125000000000 : ℝ)^6155 := by
    have hnat : (1321932289 : ℕ)^8203*3125000000000^6155 ≤ 1336720100923^6155*2500000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321932289 2500000000 1336720100923 3125000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (276175477/1250000000 : ℝ)^8203 ≤ (13368748787827/100000000000000 : ℝ)^6155 := by
    have hnat : (276175477 : ℕ)^8203*100000000000000^6155 ≤ 13368748787827^6155*1250000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276175477 1250000000 13368748787827 100000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077539743/2000000000 : ℝ)^8203 ≤ (43856207968609/100000000000000 : ℝ)^6155 := by
    have hnat : (1077539743 : ℕ)^8203*100000000000000^6155 ≤ 43856207968609^6155*2000000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077539743 2000000000 43856207968609 100000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8203/2048 : ℝ)) 8203 6155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321932289/2500000000 : ℝ), (-276175477/1250000000 : ℝ), (1077539743/2000000000 : ℝ)] ![(1336720100923/3125000000000 : ℝ), (13368748787827/100000000000000 : ℝ), (43856207968609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321932289/2500000000 : ℝ)|^8203 ≤ (1336720100923/3125000000000 : ℝ)^6155
        have hw : |(1321932289/2500000000 : ℝ)|=(1321932289/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-276175477/1250000000 : ℝ)|^8203 ≤ (13368748787827/100000000000000 : ℝ)^6155
        have hw : |(-276175477/1250000000 : ℝ)|=(276175477/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1077539743/2000000000 : ℝ)|^8203 ≤ (43856207968609/100000000000000 : ℝ)^6155
        have hw : |(1077539743/2000000000 : ℝ)|=(1077539743/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1010_box_10 (p : ℝ) (hpa : (4101/1024 : ℝ) ≤ p) (hpb : p ≤ (8203/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5287729783/10000000000 : ℝ)*x 0 + (2693849293/5000000000 : ℝ)*x 1 + (-2209403151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287729783/10000000000 : ℝ)^8203 ≤ (4277504998933/10000000000000 : ℝ)^6155 := by
    have hnat : (5287729783 : ℕ)^8203*10000000000000^6155 ≤ 4277504998933^6155*10000000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287729783 10000000000 4277504998933 10000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2693849293/5000000000 : ℝ)^8203 ≤ (43856206569143/100000000000000 : ℝ)^6155 := by
    have hnat : (2693849293 : ℕ)^8203*100000000000000^6155 ≤ 43856206569143^6155*5000000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693849293 5000000000 43856206569143 100000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2209403151/10000000000 : ℝ)^8203 ≤ (6684371712573/50000000000000 : ℝ)^6155 := by
    have hnat : (2209403151 : ℕ)^8203*50000000000000^6155 ≤ 6684371712573^6155*10000000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209403151 10000000000 6684371712573 50000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8203/2048 : ℝ)) 8203 6155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287729783/10000000000 : ℝ), (2693849293/5000000000 : ℝ), (-2209403151/10000000000 : ℝ)] ![(4277504998933/10000000000000 : ℝ), (43856206569143/100000000000000 : ℝ), (6684371712573/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287729783/10000000000 : ℝ)|^8203 ≤ (4277504998933/10000000000000 : ℝ)^6155
        have hw : |(5287729783/10000000000 : ℝ)|=(5287729783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2693849293/5000000000 : ℝ)|^8203 ≤ (43856206569143/100000000000000 : ℝ)^6155
        have hw : |(2693849293/5000000000 : ℝ)|=(2693849293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2209403151/10000000000 : ℝ)|^8203 ≤ (6684371712573/50000000000000 : ℝ)^6155
        have hw : |(-2209403151/10000000000 : ℝ)|=(2209403151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1010_box_11 (p : ℝ) (hpa : (4101/1024 : ℝ) ≤ p) (hpb : p ≤ (8203/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4513554937/10000000000 : ℝ)*x 0 + (4320700867/10000000000 : ℝ)*x 1 + (864140073/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4513554937/10000000000 : ℝ)^8203 ≤ (1385556092959/4000000000000 : ℝ)^6155 := by
    have hnat : (4513554937 : ℕ)^8203*4000000000000^6155 ≤ 1385556092959^6155*10000000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4513554937 10000000000 1385556092959 4000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4320700867/10000000000 : ℝ)^8203 ≤ (1307222054381/4000000000000 : ℝ)^6155 := by
    have hnat : (4320700867 : ℕ)^8203*4000000000000^6155 ≤ 1307222054381^6155*10000000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320700867 10000000000 1307222054381 4000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (864140073/2000000000 : ℝ)^8203 ≤ (1634027314957/5000000000000 : ℝ)^6155 := by
    have hnat : (864140073 : ℕ)^8203*5000000000000^6155 ≤ 1634027314957^6155*2000000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864140073 2000000000 1634027314957 5000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8203/2048 : ℝ)) 8203 6155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4513554937/10000000000 : ℝ), (4320700867/10000000000 : ℝ), (864140073/2000000000 : ℝ)] ![(1385556092959/4000000000000 : ℝ), (1307222054381/4000000000000 : ℝ), (1634027314957/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4513554937/10000000000 : ℝ)|^8203 ≤ (1385556092959/4000000000000 : ℝ)^6155
        have hw : |(4513554937/10000000000 : ℝ)|=(4513554937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4320700867/10000000000 : ℝ)|^8203 ≤ (1307222054381/4000000000000 : ℝ)^6155
        have hw : |(4320700867/10000000000 : ℝ)|=(4320700867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(864140073/2000000000 : ℝ)|^8203 ≤ (1634027314957/5000000000000 : ℝ)^6155
        have hw : |(864140073/2000000000 : ℝ)|=(864140073/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1010_box_12 (p : ℝ) (hpa : (4101/1024 : ℝ) ≤ p) (hpb : p ≤ (8203/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2155719223/10000000000 : ℝ)*x 0 + (5443721229/10000000000 : ℝ)*x 1 + (5271242763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155719223/10000000000 : ℝ)^8203 ≤ (2587517218467/20000000000000 : ℝ)^6155 := by
    have hnat : (2155719223 : ℕ)^8203*20000000000000^6155 ≤ 2587517218467^6155*10000000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155719223 10000000000 2587517218467 20000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5443721229/10000000000 : ℝ)^8203 ≤ (44465021016571/100000000000000 : ℝ)^6155 := by
    have hnat : (5443721229 : ℕ)^8203*100000000000000^6155 ≤ 44465021016571^6155*10000000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443721229 10000000000 44465021016571 100000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5271242763/10000000000 : ℝ)^8203 ≤ (42597392879333/100000000000000 : ℝ)^6155 := by
    have hnat : (5271242763 : ℕ)^8203*100000000000000^6155 ≤ 42597392879333^6155*10000000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271242763 10000000000 42597392879333 100000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8203/2048 : ℝ)) 8203 6155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2155719223/10000000000 : ℝ), (5443721229/10000000000 : ℝ), (5271242763/10000000000 : ℝ)] ![(2587517218467/20000000000000 : ℝ), (44465021016571/100000000000000 : ℝ), (42597392879333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2155719223/10000000000 : ℝ)|^8203 ≤ (2587517218467/20000000000000 : ℝ)^6155
        have hw : |(-2155719223/10000000000 : ℝ)|=(2155719223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5443721229/10000000000 : ℝ)|^8203 ≤ (44465021016571/100000000000000 : ℝ)^6155
        have hw : |(5443721229/10000000000 : ℝ)|=(5443721229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5271242763/10000000000 : ℝ)|^8203 ≤ (42597392879333/100000000000000 : ℝ)^6155
        have hw : |(5271242763/10000000000 : ℝ)|=(5271242763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1010_box_13 (p : ℝ) (hpa : (4101/1024 : ℝ) ≤ p) (hpb : p ≤ (8203/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5370255713/10000000000 : ℝ)*x 0 + (-2254732861/10000000000 : ℝ)*x 1 + (5271242413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370255713/10000000000 : ℝ)^8203 ≤ (43667078367981/100000000000000 : ℝ)^6155 := by
    have hnat : (5370255713 : ℕ)^8203*100000000000000^6155 ≤ 43667078367981^6155*10000000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370255713 10000000000 43667078367981 100000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2254732861/10000000000 : ℝ)^8203 ≤ (13735532508249/100000000000000 : ℝ)^6155 := by
    have hnat : (2254732861 : ℕ)^8203*100000000000000^6155 ≤ 13735532508249^6155*10000000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254732861 10000000000 13735532508249 100000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5271242413/10000000000 : ℝ)^8203 ≤ (21298694554921/50000000000000 : ℝ)^6155 := by
    have hnat : (5271242413 : ℕ)^8203*50000000000000^6155 ≤ 21298694554921^6155*10000000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271242413 10000000000 21298694554921 50000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8203/2048 : ℝ)) 8203 6155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370255713/10000000000 : ℝ), (-2254732861/10000000000 : ℝ), (5271242413/10000000000 : ℝ)] ![(43667078367981/100000000000000 : ℝ), (13735532508249/100000000000000 : ℝ), (21298694554921/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370255713/10000000000 : ℝ)|^8203 ≤ (43667078367981/100000000000000 : ℝ)^6155
        have hw : |(5370255713/10000000000 : ℝ)|=(5370255713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2254732861/10000000000 : ℝ)|^8203 ≤ (13735532508249/100000000000000 : ℝ)^6155
        have hw : |(-2254732861/10000000000 : ℝ)|=(2254732861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5271242413/10000000000 : ℝ)|^8203 ≤ (21298694554921/50000000000000 : ℝ)^6155
        have hw : |(5271242413/10000000000 : ℝ)|=(5271242413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1010_box_14 (p : ℝ) (hpa : (4101/1024 : ℝ) ≤ p) (hpb : p ≤ (8203/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2685127953/5000000000 : ℝ)*x 0 + (5271242581/10000000000 : ℝ)*x 1 + (-112736619/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685127953/5000000000 : ℝ)^8203 ≤ (43667080459497/100000000000000 : ℝ)^6155 := by
    have hnat : (2685127953 : ℕ)^8203*100000000000000^6155 ≤ 43667080459497^6155*5000000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685127953 5000000000 43667080459497 100000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5271242581/10000000000 : ℝ)^8203 ≤ (21298695459599/50000000000000 : ℝ)^6155 := by
    have hnat : (5271242581 : ℕ)^8203*50000000000000^6155 ≤ 21298695459599^6155*10000000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271242581 10000000000 21298695459599 50000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (112736619/500000000 : ℝ)^8203 ≤ (13735528603077/100000000000000 : ℝ)^6155 := by
    have hnat : (112736619 : ℕ)^8203*100000000000000^6155 ≤ 13735528603077^6155*500000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112736619 500000000 13735528603077 100000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8203/2048 : ℝ)) 8203 6155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685127953/5000000000 : ℝ), (5271242581/10000000000 : ℝ), (-112736619/500000000 : ℝ)] ![(43667080459497/100000000000000 : ℝ), (21298695459599/50000000000000 : ℝ), (13735528603077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685127953/5000000000 : ℝ)|^8203 ≤ (43667080459497/100000000000000 : ℝ)^6155
        have hw : |(2685127953/5000000000 : ℝ)|=(2685127953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5271242581/10000000000 : ℝ)|^8203 ≤ (21298695459599/50000000000000 : ℝ)^6155
        have hw : |(5271242581/10000000000 : ℝ)|=(5271242581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-112736619/500000000 : ℝ)|^8203 ≤ (13735528603077/100000000000000 : ℝ)^6155
        have hw : |(-112736619/500000000 : ℝ)|=(112736619/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1010_box_15 (p : ℝ) (hpa : (4101/1024 : ℝ) ≤ p) (hpb : p ≤ (8203/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4256439813/10000000000 : ℝ)*x 0 + (4449255669/10000000000 : ℝ)*x 1 + (1112313733/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4256439813/10000000000 : ℝ)^8203 ≤ (32034379339527/100000000000000 : ℝ)^6155 := by
    have hnat : (4256439813 : ℕ)^8203*100000000000000^6155 ≤ 32034379339527^6155*10000000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4256439813 10000000000 32034379339527 100000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4449255669/10000000000 : ℝ)^8203 ≤ (16991407038973/50000000000000 : ℝ)^6155 := by
    have hnat : (4449255669 : ℕ)^8203*50000000000000^6155 ≤ 16991407038973^6155*10000000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4449255669 10000000000 16991407038973 50000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1112313733/2500000000 : ℝ)^8203 ≤ (1359312263033/4000000000000 : ℝ)^6155 := by
    have hnat : (1112313733 : ℕ)^8203*4000000000000^6155 ≤ 1359312263033^6155*2500000000^8203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1112313733 2500000000 1359312263033 4000000000000 8203 6155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8203/2048 : ℝ)) 8203 6155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4256439813/10000000000 : ℝ), (4449255669/10000000000 : ℝ), (1112313733/2500000000 : ℝ)] ![(32034379339527/100000000000000 : ℝ), (16991407038973/50000000000000 : ℝ), (1359312263033/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4256439813/10000000000 : ℝ)|^8203 ≤ (32034379339527/100000000000000 : ℝ)^6155
        have hw : |(4256439813/10000000000 : ℝ)|=(4256439813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4449255669/10000000000 : ℝ)|^8203 ≤ (16991407038973/50000000000000 : ℝ)^6155
        have hw : |(4449255669/10000000000 : ℝ)|=(4449255669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1112313733/2500000000 : ℝ)|^8203 ≤ (1359312263033/4000000000000 : ℝ)^6155
        have hw : |(1112313733/2500000000 : ℝ)|=(1112313733/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1010_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4101/1024 : ℝ) ≤ p) (hpb : p ≤ (8203/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4590777/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6983/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11173/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62223/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(74/125 : ℝ) ∧ (39697/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (82823/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6983/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11173/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6983/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11173/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6983/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11173/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6983/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11173/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6983/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11173/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6983/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11173/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11173/100000 : ℝ) ^ (4101/1024 : ℝ) ≤ (7709062931995399/50000000000000000000 : ℝ) := by
    have hpowers : (11173/100000 : ℝ)^4101 ≤ (7709062931995399/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11173 : ℕ)^4101*50000000000000000000^1024 ≤ 7709062931995399^1024*100000^4101 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11173 100000 7709062931995399 50000000000000000000 4101 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11173/100000 : ℝ)) (X := (7709062931995399/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4101 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (6983/50000 : ℝ) ^ (4101/1024 : ℝ) ≤ (18840121629397293/50000000000000000000 : ℝ) := by
    have hpowers : (6983/50000 : ℝ)^4101 ≤ (18840121629397293/50000000000000000000 : ℝ)^1024 := by
      have hnat : (6983 : ℕ)^4101*50000000000000000000^1024 ≤ 18840121629397293^1024*50000^4101 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6983 50000 18840121629397293 50000000000000000000 4101 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6983/50000 : ℝ)) (X := (18840121629397293/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4101 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007709062931995399/25000000000000000000 : ℝ) ≤ (312524058666777/312500000000000 : ℝ) ^ (4101/1024 : ℝ) := by
    have hpowers : (25007709062931995399/25000000000000000000 : ℝ)^1024 ≤ (312524058666777/312500000000000 : ℝ)^4101 := by
      have hnat : (25007709062931995399 : ℕ)^1024*312500000000000^4101 ≤ 312524058666777^4101*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007709062931995399 25000000000000000000 312524058666777 312500000000000 1024 4101 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312524058666777/312500000000000 : ℝ)) (X := (25007709062931995399/25000000000000000000 : ℝ)) (by norm_num) 4101 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506637296140348173/12500000000000000000 : ℝ) ≤ (5000662788372331/5000000000000000 : ℝ) ^ (4101/1024 : ℝ) := by
    have hpowers : (12506637296140348173/12500000000000000000 : ℝ)^1024 ≤ (5000662788372331/5000000000000000 : ℝ)^4101 := by
      have hnat : (12506637296140348173 : ℕ)^1024*5000000000000000^4101 ≤ 5000662788372331^4101*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506637296140348173 12500000000000000000 5000662788372331 5000000000000000 1024 4101 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000662788372331/5000000000000000 : ℝ)) (X := (12506637296140348173/12500000000000000000 : ℝ)) (by norm_num) 4101 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018840121629397293/25000000000000000000 : ℝ) ≤ (500094063807623/500000000000000 : ℝ) ^ (4101/1024 : ℝ) := by
    have hpowers : (25018840121629397293/25000000000000000000 : ℝ)^1024 ≤ (500094063807623/500000000000000 : ℝ)^4101 := by
      have hnat : (25018840121629397293 : ℕ)^1024*500000000000000^4101 ≤ 500094063807623^4101*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018840121629397293 25000000000000000000 500094063807623 500000000000000 1024 4101 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500094063807623/500000000000000 : ℝ)) (X := (25018840121629397293/25000000000000000000 : ℝ)) (by norm_num) 4101 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7709062931995399/50000000000000000000 : ℝ) ≤ ((6979933152108801761/6982500000000000000 : ℝ)+2*(277849703899/139650000000000 : ℝ)*(11173/100000 : ℝ))^(4101/1024 : ℝ) := by
    rw [show (6979933152108801761/6982500000000000000 : ℝ)+2*(277849703899/139650000000000 : ℝ)*(11173/100000 : ℝ)=(312524058666777/312500000000000 : ℝ) by norm_num, show 1+2*(7709062931995399/50000000000000000000 : ℝ)=(25007709062931995399/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18840121629397293/50000000000000000000 : ℝ)+(7709062931995399/50000000000000000000 : ℝ) ≤ ((6979933152108801761/6982500000000000000 : ℝ)+(277849703899/139650000000000 : ℝ)*((6983/50000 : ℝ)+(11173/100000 : ℝ)))^(4101/1024 : ℝ) := by
    rw [show (6979933152108801761/6982500000000000000 : ℝ)+(277849703899/139650000000000 : ℝ)*((6983/50000 : ℝ)+(11173/100000 : ℝ))=(5000662788372331/5000000000000000 : ℝ) by norm_num, show 1+(18840121629397293/50000000000000000000 : ℝ)+(7709062931995399/50000000000000000000 : ℝ)=(12506637296140348173/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18840121629397293/50000000000000000000 : ℝ) ≤ ((6979933152108801761/6982500000000000000 : ℝ)+2*(277849703899/139650000000000 : ℝ)*(6983/50000 : ℝ))^(4101/1024 : ℝ) := by
    rw [show (6979933152108801761/6982500000000000000 : ℝ)+2*(277849703899/139650000000000 : ℝ)*(6983/50000 : ℝ)=(500094063807623/500000000000000 : ℝ) by norm_num, show 1+2*(18840121629397293/50000000000000000000 : ℝ)=(25018840121629397293/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6979933152108801761/6982500000000000000 : ℝ)*(X 1 0+X 2 0)+(277849703899/139650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4101/1024 : ℝ)) (lo := (11173/100000 : ℝ)) (hi := (6983/50000 : ℝ)) (c := (6979933152108801761/6982500000000000000 : ℝ)) (alpha := (277849703899/139650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6979933152108801761/6982500000000000000 : ℝ)*(X 0 1+X 2 1)+(277849703899/139650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4101/1024 : ℝ)) (lo := (11173/100000 : ℝ)) (hi := (6983/50000 : ℝ)) (c := (6979933152108801761/6982500000000000000 : ℝ)) (alpha := (277849703899/139650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6979933152108801761/6982500000000000000 : ℝ)*(X 0 2+X 1 2)+(277849703899/139650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4101/1024 : ℝ)) (lo := (11173/100000 : ℝ)) (hi := (6983/50000 : ℝ)) (c := (6979933152108801761/6982500000000000000 : ℝ)) (alpha := (277849703899/139650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-84008963/400000000 : ℝ)*X 0 0+(33613173/62500000 : ℝ)*X 0 1+(5378107429/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1010_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((165454067/312500000 : ℝ)*X 1 0+(-2213207379/10000000000 : ℝ)*X 1 1+(5378107539/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1010_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1323632523/2500000000 : ℝ)*X 2 0+(672263453/1250000000 : ℝ)*X 2 1+(-2213207333/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1010_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4492649131/10000000000 : ℝ)*X 0 0+(4331294041/10000000000 : ℝ)*X 0 1+(4331293973/10000000000 : ℝ)*X 0 2+(4492649131/10000000000 : ℝ)*X 1 0+(4331294041/10000000000 : ℝ)*X 1 1+(4331293973/10000000000 : ℝ)*X 1 2+(4492649131/10000000000 : ℝ)*X 2 0+(4331294041/10000000000 : ℝ)*X 2 1+(4331293973/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1010_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-472892099/2000000000 : ℝ)*X 0 0+(5279211091/10000000000 : ℝ)*X 0 1+(131980281/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1010_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((536461157/1000000000 : ℝ)*X 1 0+(-18013533/80000000 : ℝ)*X 1 1+(2639605357/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1010_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5364611211/10000000000 : ℝ)*X 2 0+(5279211373/10000000000 : ℝ)*X 2 1+(-225169123/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1010_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1068566303/2500000000 : ℝ)*X 0 0+(4440464077/10000000000 : ℝ)*X 0 1+(2220231981/5000000000 : ℝ)*X 0 2+(1068566303/2500000000 : ℝ)*X 1 0+(4440464077/10000000000 : ℝ)*X 1 1+(2220231981/5000000000 : ℝ)*X 1 2+(1068566303/2500000000 : ℝ)*X 2 0+(4440464077/10000000000 : ℝ)*X 2 1+(2220231981/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1010_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2309372339/10000000000 : ℝ)*X 0 0+(5212216817/10000000000 : ℝ)*X 0 1+(673462317/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1010_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1321932289/2500000000 : ℝ)*X 1 0+(-276175477/1250000000 : ℝ)*X 1 1+(1077539743/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1010_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5287729783/10000000000 : ℝ)*X 2 0+(2693849293/5000000000 : ℝ)*X 2 1+(-2209403151/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1010_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4513554937/10000000000 : ℝ)*X 0 0+(4320700867/10000000000 : ℝ)*X 0 1+(864140073/2000000000 : ℝ)*X 0 2+(4513554937/10000000000 : ℝ)*X 1 0+(4320700867/10000000000 : ℝ)*X 1 1+(864140073/2000000000 : ℝ)*X 1 2+(4513554937/10000000000 : ℝ)*X 2 0+(4320700867/10000000000 : ℝ)*X 2 1+(864140073/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1010_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2155719223/10000000000 : ℝ)*X 0 0+(5443721229/10000000000 : ℝ)*X 0 1+(5271242763/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1010_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5370255713/10000000000 : ℝ)*X 1 0+(-2254732861/10000000000 : ℝ)*X 1 1+(5271242413/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1010_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2685127953/5000000000 : ℝ)*X 2 0+(5271242581/10000000000 : ℝ)*X 2 1+(-112736619/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1010_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4256439813/10000000000 : ℝ)*X 0 0+(4449255669/10000000000 : ℝ)*X 0 1+(1112313733/2500000000 : ℝ)*X 0 2+(4256439813/10000000000 : ℝ)*X 1 0+(4449255669/10000000000 : ℝ)*X 1 1+(1112313733/2500000000 : ℝ)*X 1 2+(4256439813/10000000000 : ℝ)*X 2 0+(4449255669/10000000000 : ℝ)*X 2 1+(1112313733/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1010_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62223/100000 : ℝ) ≤ (-36204412441419722505757916741061/58187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (41569689/100000000000000 : ℝ)*(upper0) + (11063459/6250000000000 : ℝ)*(upper1) + (205839859/100000000000000 : ℝ)*(upper5) + (1904608232088801/50000000000000 : ℝ)*(major0) + (1904608232088801/50000000000000 : ℝ)*(major1) + (1904608232088801/50000000000000 : ℝ)*(major2) + (20768520609/100000000000000 : ℝ)*(sp1) + (4027015913/20000000000000 : ℝ)*(sp3) + (1261545094698683/25000000000000 : ℝ)*(sp4) + (504617039308187/10000000000000 : ℝ)*(sp5) + (504612807669031/10000000000000 : ℝ)*(sp6) + (648240429392173/25000000000000 : ℝ)*(sp7) + (5391403873/50000000000000 : ℝ)*(sp8) + (7885614021/12500000000000 : ℝ)*(sp14) + (40515341447629/1562500000000 : ℝ)*(f.failure) + (5046191161602479/100000000000000 : ℝ)*(f.sum) + (8006011677543/4655000000000000000000000000 : ℝ)*base66 + (2112675155895751187/116375000000000000000000000000000 : ℝ)*base67 + (766239629458001187/116375000000000000000000000000000 : ℝ)*base69 + (324117002320748813/116375000000000000000000000000000 : ℝ)*base72 + (36130725158377/1163750000000000000000000000 : ℝ)*base74 + (2302147698052376187/116375000000000000000000000000000 : ℝ)*base75 + (129820440619001187/116375000000000000000000000000000 : ℝ)*base77 + (2634457086362248813/116375000000000000000000000000000 : ℝ)*base80 + (6455873151737/4655000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (219693/19531250000000000000 : ℝ)*base90 + (219693/19531250000000000000 : ℝ)*base92 + (219693/19531250000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (74/125 : ℝ) ≤ (3626135194726130475756405591991/6125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2828583/25000000000000 : ℝ)*(lower1) + (4932279/20000000000000 : ℝ)*(upper4) + (6780143/20000000000000 : ℝ)*(lower5) + (3871203824419937/100000000000000 : ℝ)*(major0) + (3871203824419937/100000000000000 : ℝ)*(major1) + (3871203824419937/100000000000000 : ℝ)*(major2) + (5087489799954241/100000000000000 : ℝ)*(sp0) + (5087492247421229/100000000000000 : ℝ)*(sp1) + (5087484953517459/100000000000000 : ℝ)*(sp2) + (1317587458914783/50000000000000 : ℝ)*(sp3) + (487389863/12500000000000 : ℝ)*(sp5) + (5596511337/50000000000000 : ℝ)*(sp6) + (1257691611/50000000000000 : ℝ)*(sp7) + (6346585893/100000000000000 : ℝ)*(sp8) + (658794358303197/25000000000000 : ℝ)*(f.failure) + (5087496146540133/100000000000000 : ℝ)*(f.sum) + (28062681119497/6982500000000000000000000000 : ℝ)*base66 + (819402367049009057/698250000000000000000000000000000 : ℝ)*base67 + (5408793941925509057/698250000000000000000000000000000 : ℝ)*base69 + (2185416279782759057/698250000000000000000000000000000 : ℝ)*base71 + (122852786999459/13965000000000000000000000000 : ℝ)*base74 + (14867446351163009057/698250000000000000000000000000000 : ℝ)*base75 + (8169189623908259057/698250000000000000000000000000000 : ℝ)*base77 + (6759802396523759057/698250000000000000000000000000000 : ℝ)*base79 + (38592794798251/13965000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (32819/78125000000000000000 : ℝ)*base89 + (32819/78125000000000000000 : ℝ)*base91 + (32819/78125000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (39697/50000 : ℝ) ≤ (46198935246365540434142545403721/58187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19139033/50000000000000 : ℝ)*(upper0) + (28748629/25000000000000 : ℝ)*(lower3) + (495630803/100000000000000 : ℝ)*(upper4) + (4339530233699139/100000000000000 : ℝ)*(major0) + (4339530233699139/100000000000000 : ℝ)*(major1) + (4339530233699139/100000000000000 : ℝ)*(major2) + (128913541103/50000000000000 : ℝ)*(sp1) + (461265962193/100000000000000 : ℝ)*(sp2) + (26487815823/10000000000000 : ℝ)*(sp3) + (2791722859/100000000000000 : ℝ)*(sp4) + (227944758942249/4000000000000 : ℝ)*(sp8) + (2849181969098439/50000000000000 : ℝ)*(sp9) + (5698160499316891/100000000000000 : ℝ)*(sp10) + (1476854134251479/50000000000000 : ℝ)*(sp11) + (738493286665297/25000000000000 : ℝ)*(f.failure) + (1424655441319771/25000000000000 : ℝ)*(f.sum) + (9158864477047/2327500000000000000000000000 : ℝ)*base65 + (191636701927644593/232750000000000000000000000000000 : ℝ)*base67 + (546881889949855407/232750000000000000000000000000000 : ℝ)*base70 + (791769217543144593/232750000000000000000000000000000 : ℝ)*base71 + (39998827530649/1163750000000000000000000000 : ℝ)*base74 + (119937307059144593/232750000000000000000000000000000 : ℝ)*base75 + (1078823568446394593/232750000000000000000000000000000 : ℝ)*base77 + (6009313593156644593/232750000000000000000000000000000 : ℝ)*base79 + (1590669085861/290937500000000000000000000 : ℝ)*base82 + (177981/78125000000000000000 : ℝ)*base90 + (177981/78125000000000000000 : ℝ)*base92 + (177981/78125000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-82823/100000 : ℝ) ≤ (-19276582741081949558368321844999/23275000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (43460699/100000000000000 : ℝ)*(lower0) + (165100367/50000000000000 : ℝ)*(lower2) + (9961429/10000000000000 : ℝ)*(upper3) + (42453533/50000000000000 : ℝ)*(upper5) + (874745731384841/20000000000000 : ℝ)*(major0) + (874745731384841/20000000000000 : ℝ)*(major1) + (874745731384841/20000000000000 : ℝ)*(major2) + (132376491/25000000000000 : ℝ)*(sp0) + (386777875573/100000000000000 : ℝ)*(sp5) + (36607681973/25000000000000 : ℝ)*(sp7) + (5797811331038731/100000000000000 : ℝ)*(sp12) + (5797425082669123/100000000000000 : ℝ)*(sp13) + (1159562372108939/20000000000000 : ℝ)*(sp14) + (1488553007701141/50000000000000 : ℝ)*(sp15) + (1488626223065087/50000000000000 : ℝ)*(f.failure) + (1159562372108939/20000000000000 : ℝ)*(f.sum) + (9077655689917/2793000000000000000000000000 : ℝ)*base65 + (1365219677426194999/139650000000000000000000000000000 : ℝ)*base68 + (779867587375405001/139650000000000000000000000000000 : ℝ)*base69 + (695120243149894999/139650000000000000000000000000000 : ℝ)*base72 + (20878417242971/698250000000000000000000000 : ℝ)*base74 + (448904748390394999/139650000000000000000000000000000 : ℝ)*base76 + (1722907027586455001/139650000000000000000000000000000 : ℝ)*base77 + (1641382283209594999/139650000000000000000000000000000 : ℝ)*base80 + (6987420541757/1396500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (590099/156250000000000000000 : ℝ)*base89 + (590099/156250000000000000000 : ℝ)*base91 + (590099/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1010_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4101/1024 : ℝ) ≤ p) (hpb : p ≤ (8203/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4590777/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6983/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11173/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(74/125 : ℝ) else (39697/50000 : ℝ) ≤ X j i ∧ X j i ≤ (82823/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1010_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4101/1024 : ℝ) ≤ p) (hpb : p ≤ (8203/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4590777/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6983/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11173/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(74/125 : ℝ) else (39697/50000 : ℝ) ≤ X j i ∧ X j i ≤ (82823/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_w1010_box p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

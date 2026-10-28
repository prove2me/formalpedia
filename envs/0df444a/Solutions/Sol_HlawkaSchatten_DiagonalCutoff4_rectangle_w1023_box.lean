-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_w1023_box
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:13:49.469691+00:00
-- url     : https://prove2.me/submissions/d821a2cc-a8a9-417d-bde0-9922dcd41ade

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
theorem support_rectangle_w1023_box_0 (p : ℝ) (hpa : (8215/2048 : ℝ) ≤ p) (hpb : p ≤ (1027/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-523537309/2500000000 : ℝ)*x 0 + (672242803/1250000000 : ℝ)*x 1 + (1075588497/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (523537309/2500000000 : ℝ)^1027 ≤ (12461132143447/100000000000000 : ℝ)^771 := by
    have hnat : (523537309 : ℕ)^1027*100000000000000^771 ≤ 12461132143447^771*2500000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523537309 2500000000 12461132143447 100000000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (672242803/1250000000 : ℝ)^1027 ≤ (8753886718387/20000000000000 : ℝ)^771 := by
    have hnat : (672242803 : ℕ)^1027*20000000000000^771 ≤ 8753886718387^771*1250000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672242803 1250000000 8753886718387 20000000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1075588497/2000000000 : ℝ)^1027 ≤ (21884717126619/50000000000000 : ℝ)^771 := by
    have hnat : (1075588497 : ℕ)^1027*50000000000000^771 ≤ 21884717126619^771*2000000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075588497 2000000000 21884717126619 50000000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1027/256 : ℝ)) 1027 771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-523537309/2500000000 : ℝ), (672242803/1250000000 : ℝ), (1075588497/2000000000 : ℝ)] ![(12461132143447/100000000000000 : ℝ), (8753886718387/20000000000000 : ℝ), (21884717126619/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-523537309/2500000000 : ℝ)|^1027 ≤ (12461132143447/100000000000000 : ℝ)^771
        have hw : |(-523537309/2500000000 : ℝ)|=(523537309/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(672242803/1250000000 : ℝ)|^1027 ≤ (8753886718387/20000000000000 : ℝ)^771
        have hw : |(672242803/1250000000 : ℝ)|=(672242803/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1075588497/2000000000 : ℝ)|^1027 ≤ (21884717126619/50000000000000 : ℝ)^771
        have hw : |(1075588497/2000000000 : ℝ)|=(1075588497/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1023_box_1 (p : ℝ) (hpa : (8215/2048 : ℝ) ≤ p) (hpb : p ≤ (1027/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5294690947/10000000000 : ℝ)*x 0 + (-551682353/2500000000 : ℝ)*x 1 + (2688971201/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294690947/10000000000 : ℝ)^1027 ≤ (42869228759653/100000000000000 : ℝ)^771 := by
    have hnat : (5294690947 : ℕ)^1027*100000000000000^771 ≤ 42869228759653^771*10000000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294690947 10000000000 42869228759653 100000000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (551682353/2500000000 : ℝ)^1027 ≤ (6680668938987/50000000000000 : ℝ)^771 := by
    have hnat : (551682353 : ℕ)^1027*50000000000000^771 ≤ 6680668938987^771*2500000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551682353 2500000000 6680668938987 50000000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688971201/5000000000 : ℝ)^1027 ≤ (5471179169179/12500000000000 : ℝ)^771 := by
    have hnat : (2688971201 : ℕ)^1027*12500000000000^771 ≤ 5471179169179^771*5000000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688971201 5000000000 5471179169179 12500000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1027/256 : ℝ)) 1027 771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294690947/10000000000 : ℝ), (-551682353/2500000000 : ℝ), (2688971201/5000000000 : ℝ)] ![(42869228759653/100000000000000 : ℝ), (6680668938987/50000000000000 : ℝ), (5471179169179/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294690947/10000000000 : ℝ)|^1027 ≤ (42869228759653/100000000000000 : ℝ)^771
        have hw : |(5294690947/10000000000 : ℝ)|=(5294690947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-551682353/2500000000 : ℝ)|^1027 ≤ (6680668938987/50000000000000 : ℝ)^771
        have hw : |(-551682353/2500000000 : ℝ)|=(551682353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688971201/5000000000 : ℝ)|^1027 ≤ (5471179169179/12500000000000 : ℝ)^771
        have hw : |(2688971201/5000000000 : ℝ)|=(2688971201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1023_box_2 (p : ℝ) (hpa : (8215/2048 : ℝ) ≤ p) (hpb : p ≤ (1027/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5294690587/10000000000 : ℝ)*x 0 + (5377942691/10000000000 : ℝ)*x 1 + (-441345901/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294690587/10000000000 : ℝ)^1027 ≤ (10717306219261/25000000000000 : ℝ)^771 := by
    have hnat : (5294690587 : ℕ)^1027*25000000000000^771 ≤ 10717306219261^771*10000000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294690587 10000000000 10717306219261 25000000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5377942691/10000000000 : ℝ)^1027 ≤ (10942359121623/25000000000000 : ℝ)^771 := by
    have hnat : (5377942691 : ℕ)^1027*25000000000000^771 ≤ 10942359121623^771*10000000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377942691 10000000000 10942359121623 25000000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (441345901/2000000000 : ℝ)^1027 ≤ (13361338628041/100000000000000 : ℝ)^771 := by
    have hnat : (441345901 : ℕ)^1027*100000000000000^771 ≤ 13361338628041^771*2000000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441345901 2000000000 13361338628041 100000000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1027/256 : ℝ)) 1027 771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294690587/10000000000 : ℝ), (5377942691/10000000000 : ℝ), (-441345901/2000000000 : ℝ)] ![(10717306219261/25000000000000 : ℝ), (10942359121623/25000000000000 : ℝ), (13361338628041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294690587/10000000000 : ℝ)|^1027 ≤ (10717306219261/25000000000000 : ℝ)^771
        have hw : |(5294690587/10000000000 : ℝ)|=(5294690587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5377942691/10000000000 : ℝ)|^1027 ≤ (10942359121623/25000000000000 : ℝ)^771
        have hw : |(5377942691/10000000000 : ℝ)|=(5377942691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-441345901/2000000000 : ℝ)|^1027 ≤ (13361338628041/100000000000000 : ℝ)^771
        have hw : |(-441345901/2000000000 : ℝ)|=(441345901/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1023_box_3 (p : ℝ) (hpa : (8215/2048 : ℝ) ≤ p) (hpb : p ≤ (1027/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4490607847/10000000000 : ℝ)*x 0 + (432946199/1000000000 : ℝ)*x 1 + (865892351/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4490607847/10000000000 : ℝ)^1027 ≤ (26893531669/78125000000 : ℝ)^771 := by
    have hnat : (4490607847 : ℕ)^1027*78125000000^771 ≤ 26893531669^771*10000000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490607847 10000000000 26893531669 78125000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (432946199/1000000000 : ℝ)^1027 ≤ (8197035228037/25000000000000 : ℝ)^771 := by
    have hnat : (432946199 : ℕ)^1027*25000000000000^771 ≤ 8197035228037^771*1000000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432946199 1000000000 8197035228037 25000000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (865892351/2000000000 : ℝ)^1027 ≤ (16394069270751/50000000000000 : ℝ)^771 := by
    have hnat : (865892351 : ℕ)^1027*50000000000000^771 ≤ 16394069270751^771*2000000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865892351 2000000000 16394069270751 50000000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1027/256 : ℝ)) 1027 771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4490607847/10000000000 : ℝ), (432946199/1000000000 : ℝ), (865892351/2000000000 : ℝ)] ![(26893531669/78125000000 : ℝ), (8197035228037/25000000000000 : ℝ), (16394069270751/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4490607847/10000000000 : ℝ)|^1027 ≤ (26893531669/78125000000 : ℝ)^771
        have hw : |(4490607847/10000000000 : ℝ)|=(4490607847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(432946199/1000000000 : ℝ)|^1027 ≤ (8197035228037/25000000000000 : ℝ)^771
        have hw : |(432946199/1000000000 : ℝ)|=(432946199/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(865892351/2000000000 : ℝ)|^1027 ≤ (16394069270751/50000000000000 : ℝ)^771
        have hw : |(865892351/2000000000 : ℝ)|=(865892351/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1023_box_4 (p : ℝ) (hpa : (8215/2048 : ℝ) ≤ p) (hpb : p ≤ (1027/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1178742133/5000000000 : ℝ)*x 0 + (1319854767/2500000000 : ℝ)*x 1 + (82490927/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1178742133/5000000000 : ℝ)^1027 ≤ (3647699248459/25000000000000 : ℝ)^771 := by
    have hnat : (1178742133 : ℕ)^1027*25000000000000^771 ≤ 3647699248459^771*5000000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1178742133 5000000000 3647699248459 25000000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1319854767/2500000000 : ℝ)^1027 ≤ (21352300049339/50000000000000 : ℝ)^771 := by
    have hnat : (1319854767 : ℕ)^1027*50000000000000^771 ≤ 21352300049339^771*2500000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319854767 2500000000 21352300049339 50000000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82490927/156250000 : ℝ)^1027 ≤ (333629710157/781250000000 : ℝ)^771 := by
    have hnat : (82490927 : ℕ)^1027*781250000000^771 ≤ 333629710157^771*156250000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82490927 156250000 333629710157 781250000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1027/256 : ℝ)) 1027 771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1178742133/5000000000 : ℝ), (1319854767/2500000000 : ℝ), (82490927/156250000 : ℝ)] ![(3647699248459/25000000000000 : ℝ), (21352300049339/50000000000000 : ℝ), (333629710157/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1178742133/5000000000 : ℝ)|^1027 ≤ (3647699248459/25000000000000 : ℝ)^771
        have hw : |(-1178742133/5000000000 : ℝ)|=(1178742133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1319854767/2500000000 : ℝ)|^1027 ≤ (21352300049339/50000000000000 : ℝ)^771
        have hw : |(1319854767/2500000000 : ℝ)|=(1319854767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(82490927/156250000 : ℝ)|^1027 ≤ (333629710157/781250000000 : ℝ)^771
        have hw : |(82490927/156250000 : ℝ)|=(82490927/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1023_box_5 (p : ℝ) (hpa : (8215/2048 : ℝ) ≤ p) (hpb : p ≤ (1027/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1072897409/2000000000 : ℝ)*x 0 + (-561277567/2500000000 : ℝ)*x 1 + (13198547/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072897409/2000000000 : ℝ)^1027 ≤ (8724724789713/20000000000000 : ℝ)^771 := by
    have hnat : (1072897409 : ℕ)^1027*20000000000000^771 ≤ 8724724789713^771*2000000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072897409 2000000000 8724724789713 20000000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (561277567/2500000000 : ℝ)^1027 ≤ (1708972352571/12500000000000 : ℝ)^771 := by
    have hnat : (561277567 : ℕ)^1027*12500000000000^771 ≤ 1708972352571^771*2500000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561277567 2500000000 1708972352571 12500000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13198547/25000000 : ℝ)^1027 ≤ (42704597211063/100000000000000 : ℝ)^771 := by
    have hnat : (13198547 : ℕ)^1027*100000000000000^771 ≤ 42704597211063^771*25000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13198547 25000000 42704597211063 100000000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1027/256 : ℝ)) 1027 771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072897409/2000000000 : ℝ), (-561277567/2500000000 : ℝ), (13198547/25000000 : ℝ)] ![(8724724789713/20000000000000 : ℝ), (1708972352571/12500000000000 : ℝ), (42704597211063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072897409/2000000000 : ℝ)|^1027 ≤ (8724724789713/20000000000000 : ℝ)^771
        have hw : |(1072897409/2000000000 : ℝ)|=(1072897409/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-561277567/2500000000 : ℝ)|^1027 ≤ (1708972352571/12500000000000 : ℝ)^771
        have hw : |(-561277567/2500000000 : ℝ)|=(561277567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(13198547/25000000 : ℝ)|^1027 ≤ (42704597211063/100000000000000 : ℝ)^771
        have hw : |(13198547/25000000 : ℝ)|=(13198547/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1023_box_6 (p : ℝ) (hpa : (8215/2048 : ℝ) ≤ p) (hpb : p ≤ (1027/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5364486297/10000000000 : ℝ)*x 0 + (1319854879/2500000000 : ℝ)*x 1 + (-561277579/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364486297/10000000000 : ℝ)^1027 ≤ (43623615846211/100000000000000 : ℝ)^771 := by
    have hnat : (5364486297 : ℕ)^1027*100000000000000^771 ≤ 43623615846211^771*10000000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364486297 10000000000 43623615846211 100000000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1319854879/2500000000 : ℝ)^1027 ≤ (42704604925737/100000000000000 : ℝ)^771 := by
    have hnat : (1319854879 : ℕ)^1027*100000000000000^771 ≤ 42704604925737^771*2500000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319854879 2500000000 42704604925737 100000000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (561277579/2500000000 : ℝ)^1027 ≤ (6835889604961/50000000000000 : ℝ)^771 := by
    have hnat : (561277579 : ℕ)^1027*50000000000000^771 ≤ 6835889604961^771*2500000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561277579 2500000000 6835889604961 50000000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1027/256 : ℝ)) 1027 771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364486297/10000000000 : ℝ), (1319854879/2500000000 : ℝ), (-561277579/2500000000 : ℝ)] ![(43623615846211/100000000000000 : ℝ), (42704604925737/100000000000000 : ℝ), (6835889604961/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364486297/10000000000 : ℝ)|^1027 ≤ (43623615846211/100000000000000 : ℝ)^771
        have hw : |(5364486297/10000000000 : ℝ)|=(5364486297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1319854879/2500000000 : ℝ)|^1027 ≤ (42704604925737/100000000000000 : ℝ)^771
        have hw : |(1319854879/2500000000 : ℝ)|=(1319854879/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-561277579/2500000000 : ℝ)|^1027 ≤ (6835889604961/50000000000000 : ℝ)^771
        have hw : |(-561277579/2500000000 : ℝ)|=(561277579/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1023_box_7 (p : ℝ) (hpa : (8215/2048 : ℝ) ≤ p) (hpb : p ≤ (1027/256 : ℝ)) (x : Fin 3 → ℝ) :
    (854501897/2000000000 : ℝ)*x 0 + (4438489039/10000000000 : ℝ)*x 1 + (443848939/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (854501897/2000000000 : ℝ)^1027 ≤ (257718964691/800000000000 : ℝ)^771 := by
    have hnat : (854501897 : ℕ)^1027*800000000000^771 ≤ 257718964691^771*2000000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      854501897 2000000000 257718964691 800000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4438489039/10000000000 : ℝ)^1027 ≤ (6778512582983/20000000000000 : ℝ)^771 := by
    have hnat : (4438489039 : ℕ)^1027*20000000000000^771 ≤ 6778512582983^771*10000000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4438489039 10000000000 6778512582983 20000000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (443848939/1000000000 : ℝ)^1027 ≤ (16946283242557/50000000000000 : ℝ)^771 := by
    have hnat : (443848939 : ℕ)^1027*50000000000000^771 ≤ 16946283242557^771*1000000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443848939 1000000000 16946283242557 50000000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1027/256 : ℝ)) 1027 771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(854501897/2000000000 : ℝ), (4438489039/10000000000 : ℝ), (443848939/1000000000 : ℝ)] ![(257718964691/800000000000 : ℝ), (6778512582983/20000000000000 : ℝ), (16946283242557/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(854501897/2000000000 : ℝ)|^1027 ≤ (257718964691/800000000000 : ℝ)^771
        have hw : |(854501897/2000000000 : ℝ)|=(854501897/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4438489039/10000000000 : ℝ)|^1027 ≤ (6778512582983/20000000000000 : ℝ)^771
        have hw : |(4438489039/10000000000 : ℝ)|=(4438489039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(443848939/1000000000 : ℝ)|^1027 ≤ (16946283242557/50000000000000 : ℝ)^771
        have hw : |(443848939/1000000000 : ℝ)|=(443848939/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1023_box_8 (p : ℝ) (hpa : (8215/2048 : ℝ) ≤ p) (hpb : p ≤ (1027/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2302566859/10000000000 : ℝ)*x 0 + (5212651061/10000000000 : ℝ)*x 1 + (1077507409/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2302566859/10000000000 : ℝ)^1027 ≤ (1413980936207/10000000000000 : ℝ)^771 := by
    have hnat : (2302566859 : ℕ)^1027*10000000000000^771 ≤ 1413980936207^771*10000000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2302566859 10000000000 1413980936207 10000000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5212651061/10000000000 : ℝ)^1027 ≤ (41986710586997/100000000000000 : ℝ)^771 := by
    have hnat : (5212651061 : ℕ)^1027*100000000000000^771 ≤ 41986710586997^771*10000000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5212651061 10000000000 41986710586997 100000000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077507409/2000000000 : ℝ)^1027 ≤ (2742092502077/6250000000000 : ℝ)^771 := by
    have hnat : (1077507409 : ℕ)^1027*6250000000000^771 ≤ 2742092502077^771*2000000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077507409 2000000000 2742092502077 6250000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1027/256 : ℝ)) 1027 771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2302566859/10000000000 : ℝ), (5212651061/10000000000 : ℝ), (1077507409/2000000000 : ℝ)] ![(1413980936207/10000000000000 : ℝ), (41986710586997/100000000000000 : ℝ), (2742092502077/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2302566859/10000000000 : ℝ)|^1027 ≤ (1413980936207/10000000000000 : ℝ)^771
        have hw : |(-2302566859/10000000000 : ℝ)|=(2302566859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5212651061/10000000000 : ℝ)|^1027 ≤ (41986710586997/100000000000000 : ℝ)^771
        have hw : |(5212651061/10000000000 : ℝ)|=(5212651061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1077507409/2000000000 : ℝ)|^1027 ≤ (2742092502077/6250000000000 : ℝ)^771
        have hw : |(1077507409/2000000000 : ℝ)|=(1077507409/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1023_box_9 (p : ℝ) (hpa : (8215/2048 : ℝ) ≤ p) (hpb : p ≤ (1027/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5287890337/10000000000 : ℝ)*x 0 + (-1101459963/5000000000 : ℝ)*x 1 + (5387536861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287890337/10000000000 : ℝ)^1027 ≤ (10698974915269/25000000000000 : ℝ)^771 := by
    have hnat : (5287890337 : ℕ)^1027*25000000000000^771 ≤ 10698974915269^771*10000000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287890337 10000000000 10698974915269 25000000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1101459963/5000000000 : ℝ)^1027 ≤ (1333062229399/10000000000000 : ℝ)^771 := by
    have hnat : (1101459963 : ℕ)^1027*10000000000000^771 ≤ 1333062229399^771*5000000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101459963 5000000000 1333062229399 10000000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5387536861/10000000000 : ℝ)^1027 ≤ (438734780373/1000000000000 : ℝ)^771 := by
    have hnat : (5387536861 : ℕ)^1027*1000000000000^771 ≤ 438734780373^771*10000000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387536861 10000000000 438734780373 1000000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1027/256 : ℝ)) 1027 771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287890337/10000000000 : ℝ), (-1101459963/5000000000 : ℝ), (5387536861/10000000000 : ℝ)] ![(10698974915269/25000000000000 : ℝ), (1333062229399/10000000000000 : ℝ), (438734780373/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287890337/10000000000 : ℝ)|^1027 ≤ (10698974915269/25000000000000 : ℝ)^771
        have hw : |(5287890337/10000000000 : ℝ)|=(5287890337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1101459963/5000000000 : ℝ)|^1027 ≤ (1333062229399/10000000000000 : ℝ)^771
        have hw : |(-1101459963/5000000000 : ℝ)|=(1101459963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5387536861/10000000000 : ℝ)|^1027 ≤ (438734780373/1000000000000 : ℝ)^771
        have hw : |(5387536861/10000000000 : ℝ)|=(5387536861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1023_box_10 (p : ℝ) (hpa : (8215/2048 : ℝ) ≤ p) (hpb : p ≤ (1027/256 : ℝ)) (x : Fin 3 → ℝ) :
    (66098629/125000000 : ℝ)*x 0 + (5387536681/10000000000 : ℝ)*x 1 + (-2202920189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66098629/125000000 : ℝ)^1027 ≤ (42795899477809/100000000000000 : ℝ)^771 := by
    have hnat : (66098629 : ℕ)^1027*100000000000000^771 ≤ 42795899477809^771*125000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66098629 125000000 42795899477809 100000000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5387536681/10000000000 : ℝ)^1027 ≤ (21936738042379/50000000000000 : ℝ)^771 := by
    have hnat : (5387536681 : ℕ)^1027*50000000000000^771 ≤ 21936738042379^771*10000000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387536681 10000000000 21936738042379 50000000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2202920189/10000000000 : ℝ)^1027 ≤ (1333062441393/10000000000000 : ℝ)^771 := by
    have hnat : (2202920189 : ℕ)^1027*10000000000000^771 ≤ 1333062441393^771*10000000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2202920189 10000000000 1333062441393 10000000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1027/256 : ℝ)) 1027 771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66098629/125000000 : ℝ), (5387536681/10000000000 : ℝ), (-2202920189/10000000000 : ℝ)] ![(42795899477809/100000000000000 : ℝ), (21936738042379/50000000000000 : ℝ), (1333062441393/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66098629/125000000 : ℝ)|^1027 ≤ (42795899477809/100000000000000 : ℝ)^771
        have hw : |(66098629/125000000 : ℝ)|=(66098629/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5387536681/10000000000 : ℝ)|^1027 ≤ (21936738042379/50000000000000 : ℝ)^771
        have hw : |(5387536681/10000000000 : ℝ)|=(5387536681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2202920189/10000000000 : ℝ)|^1027 ≤ (1333062441393/10000000000000 : ℝ)^771
        have hw : |(-2202920189/10000000000 : ℝ)|=(2202920189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1023_box_11 (p : ℝ) (hpa : (8215/2048 : ℝ) ≤ p) (hpb : p ≤ (1027/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4511573389/10000000000 : ℝ)*x 0 + (4318838157/10000000000 : ℝ)*x 1 + (1079709751/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4511573389/10000000000 : ℝ)^1027 ≤ (8659491418899/25000000000000 : ℝ)^771 := by
    have hnat : (4511573389 : ℕ)^1027*25000000000000^771 ≤ 8659491418899^771*10000000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4511573389 10000000000 8659491418899 25000000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4318838157/10000000000 : ℝ)^1027 ≤ (32681012885403/100000000000000 : ℝ)^771 := by
    have hnat : (4318838157 : ℕ)^1027*100000000000000^771 ≤ 32681012885403^771*10000000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4318838157 10000000000 32681012885403 100000000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1079709751/2500000000 : ℝ)^1027 ≤ (32681021422851/100000000000000 : ℝ)^771 := by
    have hnat : (1079709751 : ℕ)^1027*100000000000000^771 ≤ 32681021422851^771*2500000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079709751 2500000000 32681021422851 100000000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1027/256 : ℝ)) 1027 771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4511573389/10000000000 : ℝ), (4318838157/10000000000 : ℝ), (1079709751/2500000000 : ℝ)] ![(8659491418899/25000000000000 : ℝ), (32681012885403/100000000000000 : ℝ), (32681021422851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4511573389/10000000000 : ℝ)|^1027 ≤ (8659491418899/25000000000000 : ℝ)^771
        have hw : |(4511573389/10000000000 : ℝ)|=(4511573389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4318838157/10000000000 : ℝ)|^1027 ≤ (32681012885403/100000000000000 : ℝ)^771
        have hw : |(4318838157/10000000000 : ℝ)|=(4318838157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1079709751/2500000000 : ℝ)|^1027 ≤ (32681021422851/100000000000000 : ℝ)^771
        have hw : |(1079709751/2500000000 : ℝ)|=(1079709751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1023_box_12 (p : ℝ) (hpa : (8215/2048 : ℝ) ≤ p) (hpb : p ≤ (1027/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-214946511/1000000000 : ℝ)*x 0 + (5443340007/10000000000 : ℝ)*x 1 + (527144207/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214946511/1000000000 : ℝ)^1027 ≤ (12901489268769/100000000000000 : ℝ)^771 := by
    have hnat : (214946511 : ℕ)^1027*100000000000000^771 ≤ 12901489268769^771*1000000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214946511 1000000000 12901489268769 100000000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5443340007/10000000000 : ℝ)^1027 ≤ (5559979836367/12500000000000 : ℝ)^771 := by
    have hnat : (5443340007 : ℕ)^1027*12500000000000^771 ≤ 5559979836367^771*10000000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443340007 10000000000 5559979836367 12500000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (527144207/1000000000 : ℝ)^1027 ≤ (21309336012143/50000000000000 : ℝ)^771 := by
    have hnat : (527144207 : ℕ)^1027*50000000000000^771 ≤ 21309336012143^771*1000000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527144207 1000000000 21309336012143 50000000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1027/256 : ℝ)) 1027 771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-214946511/1000000000 : ℝ), (5443340007/10000000000 : ℝ), (527144207/1000000000 : ℝ)] ![(12901489268769/100000000000000 : ℝ), (5559979836367/12500000000000 : ℝ), (21309336012143/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-214946511/1000000000 : ℝ)|^1027 ≤ (12901489268769/100000000000000 : ℝ)^771
        have hw : |(-214946511/1000000000 : ℝ)|=(214946511/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5443340007/10000000000 : ℝ)|^1027 ≤ (5559979836367/12500000000000 : ℝ)^771
        have hw : |(5443340007/10000000000 : ℝ)|=(5443340007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(527144207/1000000000 : ℝ)|^1027 ≤ (21309336012143/50000000000000 : ℝ)^771
        have hw : |(527144207/1000000000 : ℝ)|=(527144207/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1023_box_13 (p : ℝ) (hpa : (8215/2048 : ℝ) ≤ p) (hpb : p ≤ (1027/256 : ℝ)) (x : Fin 3 → ℝ) :
    (134253409/250000000 : ℝ)*x 0 + (-2248157851/10000000000 : ℝ)*x 1 + (1317860397/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134253409/250000000 : ℝ)^1027 ≤ (43684828159241/100000000000000 : ℝ)^771 := by
    have hnat : (134253409 : ℕ)^1027*100000000000000^771 ≤ 43684828159241^771*250000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134253409 250000000 43684828159241 100000000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2248157851/10000000000 : ℝ)^1027 ≤ (6848252493463/50000000000000 : ℝ)^771 := by
    have hnat : (2248157851 : ℕ)^1027*50000000000000^771 ≤ 6848252493463^771*10000000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248157851 10000000000 6848252493463 50000000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1317860397/2500000000 : ℝ)^1027 ≤ (8523733366699/20000000000000 : ℝ)^771 := by
    have hnat : (1317860397 : ℕ)^1027*20000000000000^771 ≤ 8523733366699^771*2500000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317860397 2500000000 8523733366699 20000000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1027/256 : ℝ)) 1027 771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134253409/250000000 : ℝ), (-2248157851/10000000000 : ℝ), (1317860397/2500000000 : ℝ)] ![(43684828159241/100000000000000 : ℝ), (6848252493463/50000000000000 : ℝ), (8523733366699/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134253409/250000000 : ℝ)|^1027 ≤ (43684828159241/100000000000000 : ℝ)^771
        have hw : |(134253409/250000000 : ℝ)|=(134253409/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2248157851/10000000000 : ℝ)|^1027 ≤ (6848252493463/50000000000000 : ℝ)^771
        have hw : |(-2248157851/10000000000 : ℝ)|=(2248157851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1317860397/2500000000 : ℝ)|^1027 ≤ (8523733366699/20000000000000 : ℝ)^771
        have hw : |(1317860397/2500000000 : ℝ)|=(1317860397/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1023_box_14 (p : ℝ) (hpa : (8215/2048 : ℝ) ≤ p) (hpb : p ≤ (1027/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5370135831/10000000000 : ℝ)*x 0 + (5271441737/10000000000 : ℝ)*x 1 + (-56203959/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370135831/10000000000 : ℝ)^1027 ≤ (21842411213549/50000000000000 : ℝ)^771 := by
    have hnat : (5370135831 : ℕ)^1027*50000000000000^771 ≤ 21842411213549^771*10000000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370135831 10000000000 21842411213549 50000000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5271441737/10000000000 : ℝ)^1027 ≤ (42618668438117/100000000000000 : ℝ)^771 := by
    have hnat : (5271441737 : ℕ)^1027*100000000000000^771 ≤ 42618668438117^771*10000000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271441737 10000000000 42618668438117 100000000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (56203959/250000000 : ℝ)^1027 ≤ (13696509117561/100000000000000 : ℝ)^771 := by
    have hnat : (56203959 : ℕ)^1027*100000000000000^771 ≤ 13696509117561^771*250000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56203959 250000000 13696509117561 100000000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1027/256 : ℝ)) 1027 771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370135831/10000000000 : ℝ), (5271441737/10000000000 : ℝ), (-56203959/250000000 : ℝ)] ![(21842411213549/50000000000000 : ℝ), (42618668438117/100000000000000 : ℝ), (13696509117561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370135831/10000000000 : ℝ)|^1027 ≤ (21842411213549/50000000000000 : ℝ)^771
        have hw : |(5370135831/10000000000 : ℝ)|=(5370135831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5271441737/10000000000 : ℝ)|^1027 ≤ (42618668438117/100000000000000 : ℝ)^771
        have hw : |(5271441737/10000000000 : ℝ)|=(5271441737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-56203959/250000000 : ℝ)|^1027 ≤ (13696509117561/100000000000000 : ℝ)^771
        have hw : |(-56203959/250000000 : ℝ)|=(56203959/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1023_box_15 (p : ℝ) (hpa : (8215/2048 : ℝ) ≤ p) (hpb : p ≤ (1027/256 : ℝ)) (x : Fin 3 → ℝ) :
    (850924361/2000000000 : ℝ)*x 0 + (444731113/1000000000 : ℝ)*x 1 + (4447311933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (850924361/2000000000 : ℝ)^1027 ≤ (6407067773633/20000000000000 : ℝ)^771 := by
    have hnat : (850924361 : ℕ)^1027*20000000000000^771 ≤ 6407067773633^771*2000000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850924361 2000000000 6407067773633 20000000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (444731113/1000000000 : ℝ)^1027 ≤ (33982326477527/100000000000000 : ℝ)^771 := by
    have hnat : (444731113 : ℕ)^1027*100000000000000^771 ≤ 33982326477527^771*1000000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      444731113 1000000000 33982326477527 100000000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4447311933/10000000000 : ℝ)^1027 ≤ (6796466930127/20000000000000 : ℝ)^771 := by
    have hnat : (4447311933 : ℕ)^1027*20000000000000^771 ≤ 6796466930127^771*10000000000^1027 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4447311933 10000000000 6796466930127 20000000000000 1027 771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1027/256 : ℝ)) 1027 771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(850924361/2000000000 : ℝ), (444731113/1000000000 : ℝ), (4447311933/10000000000 : ℝ)] ![(6407067773633/20000000000000 : ℝ), (33982326477527/100000000000000 : ℝ), (6796466930127/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(850924361/2000000000 : ℝ)|^1027 ≤ (6407067773633/20000000000000 : ℝ)^771
        have hw : |(850924361/2000000000 : ℝ)|=(850924361/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(444731113/1000000000 : ℝ)|^1027 ≤ (33982326477527/100000000000000 : ℝ)^771
        have hw : |(444731113/1000000000 : ℝ)|=(444731113/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4447311933/10000000000 : ℝ)|^1027 ≤ (6796466930127/20000000000000 : ℝ)^771
        have hw : |(4447311933/10000000000 : ℝ)|=(4447311933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1023_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8215/2048 : ℝ) ≤ p) (hpb : p ≤ (1027/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147157257/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (559/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11191/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62223/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59209/100000 : ℝ) ∧ (19859/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (41427/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (559/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11191/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (559/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11191/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (559/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11191/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (559/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11191/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (559/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11191/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (559/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11191/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11191/100000 : ℝ) ^ (8215/2048 : ℝ) ≤ (15303611596135437/100000000000000000000 : ℝ) := by
    have hpowers : (11191/100000 : ℝ)^8215 ≤ (15303611596135437/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11191 : ℕ)^8215*100000000000000000000^2048 ≤ 15303611596135437^2048*100000^8215 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11191 100000 15303611596135437 100000000000000000000 8215 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11191/100000 : ℝ)) (X := (15303611596135437/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8215 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (559/4000 : ℝ) ^ (8215/2048 : ℝ) ≤ (9327154596211823/25000000000000000000 : ℝ) := by
    have hpowers : (559/4000 : ℝ)^8215 ≤ (9327154596211823/25000000000000000000 : ℝ)^2048 := by
      have hnat : (559 : ℕ)^8215*25000000000000000000^2048 ≤ 9327154596211823^2048*4000^8215 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        559 4000 9327154596211823 25000000000000000000 8215 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (559/4000 : ℝ)) (X := (9327154596211823/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8215 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50015303611596135437/50000000000000000000 : ℝ) ≤ (2500190737653771/2500000000000000 : ℝ) ^ (8215/2048 : ℝ) := by
    have hpowers : (50015303611596135437/50000000000000000000 : ℝ)^2048 ≤ (2500190737653771/2500000000000000 : ℝ)^8215 := by
      have hnat : (50015303611596135437 : ℕ)^2048*2500000000000000^8215 ≤ 2500190737653771^8215*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015303611596135437 50000000000000000000 2500190737653771 2500000000000000 2048 8215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500190737653771/2500000000000000 : ℝ)) (X := (50015303611596135437/50000000000000000000 : ℝ)) (by norm_num) 8215 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100052612229980982729/100000000000000000000 : ℝ) ≤ (5000655682136903/5000000000000000 : ℝ) ^ (8215/2048 : ℝ) := by
    have hpowers : (100052612229980982729/100000000000000000000 : ℝ)^2048 ≤ (5000655682136903/5000000000000000 : ℝ)^8215 := by
      have hnat : (100052612229980982729 : ℕ)^2048*5000000000000000^8215 ≤ 5000655682136903^8215*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052612229980982729 100000000000000000000 5000655682136903 5000000000000000 2048 8215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000655682136903/5000000000000000 : ℝ)) (X := (100052612229980982729/100000000000000000000 : ℝ)) (by norm_num) 8215 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509327154596211823/12500000000000000000 : ℝ) ≤ (625116236120783/625000000000000 : ℝ) ^ (8215/2048 : ℝ) := by
    have hpowers : (12509327154596211823/12500000000000000000 : ℝ)^2048 ≤ (625116236120783/625000000000000 : ℝ)^8215 := by
      have hnat : (12509327154596211823 : ℕ)^2048*625000000000000^8215 ≤ 625116236120783^8215*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509327154596211823 12500000000000000000 625116236120783 625000000000000 2048 8215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625116236120783/625000000000000 : ℝ)) (X := (12509327154596211823/12500000000000000000 : ℝ)) (by norm_num) 8215 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15303611596135437/100000000000000000000 : ℝ) ≤ ((239912495344852397/240000000000000000 : ℝ)+2*(9455407909/4800000000000 : ℝ)*(11191/100000 : ℝ))^(8215/2048 : ℝ) := by
    rw [show (239912495344852397/240000000000000000 : ℝ)+2*(9455407909/4800000000000 : ℝ)*(11191/100000 : ℝ)=(2500190737653771/2500000000000000 : ℝ) by norm_num, show 1+2*(15303611596135437/100000000000000000000 : ℝ)=(50015303611596135437/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9327154596211823/25000000000000000000 : ℝ)+(15303611596135437/100000000000000000000 : ℝ) ≤ ((239912495344852397/240000000000000000 : ℝ)+(9455407909/4800000000000 : ℝ)*((559/4000 : ℝ)+(11191/100000 : ℝ)))^(8215/2048 : ℝ) := by
    rw [show (239912495344852397/240000000000000000 : ℝ)+(9455407909/4800000000000 : ℝ)*((559/4000 : ℝ)+(11191/100000 : ℝ))=(5000655682136903/5000000000000000 : ℝ) by norm_num, show 1+(9327154596211823/25000000000000000000 : ℝ)+(15303611596135437/100000000000000000000 : ℝ)=(100052612229980982729/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9327154596211823/25000000000000000000 : ℝ) ≤ ((239912495344852397/240000000000000000 : ℝ)+2*(9455407909/4800000000000 : ℝ)*(559/4000 : ℝ))^(8215/2048 : ℝ) := by
    rw [show (239912495344852397/240000000000000000 : ℝ)+2*(9455407909/4800000000000 : ℝ)*(559/4000 : ℝ)=(625116236120783/625000000000000 : ℝ) by norm_num, show 1+2*(9327154596211823/25000000000000000000 : ℝ)=(12509327154596211823/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (239912495344852397/240000000000000000 : ℝ)*(X 1 0+X 2 0)+(9455407909/4800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8215/2048 : ℝ)) (lo := (11191/100000 : ℝ)) (hi := (559/4000 : ℝ)) (c := (239912495344852397/240000000000000000 : ℝ)) (alpha := (9455407909/4800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (239912495344852397/240000000000000000 : ℝ)*(X 0 1+X 2 1)+(9455407909/4800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8215/2048 : ℝ)) (lo := (11191/100000 : ℝ)) (hi := (559/4000 : ℝ)) (c := (239912495344852397/240000000000000000 : ℝ)) (alpha := (9455407909/4800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (239912495344852397/240000000000000000 : ℝ)*(X 0 2+X 1 2)+(9455407909/4800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8215/2048 : ℝ)) (lo := (11191/100000 : ℝ)) (hi := (559/4000 : ℝ)) (c := (239912495344852397/240000000000000000 : ℝ)) (alpha := (9455407909/4800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-523537309/2500000000 : ℝ)*X 0 0+(672242803/1250000000 : ℝ)*X 0 1+(1075588497/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1023_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5294690947/10000000000 : ℝ)*X 1 0+(-551682353/2500000000 : ℝ)*X 1 1+(2688971201/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1023_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5294690587/10000000000 : ℝ)*X 2 0+(5377942691/10000000000 : ℝ)*X 2 1+(-441345901/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1023_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4490607847/10000000000 : ℝ)*X 0 0+(432946199/1000000000 : ℝ)*X 0 1+(865892351/2000000000 : ℝ)*X 0 2+(4490607847/10000000000 : ℝ)*X 1 0+(432946199/1000000000 : ℝ)*X 1 1+(865892351/2000000000 : ℝ)*X 1 2+(4490607847/10000000000 : ℝ)*X 2 0+(432946199/1000000000 : ℝ)*X 2 1+(865892351/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1023_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1178742133/5000000000 : ℝ)*X 0 0+(1319854767/2500000000 : ℝ)*X 0 1+(82490927/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1023_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1072897409/2000000000 : ℝ)*X 1 0+(-561277567/2500000000 : ℝ)*X 1 1+(13198547/25000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1023_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5364486297/10000000000 : ℝ)*X 2 0+(1319854879/2500000000 : ℝ)*X 2 1+(-561277579/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1023_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((854501897/2000000000 : ℝ)*X 0 0+(4438489039/10000000000 : ℝ)*X 0 1+(443848939/1000000000 : ℝ)*X 0 2+(854501897/2000000000 : ℝ)*X 1 0+(4438489039/10000000000 : ℝ)*X 1 1+(443848939/1000000000 : ℝ)*X 1 2+(854501897/2000000000 : ℝ)*X 2 0+(4438489039/10000000000 : ℝ)*X 2 1+(443848939/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1023_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2302566859/10000000000 : ℝ)*X 0 0+(5212651061/10000000000 : ℝ)*X 0 1+(1077507409/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1023_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5287890337/10000000000 : ℝ)*X 1 0+(-1101459963/5000000000 : ℝ)*X 1 1+(5387536861/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1023_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((66098629/125000000 : ℝ)*X 2 0+(5387536681/10000000000 : ℝ)*X 2 1+(-2202920189/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1023_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4511573389/10000000000 : ℝ)*X 0 0+(4318838157/10000000000 : ℝ)*X 0 1+(1079709751/2500000000 : ℝ)*X 0 2+(4511573389/10000000000 : ℝ)*X 1 0+(4318838157/10000000000 : ℝ)*X 1 1+(1079709751/2500000000 : ℝ)*X 1 2+(4511573389/10000000000 : ℝ)*X 2 0+(4318838157/10000000000 : ℝ)*X 2 1+(1079709751/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1023_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-214946511/1000000000 : ℝ)*X 0 0+(5443340007/10000000000 : ℝ)*X 0 1+(527144207/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1023_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((134253409/250000000 : ℝ)*X 1 0+(-2248157851/10000000000 : ℝ)*X 1 1+(1317860397/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1023_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5370135831/10000000000 : ℝ)*X 2 0+(5271441737/10000000000 : ℝ)*X 2 1+(-56203959/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1023_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((850924361/2000000000 : ℝ)*X 0 0+(444731113/1000000000 : ℝ)*X 0 1+(4447311933/10000000000 : ℝ)*X 0 2+(850924361/2000000000 : ℝ)*X 1 0+(444731113/1000000000 : ℝ)*X 1 1+(4447311933/10000000000 : ℝ)*X 1 2+(850924361/2000000000 : ℝ)*X 2 0+(444731113/1000000000 : ℝ)*X 2 1+(4447311933/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1023_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62223/100000 : ℝ) ≤ (-1244411416731048724442904912207/2000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (48484623/25000000000000 : ℝ)*(upper1) + (74509639/25000000000000 : ℝ)*(upper2) + (34799221/100000000000000 : ℝ)*(lower4) + (235439741/100000000000000 : ℝ)*(upper5) + (190996856341927/5000000000000 : ℝ)*(major0) + (190996856341927/5000000000000 : ℝ)*(major1) + (1909968563419271/50000000000000 : ℝ)*(major2) + (3729191131/50000000000000 : ℝ)*(sp1) + (173298073/20000000000000 : ℝ)*(sp2) + (12964245947/100000000000000 : ℝ)*(sp3) + (1266198675854769/25000000000000 : ℝ)*(sp4) + (5064787245036813/100000000000000 : ℝ)*(sp5) + (5064793836928711/100000000000000 : ℝ)*(sp6) + (25958067762909/1000000000000 : ℝ)*(sp7) + (2595819740536847/100000000000000 : ℝ)*(f.failure) + (1266198675854769/25000000000000 : ℝ)*(f.sum) + (65759855483/80000000000000000000000000 : ℝ)*base65 + (3183027902785327/400000000000000000000000000000 : ℝ)*base68 + (60171490161947529/4000000000000000000000000000000 : ℝ)*base69 + (265372506785327/400000000000000000000000000000 : ℝ)*base72 + (57731297237/80000000000000000000000000 : ℝ)*base74 + (72729662977947529/4000000000000000000000000000000 : ℝ)*base75 + (8347831827500981/1200000000000000000000000000000 : ℝ)*base78 + (8394506655500981/1200000000000000000000000000000 : ℝ)*base80 + (4736954233/2400000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (111948679/10000000000000000000000 : ℝ)*base89 + (111948679/10000000000000000000000 : ℝ)*base91 + (88051321/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59209/100000 : ℝ) ≤ (296057536575141523904168880121/500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (124451347/100000000000000 : ℝ)*(upper1) + (285983603/100000000000000 : ℝ)*(upper2) + (5057401/50000000000000 : ℝ)*(upper3) + (147766279/100000000000000 : ℝ)*(upper4) + (776422116765691/20000000000000 : ℝ)*(major0) + (776422116765691/20000000000000 : ℝ)*(major1) + (485263822978557/12500000000000 : ℝ)*(major2) + (1021282917395557/20000000000000 : ℝ)*(sp0) + (5106407283824609/100000000000000 : ℝ)*(sp1) + (5106400748480397/100000000000000 : ℝ)*(sp2) + (65951440003833/2500000000000 : ℝ)*(sp3) + (292126127/4000000000000 : ℝ)*(sp5) + (13838497387/100000000000000 : ℝ)*(sp6) + (11811420759/100000000000000 : ℝ)*(sp11) + (8243966911169/312500000000 : ℝ)*(f.failure) + (1021282917395557/20000000000000 : ℝ)*(f.sum) + (2400713865781/480000000000000000000000000 : ℝ)*base66 + (38427078240648673/4800000000000000000000000000000 : ℝ)*base68 + (233529049044269879/3000000000000000000000000000000 : ℝ)*base69 + (500505122946551327/4800000000000000000000000000000 : ℝ)*base71 + (91647525301/480000000000000000000000000 : ℝ)*base74 + (2096553765269879/3000000000000000000000000000000 : ℝ)*base75 + (192879813756538673/4800000000000000000000000000000 : ℝ)*base78 + (11644693221061327/4800000000000000000000000000000 : ℝ)*base79 + (3864949112887/48000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (515933/31250000000000000000 : ℝ)*base89 + (515933/31250000000000000000 : ℝ)*base91 + (203433/31250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (19859/25000 : ℝ) ≤ (794381950548518593570048116507/1000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (54082033/25000000000000 : ℝ)*(upper0) + (24642059/20000000000000 : ℝ)*(upper2) + (83073199/50000000000000 : ℝ)*(lower3) + (218887691/100000000000000 : ℝ)*(lower5) + (1087595637517369/25000000000000 : ℝ)*(major0) + (1087595637517369/25000000000000 : ℝ)*(major1) + (1087595637517369/25000000000000 : ℝ)*(major2) + (83440814293/50000000000000 : ℝ)*(sp1) + (745517019/12500000000000 : ℝ)*(sp4) + (228719815794179/4000000000000 : ℝ)*(sp8) + (1429459366485217/25000000000000 : ℝ)*(sp9) + (2859002173784727/50000000000000 : ℝ)*(sp10) + (1478140677108937/50000000000000 : ℝ)*(sp11) + (747144707/25000000000000 : ℝ)*(sp12) + (1478140677108937/50000000000000 : ℝ)*(f.failure) + (2859002173784727/50000000000000 : ℝ)*(f.sum) + (497506655519/60000000000000000000000000 : ℝ)*base66 + (103865930449833493/6000000000000000000000000000000 : ℝ)*base67 + (18312894277833493/6000000000000000000000000000000 : ℝ)*base69 + (9402085735833493/6000000000000000000000000000000 : ℝ)*base71 + (259076810341/60000000000000000000000000 : ℝ)*base73 + (16562857903833493/6000000000000000000000000000000 : ℝ)*base75 + (14076405196166507/6000000000000000000000000000000 : ℝ)*base78 + (16303725952166507/6000000000000000000000000000000 : ℝ)*base80 + (177036430021/60000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (59105809/5000000000000000000000 : ℝ)*base89 + (59105809/5000000000000000000000 : ℝ)*base91 + (59105809/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-41427/50000 : ℝ) ≤ (-33140499594894230234424073/40000000000000000000000000 : ℝ) := by norm_num
    linear_combination (94889399/50000000000000 : ℝ)*(lower0) + (8178261/4000000000000 : ℝ)*(lower1) + (220136097/50000000000000 : ℝ)*(lower4) + (2192358519584677/50000000000000 : ℝ)*(major0) + (2192358519584677/50000000000000 : ℝ)*(major1) + (876943407833871/20000000000000 : ℝ)*(major2) + (7855514533/50000000000000 : ℝ)*(sp0) + (817553987147/100000000000000 : ℝ)*(sp5) + (52605376467/5000000000000 : ℝ)*(sp6) + (91402766049/50000000000000 : ℝ)*(sp7) + (1454355565151917/25000000000000 : ℝ)*(sp12) + (5816620417649587/100000000000000 : ℝ)*(sp13) + (2908192932053697/50000000000000 : ℝ)*(sp14) + (297943038416561/10000000000000 : ℝ)*(sp15) + (2979613189697709/100000000000000 : ℝ)*(f.failure) + (2908718985818367/50000000000000 : ℝ)*(f.sum) + (2700938557961/480000000000000000000000000 : ℝ)*base65 + (62996695358704231/12000000000000000000000000000000 : ℝ)*base68 + (25524418823998787/4800000000000000000000000000000 : ℝ)*base69 + (2963863845295769/12000000000000000000000000000000 : ℝ)*base71 + (10493931041239/480000000000000000000000000 : ℝ)*base74 + (17588825908801213/4800000000000000000000000000000 : ℝ)*base76 + (35833145139570769/12000000000000000000000000000000 : ℝ)*base77 + (507552678452429231/12000000000000000000000000000000 : ℝ)*base80 + (372731521993/120000000000000000000000000 : ℝ)*base81 + (115624213/10000000000000000000000 : ℝ)*base89 + (115624213/10000000000000000000000 : ℝ)*base91 + (15624213/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1023_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8215/2048 : ℝ) ≤ p) (hpb : p ≤ (1027/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147157257/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (559/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11191/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59209/100000 : ℝ) else (19859/25000 : ℝ) ≤ X j i ∧ X j i ≤ (41427/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1023_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8215/2048 : ℝ) ≤ p) (hpb : p ≤ (1027/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147157257/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (559/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11191/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59209/100000 : ℝ) else (19859/25000 : ℝ) ≤ X j i ∧ X j i ≤ (41427/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_w1023_box p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

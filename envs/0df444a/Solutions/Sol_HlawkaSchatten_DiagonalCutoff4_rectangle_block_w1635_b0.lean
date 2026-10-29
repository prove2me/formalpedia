-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1635_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:00:59.036619+00:00
-- url     : https://prove2.me/submissions/2b997d94-04ed-437a-9434-e97e3e4cd1ba

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
theorem support_rectangle_w1635_s0_0 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-189918291/1250000000 : ℝ)*x 0 + (2902096591/5000000000 : ℝ)*x 1 + (4911180349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (189918291/1250000000 : ℝ)^4859 ≤ (9186443422483/100000000000000 : ℝ)^3835 := by
    have hnat : (189918291 : ℕ)^4859*100000000000000^3835 ≤ 9186443422483^3835*1250000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      189918291 1250000000 9186443422483 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2902096591/5000000000 : ℝ)^4859 ≤ (50194663448369/100000000000000 : ℝ)^3835 := by
    have hnat : (2902096591 : ℕ)^4859*100000000000000^3835 ≤ 50194663448369^3835*5000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2902096591 5000000000 50194663448369 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4911180349/10000000000 : ℝ)^4859 ≤ (40618893108703/100000000000000 : ℝ)^3835 := by
    have hnat : (4911180349 : ℕ)^4859*100000000000000^3835 ≤ 40618893108703^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4911180349 10000000000 40618893108703 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-189918291/1250000000 : ℝ), (2902096591/5000000000 : ℝ), (4911180349/10000000000 : ℝ)] ![(9186443422483/100000000000000 : ℝ), (50194663448369/100000000000000 : ℝ), (40618893108703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-189918291/1250000000 : ℝ)|^4859 ≤ (9186443422483/100000000000000 : ℝ)^3835
        have hw : |(-189918291/1250000000 : ℝ)|=(189918291/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2902096591/5000000000 : ℝ)|^4859 ≤ (50194663448369/100000000000000 : ℝ)^3835
        have hw : |(2902096591/5000000000 : ℝ)|=(2902096591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4911180349/10000000000 : ℝ)|^4859 ≤ (40618893108703/100000000000000 : ℝ)^3835
        have hw : |(4911180349/10000000000 : ℝ)|=(4911180349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1635_s0_1 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1360882471/2500000000 : ℝ)*x 0 + (-2011083597/10000000000 : ℝ)*x 1 + (306948877/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1360882471/2500000000 : ℝ)^4859 ≤ (23138060439239/50000000000000 : ℝ)^3835 := by
    have hnat : (1360882471 : ℕ)^4859*50000000000000^3835 ≤ 23138060439239^3835*2500000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360882471 2500000000 23138060439239 50000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2011083597/10000000000 : ℝ)^4859 ≤ (13104968365161/100000000000000 : ℝ)^3835 := by
    have hnat : (2011083597 : ℕ)^4859*100000000000000^3835 ≤ 13104968365161^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011083597 10000000000 13104968365161 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (306948877/625000000 : ℝ)^4859 ≤ (40618910745019/100000000000000 : ℝ)^3835 := by
    have hnat : (306948877 : ℕ)^4859*100000000000000^3835 ≤ 40618910745019^3835*625000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      306948877 625000000 40618910745019 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1360882471/2500000000 : ℝ), (-2011083597/10000000000 : ℝ), (306948877/625000000 : ℝ)] ![(23138060439239/50000000000000 : ℝ), (13104968365161/100000000000000 : ℝ), (40618910745019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1360882471/2500000000 : ℝ)|^4859 ≤ (23138060439239/50000000000000 : ℝ)^3835
        have hw : |(1360882471/2500000000 : ℝ)|=(1360882471/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2011083597/10000000000 : ℝ)|^4859 ≤ (13104968365161/100000000000000 : ℝ)^3835
        have hw : |(-2011083597/10000000000 : ℝ)|=(2011083597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(306948877/625000000 : ℝ)|^4859 ≤ (40618910745019/100000000000000 : ℝ)^3835
        have hw : |(306948877/625000000 : ℝ)|=(306948877/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1635_s0_2 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (544353109/1000000000 : ℝ)*x 0 + (4911180637/10000000000 : ℝ)*x 1 + (-1005541897/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544353109/1000000000 : ℝ)^4859 ≤ (1156903346709/2500000000000 : ℝ)^3835 := by
    have hnat : (544353109 : ℕ)^4859*2500000000000^3835 ≤ 1156903346709^3835*1000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544353109 1000000000 1156903346709 2500000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4911180637/10000000000 : ℝ)^4859 ≤ (20309448063341/50000000000000 : ℝ)^3835 := by
    have hnat : (4911180637 : ℕ)^4859*50000000000000^3835 ≤ 20309448063341^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4911180637 10000000000 20309448063341 50000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1005541897/5000000000 : ℝ)^4859 ≤ (13104969991659/100000000000000 : ℝ)^3835 := by
    have hnat : (1005541897 : ℕ)^4859*100000000000000^3835 ≤ 13104969991659^3835*5000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005541897 5000000000 13104969991659 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(544353109/1000000000 : ℝ), (4911180637/10000000000 : ℝ), (-1005541897/5000000000 : ℝ)] ![(1156903346709/2500000000000 : ℝ), (20309448063341/50000000000000 : ℝ), (13104969991659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(544353109/1000000000 : ℝ)|^4859 ≤ (1156903346709/2500000000000 : ℝ)^3835
        have hw : |(544353109/1000000000 : ℝ)|=(544353109/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4911180637/10000000000 : ℝ)|^4859 ≤ (20309448063341/50000000000000 : ℝ)^3835
        have hw : |(4911180637/10000000000 : ℝ)|=(4911180637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1005541897/5000000000 : ℝ)|^4859 ≤ (13104969991659/100000000000000 : ℝ)^3835
        have hw : |(-1005541897/5000000000 : ℝ)|=(1005541897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1635_s0_3 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4097696603/10000000000 : ℝ)*x 0 + (307909357/1000000000 : ℝ)*x 1 + (106918753/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4097696603/10000000000 : ℝ)^4859 ≤ (6458213009113/20000000000000 : ℝ)^3835 := by
    have hnat : (4097696603 : ℕ)^4859*20000000000000^3835 ≤ 6458213009113^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4097696603 10000000000 6458213009113 20000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (307909357/1000000000 : ℝ)^4859 ≤ (112407286749/500000000000 : ℝ)^3835 := by
    have hnat : (307909357 : ℕ)^4859*500000000000^3835 ≤ 112407286749^3835*1000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      307909357 1000000000 112407286749 500000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (106918753/200000000 : ℝ)^4859 ≤ (45227477589381/100000000000000 : ℝ)^3835 := by
    have hnat : (106918753 : ℕ)^4859*100000000000000^3835 ≤ 45227477589381^3835*200000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106918753 200000000 45227477589381 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4097696603/10000000000 : ℝ), (307909357/1000000000 : ℝ), (106918753/200000000 : ℝ)] ![(6458213009113/20000000000000 : ℝ), (112407286749/500000000000 : ℝ), (45227477589381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4097696603/10000000000 : ℝ)|^4859 ≤ (6458213009113/20000000000000 : ℝ)^3835
        have hw : |(4097696603/10000000000 : ℝ)|=(4097696603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(307909357/1000000000 : ℝ)|^4859 ≤ (112407286749/500000000000 : ℝ)^3835
        have hw : |(307909357/1000000000 : ℝ)|=(307909357/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(106918753/200000000 : ℝ)|^4859 ≤ (45227477589381/100000000000000 : ℝ)^3835
        have hw : |(106918753/200000000 : ℝ)|=(106918753/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1635_s0_4 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1521817749/10000000000 : ℝ)*x 0 + (38543023/78125000 : ℝ)*x 1 + (722635893/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1521817749/10000000000 : ℝ)^4859 ≤ (9205380508609/100000000000000 : ℝ)^3835 := by
    have hnat : (1521817749 : ℕ)^4859*100000000000000^3835 ≤ 9205380508609^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1521817749 10000000000 9205380508609 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (38543023/78125000 : ℝ)^4859 ≤ (20426498718393/50000000000000 : ℝ)^3835 := by
    have hnat : (38543023 : ℕ)^4859*50000000000000^3835 ≤ 20426498718393^3835*78125000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38543023 78125000 20426498718393 50000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (722635893/1250000000 : ℝ)^4859 ≤ (12485405510001/25000000000000 : ℝ)^3835 := by
    have hnat : (722635893 : ℕ)^4859*25000000000000^3835 ≤ 12485405510001^3835*1250000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      722635893 1250000000 12485405510001 25000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1521817749/10000000000 : ℝ), (38543023/78125000 : ℝ), (722635893/1250000000 : ℝ)] ![(9205380508609/100000000000000 : ℝ), (20426498718393/50000000000000 : ℝ), (12485405510001/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1521817749/10000000000 : ℝ)|^4859 ≤ (9205380508609/100000000000000 : ℝ)^3835
        have hw : |(-1521817749/10000000000 : ℝ)|=(1521817749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(38543023/78125000 : ℝ)|^4859 ≤ (20426498718393/50000000000000 : ℝ)^3835
        have hw : |(38543023/78125000 : ℝ)|=(38543023/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(722635893/1250000000 : ℝ)|^4859 ≤ (12485405510001/25000000000000 : ℝ)^3835
        have hw : |(722635893/1250000000 : ℝ)|=(722635893/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1635_s0_5 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2599871103/5000000000 : ℝ)*x 0 + (-1141179083/10000000000 : ℝ)*x 1 + (5781085307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2599871103/5000000000 : ℝ)^4859 ≤ (8733229618083/20000000000000 : ℝ)^3835 := by
    have hnat : (2599871103 : ℕ)^4859*20000000000000^3835 ≤ 8733229618083^3835*5000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2599871103 5000000000 8733229618083 20000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1141179083/10000000000 : ℝ)^4859 ≤ (6392249958837/100000000000000 : ℝ)^3835 := by
    have hnat : (1141179083 : ℕ)^4859*100000000000000^3835 ≤ 6392249958837^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1141179083 10000000000 6392249958837 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5781085307/10000000000 : ℝ)^4859 ≤ (9988320386633/20000000000000 : ℝ)^3835 := by
    have hnat : (5781085307 : ℕ)^4859*20000000000000^3835 ≤ 9988320386633^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5781085307 10000000000 9988320386633 20000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2599871103/5000000000 : ℝ), (-1141179083/10000000000 : ℝ), (5781085307/10000000000 : ℝ)] ![(8733229618083/20000000000000 : ℝ), (6392249958837/100000000000000 : ℝ), (9988320386633/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2599871103/5000000000 : ℝ)|^4859 ≤ (8733229618083/20000000000000 : ℝ)^3835
        have hw : |(2599871103/5000000000 : ℝ)|=(2599871103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1141179083/10000000000 : ℝ)|^4859 ≤ (6392249958837/100000000000000 : ℝ)^3835
        have hw : |(-1141179083/10000000000 : ℝ)|=(1141179083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5781085307/10000000000 : ℝ)|^4859 ≤ (9988320386633/20000000000000 : ℝ)^3835
        have hw : |(5781085307/10000000000 : ℝ)|=(5781085307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1635_s0_6 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5199743023/10000000000 : ℝ)*x 0 + (1156216837/2000000000 : ℝ)*x 1 + (-1141179589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5199743023/10000000000 : ℝ)^4859 ≤ (8733231356671/20000000000000 : ℝ)^3835 := by
    have hnat : (5199743023 : ℕ)^4859*20000000000000^3835 ≤ 8733231356671^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5199743023 10000000000 8733231356671 20000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1156216837/2000000000 : ℝ)^4859 ≤ (49941589652343/100000000000000 : ℝ)^3835 := by
    have hnat : (1156216837 : ℕ)^4859*100000000000000^3835 ≤ 49941589652343^3835*2000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1156216837 2000000000 49941589652343 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1141179589/10000000000 : ℝ)^4859 ≤ (3196126774987/50000000000000 : ℝ)^3835 := by
    have hnat : (1141179589 : ℕ)^4859*50000000000000^3835 ≤ 3196126774987^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1141179589 10000000000 3196126774987 50000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5199743023/10000000000 : ℝ), (1156216837/2000000000 : ℝ), (-1141179589/10000000000 : ℝ)] ![(8733231356671/20000000000000 : ℝ), (49941589652343/100000000000000 : ℝ), (3196126774987/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5199743023/10000000000 : ℝ)|^4859 ≤ (8733231356671/20000000000000 : ℝ)^3835
        have hw : |(5199743023/10000000000 : ℝ)|=(5199743023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1156216837/2000000000 : ℝ)|^4859 ≤ (49941589652343/100000000000000 : ℝ)^3835
        have hw : |(1156216837/2000000000 : ℝ)|=(1156216837/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1141179589/10000000000 : ℝ)|^4859 ≤ (3196126774987/50000000000000 : ℝ)^3835
        have hw : |(-1141179589/10000000000 : ℝ)|=(1141179589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1635_s0_7 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4103973051/10000000000 : ℝ)*x 0 + (2644629561/5000000000 : ℝ)*x 1 + (3137750639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4103973051/10000000000 : ℝ)^4859 ≤ (404421809129/1250000000000 : ℝ)^3835 := by
    have hnat : (4103973051 : ℕ)^4859*1250000000000^3835 ≤ 404421809129^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4103973051 10000000000 404421809129 1250000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2644629561/5000000000 : ℝ)^4859 ≤ (22310397309147/50000000000000 : ℝ)^3835 := by
    have hnat : (2644629561 : ℕ)^4859*50000000000000^3835 ≤ 22310397309147^3835*5000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644629561 5000000000 22310397309147 50000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3137750639/10000000000 : ℝ)^4859 ≤ (4605092128151/20000000000000 : ℝ)^3835 := by
    have hnat : (3137750639 : ℕ)^4859*20000000000000^3835 ≤ 4605092128151^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3137750639 10000000000 4605092128151 20000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4103973051/10000000000 : ℝ), (2644629561/5000000000 : ℝ), (3137750639/10000000000 : ℝ)] ![(404421809129/1250000000000 : ℝ), (22310397309147/50000000000000 : ℝ), (4605092128151/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4103973051/10000000000 : ℝ)|^4859 ≤ (404421809129/1250000000000 : ℝ)^3835
        have hw : |(4103973051/10000000000 : ℝ)|=(4103973051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2644629561/5000000000 : ℝ)|^4859 ≤ (22310397309147/50000000000000 : ℝ)^3835
        have hw : |(2644629561/5000000000 : ℝ)|=(2644629561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3137750639/10000000000 : ℝ)|^4859 ≤ (4605092128151/20000000000000 : ℝ)^3835
        have hw : |(3137750639/10000000000 : ℝ)|=(3137750639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1635_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35384243/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (4547/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (23681/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4855/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4855 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4855*1^1024 ≤ 0^1024*1^4855 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4855 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4855 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4855/1024 : ℝ) ≤ (324505817627976243/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4855 ≤ (324505817627976243/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4855*25000000000000000000^1024 ≤ 324505817627976243^1024*5^4855 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 324505817627976243 25000000000000000000 4855 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (324505817627976243/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4855 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4855/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4855 := by
      have hnat : (1 : ℕ)^1024*1^4855 ≤ 1^4855*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4855 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4855 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25324505817627976243/25000000000000000000 : ℝ) ≤ (10027238331960127/10000000000000000 : ℝ) ^ (4855/1024 : ℝ) := by
    have hpowers : (25324505817627976243/25000000000000000000 : ℝ)^1024 ≤ (10027238331960127/10000000000000000 : ℝ)^4855 := by
      have hnat : (25324505817627976243 : ℕ)^1024*10000000000000000^4855 ≤ 10027238331960127^4855*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25324505817627976243 25000000000000000000 10027238331960127 10000000000000000 1024 4855 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10027238331960127/10000000000000000 : ℝ)) (X := (25324505817627976243/25000000000000000000 : ℝ)) (by norm_num) 4855 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12824505817627976243/12500000000000000000 : ℝ) ≤ (5027238331960127/5000000000000000 : ℝ) ^ (4855/1024 : ℝ) := by
    have hpowers : (12824505817627976243/12500000000000000000 : ℝ)^1024 ≤ (5027238331960127/5000000000000000 : ℝ)^4855 := by
      have hnat : (12824505817627976243 : ℕ)^1024*5000000000000000^4855 ≤ 5027238331960127^4855*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12824505817627976243 12500000000000000000 5027238331960127 5000000000000000 1024 4855 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5027238331960127/5000000000000000 : ℝ)) (X := (12824505817627976243/12500000000000000000 : ℝ)) (by norm_num) 4855 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(27238331960127/4000000000000000 : ℝ)*(0 : ℝ))^(4855/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(27238331960127/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(324505817627976243/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(27238331960127/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4855/1024 : ℝ) := by
    rw [show (1 : ℝ)+(27238331960127/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10027238331960127/10000000000000000 : ℝ) by norm_num, show 1+(324505817627976243/25000000000000000000 : ℝ)+(0 : ℝ)=(25324505817627976243/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(324505817627976243/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(27238331960127/4000000000000000 : ℝ)*(2/5 : ℝ))^(4855/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(27238331960127/4000000000000000 : ℝ)*(2/5 : ℝ)=(5027238331960127/5000000000000000 : ℝ) by norm_num, show 1+2*(324505817627976243/25000000000000000000 : ℝ)=(12824505817627976243/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(27238331960127/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4855/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (27238331960127/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(27238331960127/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4855/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (27238331960127/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(27238331960127/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4855/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (27238331960127/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-189918291/1250000000 : ℝ)*X 0 0+(2902096591/5000000000 : ℝ)*X 0 1+(4911180349/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1360882471/2500000000 : ℝ)*X 1 0+(-2011083597/10000000000 : ℝ)*X 1 1+(306948877/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((544353109/1000000000 : ℝ)*X 2 0+(4911180637/10000000000 : ℝ)*X 2 1+(-1005541897/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4097696603/10000000000 : ℝ)*X 0 0+(307909357/1000000000 : ℝ)*X 0 1+(106918753/200000000 : ℝ)*X 0 2+(4097696603/10000000000 : ℝ)*X 1 0+(307909357/1000000000 : ℝ)*X 1 1+(106918753/200000000 : ℝ)*X 1 2+(4097696603/10000000000 : ℝ)*X 2 0+(307909357/1000000000 : ℝ)*X 2 1+(106918753/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1521817749/10000000000 : ℝ)*X 0 0+(38543023/78125000 : ℝ)*X 0 1+(722635893/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2599871103/5000000000 : ℝ)*X 1 0+(-1141179083/10000000000 : ℝ)*X 1 1+(5781085307/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5199743023/10000000000 : ℝ)*X 2 0+(1156216837/2000000000 : ℝ)*X 2 1+(-1141179589/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4103973051/10000000000 : ℝ)*X 0 0+(2644629561/5000000000 : ℝ)*X 0 1+(3137750639/10000000000 : ℝ)*X 0 2+(4103973051/10000000000 : ℝ)*X 1 0+(2644629561/5000000000 : ℝ)*X 1 1+(3137750639/10000000000 : ℝ)*X 1 2+(4103973051/10000000000 : ℝ)*X 2 0+(2644629561/5000000000 : ℝ)*X 2 1+(3137750639/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1962004364871162114741/312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (264600011/25000000000000 : ℝ)*(base19) + (257162757/20000000000000 : ℝ)*(base23) + (85091293/50000000000000 : ℝ)*(upper3) + (450257/4000000000000 : ℝ)*(upper4) + (37416241/25000000000000 : ℝ)*(upper5) + (2439005906247/312500000000 : ℝ)*(major0) + (2439005906247/312500000000 : ℝ)*(major1) + (2439005906247/312500000000 : ℝ)*(major2) + (1119810588662481/100000000000000 : ℝ)*(sp0) + (1119815931903771/100000000000000 : ℝ)*(sp1) + (111981570449003/10000000000000 : ℝ)*(sp2) + (441144100723987/100000000000000 : ℝ)*(sp3) + (3200820667/50000000000000 : ℝ)*(sp4) + (2479689809/100000000000000 : ℝ)*(sp7) + (110286645103449/25000000000000 : ℝ)*(f.failure) + (223963398060763/20000000000000 : ℝ)*(f.sum) + (1693681090381/625000000000000000000000000 : ℝ)*base66 + (1545030305869/1250000000000000000000000000 : ℝ)*base67 + (4372676369131/1250000000000000000000000000 : ℝ)*base70 + (7318303266631/1250000000000000000000000000 : ℝ)*base72 + (235328114859/39062500000000000000000000 : ℝ)*base73 + (4773984752881/1250000000000000000000000000 : ℝ)*base76 + (379853436631/1250000000000000000000000000 : ℝ)*base78 + (6317121284131/1250000000000000000000000000 : ℝ)*base80 + (46040314859/39062500000000000000000000 : ℝ)*base81 + (445893/500000000000000000000 : ℝ)*base90 + (445893/500000000000000000000 : ℝ)*base92 + (445893/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (66310129555385994927789/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6677837/312500000000 : ℝ)*(base19) + (2273697691/100000000000000 : ℝ)*(base23) + (352836043/100000000000000 : ℝ)*(base32) + (7459741/4000000000000 : ℝ)*(upper3) + (289076309/100000000000000 : ℝ)*(upper5) + (51394354957181/6250000000000 : ℝ)*(major0) + (51394354957181/6250000000000 : ℝ)*(major1) + (51394354957181/6250000000000 : ℝ)*(major2) + (2864196727/50000000000000 : ℝ)*(sp1) + (2346021593/50000000000000 : ℝ)*(sp2) + (589915190897013/50000000000000 : ℝ)*(sp4) + (294955629123183/25000000000000 : ℝ)*(sp5) + (1179823416053149/100000000000000 : ℝ)*(sp6) + (464788270345691/100000000000000 : ℝ)*(sp7) + (232394311590867/50000000000000 : ℝ)*(f.failure) + (589915190897013/50000000000000 : ℝ)*(f.sum) + (6134312234487/12500000000000000000000000000 : ℝ)*base65 + (128150388171987/25000000000000000000000000000 : ℝ)*base67 + (143478176996987/25000000000000000000000000000 : ℝ)*base69 + (241006900096987/25000000000000000000000000000 : ℝ)*base71 + (48173672028013/12500000000000000000000000000 : ℝ)*base74 + (236375539296987/25000000000000000000000000000 : ℝ)*base75 + (178707999121987/25000000000000000000000000000 : ℝ)*base77 + (143009850596987/25000000000000000000000000000 : ℝ)*base79 + (30196154478013/12500000000000000000000000000 : ℝ)*base82 + (5491319/1000000000000000000000 : ℝ)*base90 + (5491319/1000000000000000000000 : ℝ)*base92 + (5491319/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1635_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35384243/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4547/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (23681/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1635_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1635_s1_0 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-815779583/5000000000 : ℝ)*x 0 + (2754009523/5000000000 : ℝ)*x 1 + (256727959/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (815779583/5000000000 : ℝ)^4859 ≤ (10054407658591/100000000000000 : ℝ)^3835 := by
    have hnat : (815779583 : ℕ)^4859*100000000000000^3835 ≤ 10054407658591^3835*5000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      815779583 5000000000 10054407658591 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2754009523/5000000000 : ℝ)^4859 ≤ (46971832061621/100000000000000 : ℝ)^3835 := by
    have hnat : (2754009523 : ℕ)^4859*100000000000000^3835 ≤ 46971832061621^3835*5000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2754009523 5000000000 46971832061621 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (256727959/500000000 : ℝ)^4859 ≤ (21486880131877/50000000000000 : ℝ)^3835 := by
    have hnat : (256727959 : ℕ)^4859*50000000000000^3835 ≤ 21486880131877^3835*500000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256727959 500000000 21486880131877 50000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-815779583/5000000000 : ℝ), (2754009523/5000000000 : ℝ), (256727959/500000000 : ℝ)] ![(10054407658591/100000000000000 : ℝ), (46971832061621/100000000000000 : ℝ), (21486880131877/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-815779583/5000000000 : ℝ)|^4859 ≤ (10054407658591/100000000000000 : ℝ)^3835
        have hw : |(-815779583/5000000000 : ℝ)|=(815779583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2754009523/5000000000 : ℝ)|^4859 ≤ (46971832061621/100000000000000 : ℝ)^3835
        have hw : |(2754009523/5000000000 : ℝ)|=(2754009523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(256727959/500000000 : ℝ)|^4859 ≤ (21486880131877/50000000000000 : ℝ)^3835
        have hw : |(256727959/500000000 : ℝ)|=(256727959/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1635_s1_1 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (670594091/1250000000 : ℝ)*x 0 + (-182611393/1000000000 : ℝ)*x 1 + (2567279479/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (670594091/1250000000 : ℝ)^4859 ≤ (22714626879827/50000000000000 : ℝ)^3835 := by
    have hnat : (670594091 : ℕ)^4859*50000000000000^3835 ≤ 22714626879827^3835*1250000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670594091 1250000000 22714626879827 50000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (182611393/1000000000 : ℝ)^4859 ≤ (2319397663357/20000000000000 : ℝ)^3835 := by
    have hnat : (182611393 : ℕ)^4859*20000000000000^3835 ≤ 2319397663357^3835*1000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182611393 1000000000 2319397663357 20000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2567279479/5000000000 : ℝ)^4859 ≤ (42973757909601/100000000000000 : ℝ)^3835 := by
    have hnat : (2567279479 : ℕ)^4859*100000000000000^3835 ≤ 42973757909601^3835*5000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2567279479 5000000000 42973757909601 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(670594091/1250000000 : ℝ), (-182611393/1000000000 : ℝ), (2567279479/5000000000 : ℝ)] ![(22714626879827/50000000000000 : ℝ), (2319397663357/20000000000000 : ℝ), (42973757909601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(670594091/1250000000 : ℝ)|^4859 ≤ (22714626879827/50000000000000 : ℝ)^3835
        have hw : |(670594091/1250000000 : ℝ)|=(670594091/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-182611393/1000000000 : ℝ)|^4859 ≤ (2319397663357/20000000000000 : ℝ)^3835
        have hw : |(-182611393/1000000000 : ℝ)|=(182611393/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2567279479/5000000000 : ℝ)|^4859 ≤ (42973757909601/100000000000000 : ℝ)^3835
        have hw : |(2567279479/5000000000 : ℝ)|=(2567279479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1635_s1_2 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5364753671/10000000000 : ℝ)*x 0 + (5134557829/10000000000 : ℝ)*x 1 + (-22826427/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364753671/10000000000 : ℝ)^4859 ≤ (11357315969323/25000000000000 : ℝ)^3835 := by
    have hnat : (5364753671 : ℕ)^4859*25000000000000^3835 ≤ 11357315969323^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364753671 10000000000 11357315969323 25000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5134557829/10000000000 : ℝ)^4859 ≤ (21486872968677/50000000000000 : ℝ)^3835 := by
    have hnat : (5134557829 : ℕ)^4859*50000000000000^3835 ≤ 21486872968677^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5134557829 10000000000 21486872968677 50000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (22826427/125000000 : ℝ)^4859 ≤ (2319398033489/20000000000000 : ℝ)^3835 := by
    have hnat : (22826427 : ℕ)^4859*20000000000000^3835 ≤ 2319398033489^3835*125000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22826427 125000000 2319398033489 20000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364753671/10000000000 : ℝ), (5134557829/10000000000 : ℝ), (-22826427/125000000 : ℝ)] ![(11357315969323/25000000000000 : ℝ), (21486872968677/50000000000000 : ℝ), (2319398033489/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364753671/10000000000 : ℝ)|^4859 ≤ (11357315969323/25000000000000 : ℝ)^3835
        have hw : |(5364753671/10000000000 : ℝ)|=(5364753671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5134557829/10000000000 : ℝ)|^4859 ≤ (21486872968677/50000000000000 : ℝ)^3835
        have hw : |(5134557829/10000000000 : ℝ)|=(5134557829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-22826427/125000000 : ℝ)|^4859 ≤ (2319398033489/20000000000000 : ℝ)^3835
        have hw : |(-22826427/125000000 : ℝ)|=(22826427/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1635_s1_3 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4183728017/10000000000 : ℝ)*x 0 + (745917317/2000000000 : ℝ)*x 1 + (4677588113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4183728017/10000000000 : ℝ)^4859 ≤ (16576218385011/50000000000000 : ℝ)^3835 := by
    have hnat : (4183728017 : ℕ)^4859*50000000000000^3835 ≤ 16576218385011^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4183728017 10000000000 16576218385011 50000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (745917317/2000000000 : ℝ)^4859 ≤ (28660776753599/100000000000000 : ℝ)^3835 := by
    have hnat : (745917317 : ℕ)^4859*100000000000000^3835 ≤ 28660776753599^3835*2000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      745917317 2000000000 28660776753599 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4677588113/10000000000 : ℝ)^4859 ≤ (38186786462107/100000000000000 : ℝ)^3835 := by
    have hnat : (4677588113 : ℕ)^4859*100000000000000^3835 ≤ 38186786462107^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4677588113 10000000000 38186786462107 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4183728017/10000000000 : ℝ), (745917317/2000000000 : ℝ), (4677588113/10000000000 : ℝ)] ![(16576218385011/50000000000000 : ℝ), (28660776753599/100000000000000 : ℝ), (38186786462107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4183728017/10000000000 : ℝ)|^4859 ≤ (16576218385011/50000000000000 : ℝ)^3835
        have hw : |(4183728017/10000000000 : ℝ)|=(4183728017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(745917317/2000000000 : ℝ)|^4859 ≤ (28660776753599/100000000000000 : ℝ)^3835
        have hw : |(745917317/2000000000 : ℝ)|=(745917317/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4677588113/10000000000 : ℝ)|^4859 ≤ (38186786462107/100000000000000 : ℝ)^3835
        have hw : |(4677588113/10000000000 : ℝ)|=(4677588113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1635_s1_4 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-101983577/625000000 : ℝ)*x 0 + (5138443103/10000000000 : ℝ)*x 1 + (275203891/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (101983577/625000000 : ℝ)^4859 ≤ (5027899001707/50000000000000 : ℝ)^3835 := by
    have hnat : (101983577 : ℕ)^4859*50000000000000^3835 ≤ 5027899001707^3835*625000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101983577 625000000 5027899001707 50000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5138443103/10000000000 : ℝ)^4859 ≤ (43014950680257/100000000000000 : ℝ)^3835 := by
    have hnat : (5138443103 : ℕ)^4859*100000000000000^3835 ≤ 43014950680257^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5138443103 10000000000 43014950680257 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (275203891/500000000 : ℝ)^4859 ≤ (46929251298683/100000000000000 : ℝ)^3835 := by
    have hnat : (275203891 : ℕ)^4859*100000000000000^3835 ≤ 46929251298683^3835*500000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275203891 500000000 46929251298683 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-101983577/625000000 : ℝ), (5138443103/10000000000 : ℝ), (275203891/500000000 : ℝ)] ![(5027899001707/50000000000000 : ℝ), (43014950680257/100000000000000 : ℝ), (46929251298683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-101983577/625000000 : ℝ)|^4859 ≤ (5027899001707/50000000000000 : ℝ)^3835
        have hw : |(-101983577/625000000 : ℝ)|=(101983577/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5138443103/10000000000 : ℝ)|^4859 ≤ (43014950680257/100000000000000 : ℝ)^3835
        have hw : |(5138443103/10000000000 : ℝ)|=(5138443103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(275203891/500000000 : ℝ)|^4859 ≤ (46929251298683/100000000000000 : ℝ)^3835
        have hw : |(275203891/500000000 : ℝ)|=(275203891/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1635_s1_5 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (526506527/1000000000 : ℝ)*x 0 + (-1456594381/10000000000 : ℝ)*x 1 + (2752039037/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (526506527/1000000000 : ℝ)^4859 ≤ (22181176214029/50000000000000 : ℝ)^3835 := by
    have hnat : (526506527 : ℕ)^4859*50000000000000^3835 ≤ 22181176214029^3835*1000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526506527 1000000000 22181176214029 50000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1456594381/10000000000 : ℝ)^4859 ≤ (870839351071/10000000000000 : ℝ)^3835 := by
    have hnat : (1456594381 : ℕ)^4859*10000000000000^3835 ≤ 870839351071^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1456594381 10000000000 870839351071 10000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2752039037/5000000000 : ℝ)^4859 ≤ (46929254042621/100000000000000 : ℝ)^3835 := by
    have hnat : (2752039037 : ℕ)^4859*100000000000000^3835 ≤ 46929254042621^3835*5000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2752039037 5000000000 46929254042621 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(526506527/1000000000 : ℝ), (-1456594381/10000000000 : ℝ), (2752039037/5000000000 : ℝ)] ![(22181176214029/50000000000000 : ℝ), (870839351071/10000000000000 : ℝ), (46929254042621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(526506527/1000000000 : ℝ)|^4859 ≤ (22181176214029/50000000000000 : ℝ)^3835
        have hw : |(526506527/1000000000 : ℝ)|=(526506527/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1456594381/10000000000 : ℝ)|^4859 ≤ (870839351071/10000000000000 : ℝ)^3835
        have hw : |(-1456594381/10000000000 : ℝ)|=(1456594381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2752039037/5000000000 : ℝ)|^4859 ≤ (46929254042621/100000000000000 : ℝ)^3835
        have hw : |(2752039037/5000000000 : ℝ)|=(2752039037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1635_s1_6 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2632532403/5000000000 : ℝ)*x 0 + (5504078243/10000000000 : ℝ)*x 1 + (-728297397/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2632532403/5000000000 : ℝ)^4859 ≤ (44362347474579/100000000000000 : ℝ)^3835 := by
    have hnat : (2632532403 : ℕ)^4859*100000000000000^3835 ≤ 44362347474579^3835*5000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632532403 5000000000 44362347474579 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5504078243/10000000000 : ℝ)^4859 ≤ (5866156983539/12500000000000 : ℝ)^3835 := by
    have hnat : (5504078243 : ℕ)^4859*12500000000000^3835 ≤ 5866156983539^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5504078243 10000000000 5866156983539 12500000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (728297397/5000000000 : ℝ)^4859 ≤ (8708396639173/100000000000000 : ℝ)^3835 := by
    have hnat : (728297397 : ℕ)^4859*100000000000000^3835 ≤ 8708396639173^3835*5000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      728297397 5000000000 8708396639173 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2632532403/5000000000 : ℝ), (5504078243/10000000000 : ℝ), (-728297397/5000000000 : ℝ)] ![(44362347474579/100000000000000 : ℝ), (5866156983539/12500000000000 : ℝ), (8708396639173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2632532403/5000000000 : ℝ)|^4859 ≤ (44362347474579/100000000000000 : ℝ)^3835
        have hw : |(2632532403/5000000000 : ℝ)|=(2632532403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5504078243/10000000000 : ℝ)|^4859 ≤ (5866156983539/12500000000000 : ℝ)^3835
        have hw : |(5504078243/10000000000 : ℝ)|=(5504078243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-728297397/5000000000 : ℝ)|^4859 ≤ (8708396639173/100000000000000 : ℝ)^3835
        have hw : |(-728297397/5000000000 : ℝ)|=(728297397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1635_s1_7 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4184177001/10000000000 : ℝ)*x 0 + (4667729131/10000000000 : ℝ)*x 1 + (934897669/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4184177001/10000000000 : ℝ)^4859 ≤ (33156944632201/100000000000000 : ℝ)^3835 := by
    have hnat : (4184177001 : ℕ)^4859*100000000000000^3835 ≤ 33156944632201^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4184177001 10000000000 33156944632201 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4667729131/10000000000 : ℝ)^4859 ≤ (4760604697971/12500000000000 : ℝ)^3835 := by
    have hnat : (4667729131 : ℕ)^4859*12500000000000^3835 ≤ 4760604697971^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4667729131 10000000000 4760604697971 12500000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (934897669/2500000000 : ℝ)^4859 ≤ (28758217774163/100000000000000 : ℝ)^3835 := by
    have hnat : (934897669 : ℕ)^4859*100000000000000^3835 ≤ 28758217774163^3835*2500000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      934897669 2500000000 28758217774163 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4184177001/10000000000 : ℝ), (4667729131/10000000000 : ℝ), (934897669/2500000000 : ℝ)] ![(33156944632201/100000000000000 : ℝ), (4760604697971/12500000000000 : ℝ), (28758217774163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4184177001/10000000000 : ℝ)|^4859 ≤ (33156944632201/100000000000000 : ℝ)^3835
        have hw : |(4184177001/10000000000 : ℝ)|=(4184177001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4667729131/10000000000 : ℝ)|^4859 ≤ (4760604697971/12500000000000 : ℝ)^3835
        have hw : |(4667729131/10000000000 : ℝ)|=(4667729131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(934897669/2500000000 : ℝ)|^4859 ≤ (28758217774163/100000000000000 : ℝ)^3835
        have hw : |(934897669/2500000000 : ℝ)|=(934897669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1635_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35384243/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (23681/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4547/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4771/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17469/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (23681/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4547/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (23681/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4547/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (23681/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4547/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (23681/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4547/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (23681/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4547/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (23681/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4547/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4547/100000 : ℝ) ^ (4855/1024 : ℝ) ≤ (21625237015063/50000000000000000000 : ℝ) := by
    have hpowers : (4547/100000 : ℝ)^4855 ≤ (21625237015063/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4547 : ℕ)^4855*50000000000000000000^1024 ≤ 21625237015063^1024*100000^4855 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4547 100000 21625237015063 50000000000000000000 4855 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4547/100000 : ℝ)) (X := (21625237015063/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4855 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (23681/100000 : ℝ) ^ (4855/1024 : ℝ) ≤ (108118152691704587/100000000000000000000 : ℝ) := by
    have hpowers : (23681/100000 : ℝ)^4855 ≤ (108118152691704587/100000000000000000000 : ℝ)^1024 := by
      have hnat : (23681 : ℕ)^4855*100000000000000000000^1024 ≤ 108118152691704587^1024*100000^4855 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23681 100000 108118152691704587 100000000000000000000 4855 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (23681/100000 : ℝ)) (X := (108118152691704587/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4855 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000021625237015063/25000000000000000000 : ℝ) ≤ (5000000912223899/5000000000000000 : ℝ) ^ (4855/1024 : ℝ) := by
    have hpowers : (25000021625237015063/25000000000000000000 : ℝ)^1024 ≤ (5000000912223899/5000000000000000 : ℝ)^4855 := by
      have hnat : (25000021625237015063 : ℕ)^1024*5000000000000000^4855 ≤ 5000000912223899^4855*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000021625237015063 25000000000000000000 5000000912223899 5000000000000000 1024 4855 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000912223899/5000000000000000 : ℝ)) (X := (25000021625237015063/25000000000000000000 : ℝ)) (by norm_num) 4855 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100108161403165734713/100000000000000000000 : ℝ) ≤ (10002280330433387/10000000000000000 : ℝ) ^ (4855/1024 : ℝ) := by
    have hpowers : (100108161403165734713/100000000000000000000 : ℝ)^1024 ≤ (10002280330433387/10000000000000000 : ℝ)^4855 := by
      have hnat : (100108161403165734713 : ℕ)^1024*10000000000000000^4855 ≤ 10002280330433387^4855*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100108161403165734713 100000000000000000000 10002280330433387 10000000000000000 1024 4855 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002280330433387/10000000000000000 : ℝ)) (X := (100108161403165734713/100000000000000000000 : ℝ)) (by norm_num) 4855 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50108118152691704587/50000000000000000000 : ℝ) ≤ (312642463638093/312500000000000 : ℝ) ^ (4855/1024 : ℝ) := by
    have hpowers : (50108118152691704587/50000000000000000000 : ℝ)^1024 ≤ (312642463638093/312500000000000 : ℝ)^4855 := by
      have hnat : (50108118152691704587 : ℕ)^1024*312500000000000^4855 ≤ 312642463638093^4855*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50108118152691704587 50000000000000000000 312642463638093 312500000000000 1024 4855 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312642463638093/312500000000000 : ℝ)) (X := (50108118152691704587/50000000000000000000 : ℝ)) (by norm_num) 4855 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(21625237015063/50000000000000000000 : ℝ) ≤ ((95659657087775610283/95670000000000000000 : ℝ)+2*(2278505985589/1913400000000000 : ℝ)*(4547/100000 : ℝ))^(4855/1024 : ℝ) := by
    rw [show (95659657087775610283/95670000000000000000 : ℝ)+2*(2278505985589/1913400000000000 : ℝ)*(4547/100000 : ℝ)=(5000000912223899/5000000000000000 : ℝ) by norm_num, show 1+2*(21625237015063/50000000000000000000 : ℝ)=(25000021625237015063/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(108118152691704587/100000000000000000000 : ℝ)+(21625237015063/50000000000000000000 : ℝ) ≤ ((95659657087775610283/95670000000000000000 : ℝ)+(2278505985589/1913400000000000 : ℝ)*((23681/100000 : ℝ)+(4547/100000 : ℝ)))^(4855/1024 : ℝ) := by
    rw [show (95659657087775610283/95670000000000000000 : ℝ)+(2278505985589/1913400000000000 : ℝ)*((23681/100000 : ℝ)+(4547/100000 : ℝ))=(10002280330433387/10000000000000000 : ℝ) by norm_num, show 1+(108118152691704587/100000000000000000000 : ℝ)+(21625237015063/50000000000000000000 : ℝ)=(100108161403165734713/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(108118152691704587/100000000000000000000 : ℝ) ≤ ((95659657087775610283/95670000000000000000 : ℝ)+2*(2278505985589/1913400000000000 : ℝ)*(23681/100000 : ℝ))^(4855/1024 : ℝ) := by
    rw [show (95659657087775610283/95670000000000000000 : ℝ)+2*(2278505985589/1913400000000000 : ℝ)*(23681/100000 : ℝ)=(312642463638093/312500000000000 : ℝ) by norm_num, show 1+2*(108118152691704587/100000000000000000000 : ℝ)=(50108118152691704587/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (95659657087775610283/95670000000000000000 : ℝ)*(X 1 0+X 2 0)+(2278505985589/1913400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4855/1024 : ℝ)) (lo := (4547/100000 : ℝ)) (hi := (23681/100000 : ℝ)) (c := (95659657087775610283/95670000000000000000 : ℝ)) (alpha := (2278505985589/1913400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (95659657087775610283/95670000000000000000 : ℝ)*(X 0 1+X 2 1)+(2278505985589/1913400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4855/1024 : ℝ)) (lo := (4547/100000 : ℝ)) (hi := (23681/100000 : ℝ)) (c := (95659657087775610283/95670000000000000000 : ℝ)) (alpha := (2278505985589/1913400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (95659657087775610283/95670000000000000000 : ℝ)*(X 0 2+X 1 2)+(2278505985589/1913400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4855/1024 : ℝ)) (lo := (4547/100000 : ℝ)) (hi := (23681/100000 : ℝ)) (c := (95659657087775610283/95670000000000000000 : ℝ)) (alpha := (2278505985589/1913400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-815779583/5000000000 : ℝ)*X 0 0+(2754009523/5000000000 : ℝ)*X 0 1+(256727959/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((670594091/1250000000 : ℝ)*X 1 0+(-182611393/1000000000 : ℝ)*X 1 1+(2567279479/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5364753671/10000000000 : ℝ)*X 2 0+(5134557829/10000000000 : ℝ)*X 2 1+(-22826427/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4183728017/10000000000 : ℝ)*X 0 0+(745917317/2000000000 : ℝ)*X 0 1+(4677588113/10000000000 : ℝ)*X 0 2+(4183728017/10000000000 : ℝ)*X 1 0+(745917317/2000000000 : ℝ)*X 1 1+(4677588113/10000000000 : ℝ)*X 1 2+(4183728017/10000000000 : ℝ)*X 2 0+(745917317/2000000000 : ℝ)*X 2 1+(4677588113/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-101983577/625000000 : ℝ)*X 0 0+(5138443103/10000000000 : ℝ)*X 0 1+(275203891/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((526506527/1000000000 : ℝ)*X 1 0+(-1456594381/10000000000 : ℝ)*X 1 1+(2752039037/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2632532403/5000000000 : ℝ)*X 2 0+(5504078243/10000000000 : ℝ)*X 2 1+(-728297397/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4184177001/10000000000 : ℝ)*X 0 0+(4667729131/10000000000 : ℝ)*X 0 1+(934897669/2500000000 : ℝ)*X 0 2+(4184177001/10000000000 : ℝ)*X 1 0+(4667729131/10000000000 : ℝ)*X 1 1+(934897669/2500000000 : ℝ)*X 1 2+(4184177001/10000000000 : ℝ)*X 2 0+(4667729131/10000000000 : ℝ)*X 2 1+(934897669/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7569244920186751342443/664375000000000000000000000 : ℝ) := by norm_num
    linear_combination (557470343/100000000000000 : ℝ)*(base1) + (783293717/50000000000000 : ℝ)*(base19) + (2037260607/100000000000000 : ℝ)*(base23) + (12651773/6250000000000 : ℝ)*(upper3) + (138299967/100000000000000 : ℝ)*(upper5) + (116641626795927/6250000000000 : ℝ)*(major0) + (116641626795927/6250000000000 : ℝ)*(major1) + (116641626795927/6250000000000 : ℝ)*(major2) + (2677669323555027/100000000000000 : ℝ)*(sp0) + (1338836496824261/50000000000000 : ℝ)*(sp1) + (53553450459507/2000000000000 : ℝ)*(sp2) + (131856635888801/12500000000000 : ℝ)*(sp3) + (724268909/12500000000000 : ℝ)*(sp4) + (1736442627/50000000000000 : ℝ)*(sp7) + (263714279366501/25000000000000 : ℝ)*(f.failure) + (669418640058989/25000000000000 : ℝ)*(f.sum) + (140197494981/1328750000000000000000000000 : ℝ)*base66 + (161579940709875851/66437500000000000000000000000000 : ℝ)*base68 + (115941156837124149/66437500000000000000000000000000 : ℝ)*base69 + (73922394688749149/66437500000000000000000000000000 : ℝ)*base71 + (14119969062637/2657500000000000000000000000 : ℝ)*base74 + (137162943581624149/66437500000000000000000000000000 : ℝ)*base75 + (303598190907625851/66437500000000000000000000000000 : ℝ)*base78 + (110050609909625851/66437500000000000000000000000000 : ℝ)*base80 + (494473729273/664375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (2556257/500000000000000000000 : ℝ)*base90 + (2556257/500000000000000000000 : ℝ)*base92 + (2556257/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (202430408869414403726939/31890000000000000000000000000 : ℝ) := by norm_num
    linear_combination (613110367/50000000000000 : ℝ)*(base19) + (1021164837/100000000000000 : ℝ)*(base23) + (23406089/100000000000000 : ℝ)*(upper2) + (53692173/20000000000000 : ℝ)*(upper3) + (28614029/50000000000000 : ℝ)*(upper5) + (1906195830840971/100000000000000 : ℝ)*(major0) + (1906195830840971/100000000000000 : ℝ)*(major1) + (1906195830840971/100000000000000 : ℝ)*(major2) + (4767094593/50000000000000 : ℝ)*(sp1) + (9085957917/100000000000000 : ℝ)*(sp2) + (1367482538262477/50000000000000 : ℝ)*(sp4) + (546990863223007/20000000000000 : ℝ)*(sp5) + (2734954969402201/100000000000000 : ℝ)*(sp6) + (67339148347789/6250000000000 : ℝ)*(sp7) + (67339148347789/6250000000000 : ℝ)*(f.failure) + (1367482538262477/50000000000000 : ℝ)*(f.sum) + (433446940301401/95670000000000000000000000000 : ℝ)*base66 + (12152781641863084931/3189000000000000000000000000000000 : ℝ)*base67 + (7194485861341084931/3189000000000000000000000000000000 : ℝ)*base69 + (653580564100915069/3189000000000000000000000000000000 : ℝ)*base72 + (73015006784489/95670000000000000000000000000 : ℝ)*base73 + (22336771876780915069/3189000000000000000000000000000000 : ℝ)*base76 + (5225763621904084931/3189000000000000000000000000000000 : ℝ)*base77 + (35199412604422915069/3189000000000000000000000000000000 : ℝ)*base80 + (301247667354781/95670000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (738727/125000000000000000000 : ℝ)*base89 + (738727/125000000000000000000 : ℝ)*base91 + (738727/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1635_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35384243/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (23681/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4547/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4771/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17469/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1635_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1635_s2_0 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-821195589/5000000000 : ℝ)*x 0 + (2728306737/5000000000 : ℝ)*x 1 + (5178838631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (821195589/5000000000 : ℝ)^4859 ≤ (10139057953407/100000000000000 : ℝ)^3835 := by
    have hnat : (821195589 : ℕ)^4859*100000000000000^3835 ≤ 10139057953407^3835*5000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      821195589 5000000000 10139057953407 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2728306737/5000000000 : ℝ)^4859 ≤ (23208545008759/50000000000000 : ℝ)^3835 := by
    have hnat : (2728306737 : ℕ)^4859*50000000000000^3835 ≤ 23208545008759^3835*5000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728306737 5000000000 23208545008759 50000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5178838631/10000000000 : ℝ)^4859 ≤ (4344385202071/10000000000000 : ℝ)^3835 := by
    have hnat : (5178838631 : ℕ)^4859*10000000000000^3835 ≤ 4344385202071^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178838631 10000000000 4344385202071 10000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-821195589/5000000000 : ℝ), (2728306737/5000000000 : ℝ), (5178838631/10000000000 : ℝ)] ![(10139057953407/100000000000000 : ℝ), (23208545008759/50000000000000 : ℝ), (4344385202071/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-821195589/5000000000 : ℝ)|^4859 ≤ (10139057953407/100000000000000 : ℝ)^3835
        have hw : |(-821195589/5000000000 : ℝ)|=(821195589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2728306737/5000000000 : ℝ)|^4859 ≤ (23208545008759/50000000000000 : ℝ)^3835
        have hw : |(2728306737/5000000000 : ℝ)|=(2728306737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5178838631/10000000000 : ℝ)|^4859 ≤ (4344385202071/10000000000000 : ℝ)^3835
        have hw : |(5178838631/10000000000 : ℝ)|=(5178838631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1635_s2_1 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167225631/312500000 : ℝ)*x 0 + (-1785608521/10000000000 : ℝ)*x 1 + (2589419339/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167225631/312500000 : ℝ)^4859 ≤ (45284109373471/100000000000000 : ℝ)^3835 := by
    have hnat : (167225631 : ℕ)^4859*100000000000000^3835 ≤ 45284109373471^3835*312500000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167225631 312500000 45284109373471 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1785608521/10000000000 : ℝ)^4859 ≤ (11272038094787/100000000000000 : ℝ)^3835 := by
    have hnat : (1785608521 : ℕ)^4859*100000000000000^3835 ≤ 11272038094787^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1785608521 10000000000 11272038094787 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2589419339/5000000000 : ℝ)^4859 ≤ (678810195629/1562500000000 : ℝ)^3835 := by
    have hnat : (2589419339 : ℕ)^4859*1562500000000^3835 ≤ 678810195629^3835*5000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589419339 5000000000 678810195629 1562500000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167225631/312500000 : ℝ), (-1785608521/10000000000 : ℝ), (2589419339/5000000000 : ℝ)] ![(45284109373471/100000000000000 : ℝ), (11272038094787/100000000000000 : ℝ), (678810195629/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167225631/312500000 : ℝ)|^4859 ≤ (45284109373471/100000000000000 : ℝ)^3835
        have hw : |(167225631/312500000 : ℝ)|=(167225631/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1785608521/10000000000 : ℝ)|^4859 ≤ (11272038094787/100000000000000 : ℝ)^3835
        have hw : |(-1785608521/10000000000 : ℝ)|=(1785608521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2589419339/5000000000 : ℝ)|^4859 ≤ (678810195629/1562500000000 : ℝ)^3835
        have hw : |(2589419339/5000000000 : ℝ)|=(2589419339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1635_s2_2 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351220189/10000000000 : ℝ)*x 0 + (5178838653/10000000000 : ℝ)*x 1 + (-892804279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351220189/10000000000 : ℝ)^4859 ≤ (22642054670653/50000000000000 : ℝ)^3835 := by
    have hnat : (5351220189 : ℕ)^4859*50000000000000^3835 ≤ 22642054670653^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351220189 10000000000 22642054670653 50000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5178838653/10000000000 : ℝ)^4859 ≤ (2172192612727/5000000000000 : ℝ)^3835 := by
    have hnat : (5178838653 : ℕ)^4859*5000000000000^3835 ≤ 2172192612727^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178838653 10000000000 2172192612727 5000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (892804279/5000000000 : ℝ)^4859 ≤ (2818009597681/25000000000000 : ℝ)^3835 := by
    have hnat : (892804279 : ℕ)^4859*25000000000000^3835 ≤ 2818009597681^3835*5000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      892804279 5000000000 2818009597681 25000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351220189/10000000000 : ℝ), (5178838653/10000000000 : ℝ), (-892804279/5000000000 : ℝ)] ![(22642054670653/50000000000000 : ℝ), (2172192612727/5000000000000 : ℝ), (2818009597681/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351220189/10000000000 : ℝ)|^4859 ≤ (22642054670653/50000000000000 : ℝ)^3835
        have hw : |(5351220189/10000000000 : ℝ)|=(5351220189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5178838653/10000000000 : ℝ)|^4859 ≤ (2172192612727/5000000000000 : ℝ)^3835
        have hw : |(5178838653/10000000000 : ℝ)|=(5178838653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-892804279/5000000000 : ℝ)|^4859 ≤ (2818009597681/25000000000000 : ℝ)^3835
        have hw : |(-892804279/5000000000 : ℝ)|=(892804279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1635_s2_3 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2095886167/5000000000 : ℝ)*x 0 + (962552097/2500000000 : ℝ)*x 1 + (911063723/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2095886167/5000000000 : ℝ)^4859 ≤ (33233222403917/100000000000000 : ℝ)^3835 := by
    have hnat : (2095886167 : ℕ)^4859*100000000000000^3835 ≤ 33233222403917^3835*5000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095886167 5000000000 33233222403917 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (962552097/2500000000 : ℝ)^4859 ≤ (116563510021/390625000000 : ℝ)^3835 := by
    have hnat : (962552097 : ℕ)^4859*390625000000^3835 ≤ 116563510021^3835*2500000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      962552097 2500000000 116563510021 390625000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (911063723/2000000000 : ℝ)^4859 ≤ (4615814877099/12500000000000 : ℝ)^3835 := by
    have hnat : (911063723 : ℕ)^4859*12500000000000^3835 ≤ 4615814877099^3835*2000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      911063723 2000000000 4615814877099 12500000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2095886167/5000000000 : ℝ), (962552097/2500000000 : ℝ), (911063723/2000000000 : ℝ)] ![(33233222403917/100000000000000 : ℝ), (116563510021/390625000000 : ℝ), (4615814877099/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2095886167/5000000000 : ℝ)|^4859 ≤ (33233222403917/100000000000000 : ℝ)^3835
        have hw : |(2095886167/5000000000 : ℝ)|=(2095886167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(962552097/2500000000 : ℝ)|^4859 ≤ (116563510021/390625000000 : ℝ)^3835
        have hw : |(962552097/2500000000 : ℝ)|=(962552097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(911063723/2000000000 : ℝ)|^4859 ≤ (4615814877099/12500000000000 : ℝ)^3835
        have hw : |(911063723/2000000000 : ℝ)|=(911063723/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1635_s2_4 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-410615963/2500000000 : ℝ)*x 0 + (5180994291/10000000000 : ℝ)*x 1 + (5454434703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (410615963/2500000000 : ℝ)^4859 ≤ (5069813196397/50000000000000 : ℝ)^3835 := by
    have hnat : (410615963 : ℕ)^4859*50000000000000^3835 ≤ 5069813196397^3835*2500000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410615963 2500000000 5069813196397 50000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5180994291/10000000000 : ℝ)^4859 ≤ (1738670600653/4000000000000 : ℝ)^3835 := by
    have hnat : (5180994291 : ℕ)^4859*4000000000000^3835 ≤ 1738670600653^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180994291 10000000000 1738670600653 4000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5454434703/10000000000 : ℝ)^4859 ≤ (46393608579943/100000000000000 : ℝ)^3835 := by
    have hnat : (5454434703 : ℕ)^4859*100000000000000^3835 ≤ 46393608579943^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5454434703 10000000000 46393608579943 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-410615963/2500000000 : ℝ), (5180994291/10000000000 : ℝ), (5454434703/10000000000 : ℝ)] ![(5069813196397/50000000000000 : ℝ), (1738670600653/4000000000000 : ℝ), (46393608579943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-410615963/2500000000 : ℝ)|^4859 ≤ (5069813196397/50000000000000 : ℝ)^3835
        have hw : |(-410615963/2500000000 : ℝ)|=(410615963/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5180994291/10000000000 : ℝ)|^4859 ≤ (1738670600653/4000000000000 : ℝ)^3835
        have hw : |(5180994291/10000000000 : ℝ)|=(5180994291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5454434703/10000000000 : ℝ)|^4859 ≤ (46393608579943/100000000000000 : ℝ)^3835
        have hw : |(5454434703/10000000000 : ℝ)|=(5454434703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1635_s2_5 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (105542981/200000000 : ℝ)*x 0 + (-755006137/5000000000 : ℝ)*x 1 + (272721743/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105542981/200000000 : ℝ)^4859 ≤ (44491393548803/100000000000000 : ℝ)^3835 := by
    have hnat : (105542981 : ℕ)^4859*100000000000000^3835 ≤ 44491393548803^3835*200000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105542981 200000000 44491393548803 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (755006137/5000000000 : ℝ)^4859 ≤ (2278749040787/25000000000000 : ℝ)^3835 := by
    have hnat : (755006137 : ℕ)^4859*25000000000000^3835 ≤ 2278749040787^3835*5000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      755006137 5000000000 2278749040787 25000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (272721743/500000000 : ℝ)^4859 ≤ (23196805135951/50000000000000 : ℝ)^3835 := by
    have hnat : (272721743 : ℕ)^4859*50000000000000^3835 ≤ 23196805135951^3835*500000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272721743 500000000 23196805135951 50000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105542981/200000000 : ℝ), (-755006137/5000000000 : ℝ), (272721743/500000000 : ℝ)] ![(44491393548803/100000000000000 : ℝ), (2278749040787/25000000000000 : ℝ), (23196805135951/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105542981/200000000 : ℝ)|^4859 ≤ (44491393548803/100000000000000 : ℝ)^3835
        have hw : |(105542981/200000000 : ℝ)|=(105542981/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-755006137/5000000000 : ℝ)|^4859 ≤ (2278749040787/25000000000000 : ℝ)^3835
        have hw : |(-755006137/5000000000 : ℝ)|=(755006137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(272721743/500000000 : ℝ)|^4859 ≤ (23196805135951/50000000000000 : ℝ)^3835
        have hw : |(272721743/500000000 : ℝ)|=(272721743/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1635_s2_6 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (329821871/625000000 : ℝ)*x 0 + (5454433913/10000000000 : ℝ)*x 1 + (-1510012371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (329821871/625000000 : ℝ)^4859 ≤ (44491403013177/100000000000000 : ℝ)^3835 := by
    have hnat : (329821871 : ℕ)^4859*100000000000000^3835 ≤ 44491403013177^3835*625000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329821871 625000000 44491403013177 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5454433913/10000000000 : ℝ)^4859 ≤ (46393600066269/100000000000000 : ℝ)^3835 := by
    have hnat : (5454433913 : ℕ)^4859*100000000000000^3835 ≤ 46393600066269^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5454433913 10000000000 46393600066269 100000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1510012371/10000000000 : ℝ)^4859 ≤ (455749845251/5000000000000 : ℝ)^3835 := by
    have hnat : (1510012371 : ℕ)^4859*5000000000000^3835 ≤ 455749845251^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1510012371 10000000000 455749845251 5000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(329821871/625000000 : ℝ), (5454433913/10000000000 : ℝ), (-1510012371/10000000000 : ℝ)] ![(44491403013177/100000000000000 : ℝ), (46393600066269/100000000000000 : ℝ), (455749845251/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(329821871/625000000 : ℝ)|^4859 ≤ (44491403013177/100000000000000 : ℝ)^3835
        have hw : |(329821871/625000000 : ℝ)|=(329821871/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5454433913/10000000000 : ℝ)|^4859 ≤ (46393600066269/100000000000000 : ℝ)^3835
        have hw : |(5454433913/10000000000 : ℝ)|=(5454433913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1510012371/10000000000 : ℝ)|^4859 ≤ (455749845251/5000000000000 : ℝ)^3835
        have hw : |(-1510012371/10000000000 : ℝ)|=(1510012371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1635_s2_7 (p : ℝ) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4191957589/10000000000 : ℝ)*x 0 + (454984873/1000000000 : ℝ)*x 1 + (3855738001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4191957589/10000000000 : ℝ)^4859 ≤ (3323508332861/10000000000000 : ℝ)^3835 := by
    have hnat : (4191957589 : ℕ)^4859*10000000000000^3835 ≤ 3323508332861^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4191957589 10000000000 3323508332861 10000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (454984873/1000000000 : ℝ)^4859 ≤ (1152198385493/3125000000000 : ℝ)^3835 := by
    have hnat : (454984873 : ℕ)^4859*3125000000000^3835 ≤ 1152198385493^3835*1000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      454984873 1000000000 1152198385493 3125000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3855738001/10000000000 : ℝ)^4859 ≤ (14947284160543/50000000000000 : ℝ)^3835 := by
    have hnat : (3855738001 : ℕ)^4859*50000000000000^3835 ≤ 14947284160543^3835*10000000000^4859 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3855738001 10000000000 14947284160543 50000000000000 4859 3835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4859/1024 : ℝ)) 4859 3835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4191957589/10000000000 : ℝ), (454984873/1000000000 : ℝ), (3855738001/10000000000 : ℝ)] ![(3323508332861/10000000000000 : ℝ), (1152198385493/3125000000000 : ℝ), (14947284160543/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4191957589/10000000000 : ℝ)|^4859 ≤ (3323508332861/10000000000000 : ℝ)^3835
        have hw : |(4191957589/10000000000 : ℝ)|=(4191957589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(454984873/1000000000 : ℝ)|^4859 ≤ (1152198385493/3125000000000 : ℝ)^3835
        have hw : |(454984873/1000000000 : ℝ)|=(454984873/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3855738001/10000000000 : ℝ)|^4859 ≤ (14947284160543/50000000000000 : ℝ)^3835
        have hw : |(3855738001/10000000000 : ℝ)|=(3855738001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1635_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35384243/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17469/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4771/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10499/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16397/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17469/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4771/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17469/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4771/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17469/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4771/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17469/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4771/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17469/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4771/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17469/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4771/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4771/50000 : ℝ) ^ (4855/1024 : ℝ) ≤ (1452965228139587/100000000000000000000 : ℝ) := by
    have hpowers : (4771/50000 : ℝ)^4855 ≤ (1452965228139587/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4771 : ℕ)^4855*100000000000000000000^1024 ≤ 1452965228139587^1024*50000^4855 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4771 50000 1452965228139587 100000000000000000000 4855 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4771/50000 : ℝ)) (X := (1452965228139587/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4855 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17469/100000 : ℝ) ^ (4855/1024 : ℝ) ≤ (12776237334918939/50000000000000000000 : ℝ) := by
    have hpowers : (17469/100000 : ℝ)^4855 ≤ (12776237334918939/50000000000000000000 : ℝ)^1024 := by
      have hnat : (17469 : ℕ)^4855*50000000000000000000^1024 ≤ 12776237334918939^1024*100000^4855 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17469 100000 12776237334918939 50000000000000000000 4855 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17469/100000 : ℝ)) (X := (12776237334918939/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4855 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001452965228139587/50000000000000000000 : ℝ) ≤ (10000061290188907/10000000000000000 : ℝ) ^ (4855/1024 : ℝ) := by
    have hpowers : (50001452965228139587/50000000000000000000 : ℝ)^1024 ≤ (10000061290188907/10000000000000000 : ℝ)^4855 := by
      have hnat : (50001452965228139587 : ℕ)^1024*10000000000000000^4855 ≤ 10000061290188907^4855*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001452965228139587 50000000000000000000 10000061290188907 10000000000000000 1024 4855 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000061290188907/10000000000000000 : ℝ)) (X := (50001452965228139587/50000000000000000000 : ℝ)) (by norm_num) 4855 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20005401087979595493/20000000000000000000 : ℝ) ≤ (2000113905765211/2000000000000000 : ℝ) ^ (4855/1024 : ℝ) := by
    have hpowers : (20005401087979595493/20000000000000000000 : ℝ)^1024 ≤ (2000113905765211/2000000000000000 : ℝ)^4855 := by
      have hnat : (20005401087979595493 : ℕ)^1024*2000000000000000^4855 ≤ 2000113905765211^4855*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20005401087979595493 20000000000000000000 2000113905765211 2000000000000000 1024 4855 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000113905765211/2000000000000000 : ℝ)) (X := (20005401087979595493/20000000000000000000 : ℝ)) (by norm_num) 4855 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25012776237334918939/25000000000000000000 : ℝ) ≤ (10001077767463203/10000000000000000 : ℝ) ^ (4855/1024 : ℝ) := by
    have hpowers : (25012776237334918939/25000000000000000000 : ℝ)^1024 ≤ (10001077767463203/10000000000000000 : ℝ)^4855 := by
      have hnat : (25012776237334918939 : ℕ)^1024*10000000000000000^4855 ≤ 10001077767463203^4855*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012776237334918939 25000000000000000000 10001077767463203 10000000000000000 1024 4855 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001077767463203/10000000000000000 : ℝ)) (X := (25012776237334918939/25000000000000000000 : ℝ)) (by norm_num) 4855 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1452965228139587/100000000000000000000 : ℝ) ≤ ((79260786621176133357/79270000000000000000 : ℝ)+2*(127059659287/198175000000000 : ℝ)*(4771/50000 : ℝ))^(4855/1024 : ℝ) := by
    rw [show (79260786621176133357/79270000000000000000 : ℝ)+2*(127059659287/198175000000000 : ℝ)*(4771/50000 : ℝ)=(10000061290188907/10000000000000000 : ℝ) by norm_num, show 1+2*(1452965228139587/100000000000000000000 : ℝ)=(50001452965228139587/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(12776237334918939/50000000000000000000 : ℝ)+(1452965228139587/100000000000000000000 : ℝ) ≤ ((79260786621176133357/79270000000000000000 : ℝ)+(127059659287/198175000000000 : ℝ)*((17469/100000 : ℝ)+(4771/50000 : ℝ)))^(4855/1024 : ℝ) := by
    rw [show (79260786621176133357/79270000000000000000 : ℝ)+(127059659287/198175000000000 : ℝ)*((17469/100000 : ℝ)+(4771/50000 : ℝ))=(2000113905765211/2000000000000000 : ℝ) by norm_num, show 1+(12776237334918939/50000000000000000000 : ℝ)+(1452965228139587/100000000000000000000 : ℝ)=(20005401087979595493/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(12776237334918939/50000000000000000000 : ℝ) ≤ ((79260786621176133357/79270000000000000000 : ℝ)+2*(127059659287/198175000000000 : ℝ)*(17469/100000 : ℝ))^(4855/1024 : ℝ) := by
    rw [show (79260786621176133357/79270000000000000000 : ℝ)+2*(127059659287/198175000000000 : ℝ)*(17469/100000 : ℝ)=(10001077767463203/10000000000000000 : ℝ) by norm_num, show 1+2*(12776237334918939/50000000000000000000 : ℝ)=(25012776237334918939/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (79260786621176133357/79270000000000000000 : ℝ)*(X 1 0+X 2 0)+(127059659287/198175000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4855/1024 : ℝ)) (lo := (4771/50000 : ℝ)) (hi := (17469/100000 : ℝ)) (c := (79260786621176133357/79270000000000000000 : ℝ)) (alpha := (127059659287/198175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (79260786621176133357/79270000000000000000 : ℝ)*(X 0 1+X 2 1)+(127059659287/198175000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4855/1024 : ℝ)) (lo := (4771/50000 : ℝ)) (hi := (17469/100000 : ℝ)) (c := (79260786621176133357/79270000000000000000 : ℝ)) (alpha := (127059659287/198175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (79260786621176133357/79270000000000000000 : ℝ)*(X 0 2+X 1 2)+(127059659287/198175000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4855/1024 : ℝ)) (lo := (4771/50000 : ℝ)) (hi := (17469/100000 : ℝ)) (c := (79260786621176133357/79270000000000000000 : ℝ)) (alpha := (127059659287/198175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-821195589/5000000000 : ℝ)*X 0 0+(2728306737/5000000000 : ℝ)*X 0 1+(5178838631/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167225631/312500000 : ℝ)*X 1 0+(-1785608521/10000000000 : ℝ)*X 1 1+(2589419339/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351220189/10000000000 : ℝ)*X 2 0+(5178838653/10000000000 : ℝ)*X 2 1+(-892804279/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2095886167/5000000000 : ℝ)*X 0 0+(962552097/2500000000 : ℝ)*X 0 1+(911063723/2000000000 : ℝ)*X 0 2+(2095886167/5000000000 : ℝ)*X 1 0+(962552097/2500000000 : ℝ)*X 1 1+(911063723/2000000000 : ℝ)*X 1 2+(2095886167/5000000000 : ℝ)*X 2 0+(962552097/2500000000 : ℝ)*X 2 1+(911063723/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-410615963/2500000000 : ℝ)*X 0 0+(5180994291/10000000000 : ℝ)*X 0 1+(5454434703/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((105542981/200000000 : ℝ)*X 1 0+(-755006137/5000000000 : ℝ)*X 1 1+(272721743/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((329821871/625000000 : ℝ)*X 2 0+(5454433913/10000000000 : ℝ)*X 2 1+(-1510012371/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4191957589/10000000000 : ℝ)*X 0 0+(454984873/1000000000 : ℝ)*X 0 1+(3855738001/10000000000 : ℝ)*X 0 2+(4191957589/10000000000 : ℝ)*X 1 0+(454984873/1000000000 : ℝ)*X 1 1+(3855738001/10000000000 : ℝ)*X 1 2+(4191957589/10000000000 : ℝ)*X 2 0+(454984873/1000000000 : ℝ)*X 2 1+(3855738001/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1635_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6055113806154803523718064391/1981750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (100920733/25000000000000 : ℝ)*(base19) + (172810679/50000000000000 : ℝ)*(base23) + (29990013/100000000000000 : ℝ)*(lower2) + (87159649/100000000000000 : ℝ)*(upper3) + (17102829/100000000000000 : ℝ)*(upper5) + (1254567481769921/50000000000000 : ℝ)*(major0) + (1254567481769921/50000000000000 : ℝ)*(major1) + (1254567481769921/50000000000000 : ℝ)*(major2) + (3600043668245817/100000000000000 : ℝ)*(sp0) + (1800023888892523/50000000000000 : ℝ)*(sp1) + (180002391792331/5000000000000 : ℝ)*(sp2) + (1418219464792847/100000000000000 : ℝ)*(sp3) + (4513222161/100000000000000 : ℝ)*(sp4) + (136185683/6250000000000 : ℝ)*(sp7) + (56728865750551/4000000000000 : ℝ)*(f.failure) + (1800024090733989/50000000000000 : ℝ)*(f.sum) + (53827598124049/9908750000000000000000000000 : ℝ)*base65 + (23575806087729345203/3963500000000000000000000000000000 : ℝ)*base68 + (3160187845337654797/3963500000000000000000000000000000 : ℝ)*base69 + (14651879366228845203/3963500000000000000000000000000000 : ℝ)*base72 + (93569800592117/19817500000000000000000000000 : ℝ)*base74 + (48381164085715345203/3963500000000000000000000000000000 : ℝ)*base76 + (10474481767473154797/3963500000000000000000000000000000 : ℝ)*base77 + (37421824657817845203/3963500000000000000000000000000000 : ℝ)*base80 + (116113223204261/39635000000000000000000000000 : ℝ)*base81 + (367893/80000000000000000000 : ℝ)*base89 + (367893/80000000000000000000 : ℝ)*base91 + (367893/80000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1844851424026150127950609917/198175000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1032289669/100000000000000 : ℝ)*(base19) + (415152601/20000000000000 : ℝ)*(base23) + (42533833/25000000000000 : ℝ)*(upper3) + (176425037/100000000000000 : ℝ)*(lower4) + (254889855101973/10000000000000 : ℝ)*(major0) + (254889855101973/10000000000000 : ℝ)*(major1) + (254889855101973/10000000000000 : ℝ)*(major2) + (517445673/4000000000000 : ℝ)*(sp1) + (9857669347/50000000000000 : ℝ)*(sp2) + (1541790019/100000000000000 : ℝ)*(sp3) + (457137480032053/12500000000000 : ℝ)*(sp4) + (365708587182493/10000000000000 : ℝ)*(sp5) + (1828539024577363/50000000000000 : ℝ)*(sp6) + (90043463105389/6250000000000 : ℝ)*(sp7) + (1440696951476243/100000000000000 : ℝ)*(f.failure) + (457137480032053/12500000000000 : ℝ)*(f.sum) + (1222494236451/792700000000000000000000000 : ℝ)*base66 + (5086225302597013361/792700000000000000000000000000000 : ℝ)*base67 + (1739498454643513361/792700000000000000000000000000000 : ℝ)*base69 + (317354067610813361/792700000000000000000000000000000 : ℝ)*base71 + (15254873417039/7927000000000000000000000000 : ℝ)*base73 + (8137946873312913361/792700000000000000000000000000000 : ℝ)*base75 + (2030264775765413361/792700000000000000000000000000000 : ℝ)*base77 + (2232208313760186639/792700000000000000000000000000000 : ℝ)*base80 + (14326224859711/7927000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (8960951/2000000000000000000000 : ℝ)*base90 + (8960951/2000000000000000000000 : ℝ)*base92 + (8960951/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1635_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35384243/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17469/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4771/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10499/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16397/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1635_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1635_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35384243/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10499/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16397/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1635_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1635_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1635_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4855/1024 : ℝ) ≤ p) (hpb : p ≤ (4859/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35384243/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10499/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16397/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1635_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1764_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:29:15.515993+00:00
-- url     : https://prove2.me/submissions/ea567d06-f1de-4204-9c76-55495f68bba6

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
theorem support_rectangle_w1764_s0_0 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-556576341/5000000000 : ℝ)*x 0 + (5589792669/10000000000 : ℝ)*x 1 + (2498687903/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (556576341/5000000000 : ℝ)^5999 ≤ (7084478930813/100000000000000 : ℝ)^4975 := by
    have hnat : (556576341 : ℕ)^5999*100000000000000^4975 ≤ 7084478930813^4975*5000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      556576341 5000000000 7084478930813 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5589792669/10000000000 : ℝ)^5999 ≤ (24795471826471/50000000000000 : ℝ)^4975 := by
    have hnat : (5589792669 : ℕ)^5999*50000000000000^4975 ≤ 24795471826471^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5589792669 10000000000 24795471826471 50000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2498687903/5000000000 : ℝ)^5999 ≤ (43324577398371/100000000000000 : ℝ)^4975 := by
    have hnat : (2498687903 : ℕ)^5999*100000000000000^4975 ≤ 43324577398371^4975*5000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2498687903 5000000000 43324577398371 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-556576341/5000000000 : ℝ), (5589792669/10000000000 : ℝ), (2498687903/5000000000 : ℝ)] ![(7084478930813/100000000000000 : ℝ), (24795471826471/50000000000000 : ℝ), (43324577398371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-556576341/5000000000 : ℝ)|^5999 ≤ (7084478930813/100000000000000 : ℝ)^4975
        have hw : |(-556576341/5000000000 : ℝ)|=(556576341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5589792669/10000000000 : ℝ)|^5999 ≤ (24795471826471/50000000000000 : ℝ)^4975
        have hw : |(5589792669/10000000000 : ℝ)|=(5589792669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2498687903/5000000000 : ℝ)|^5999 ≤ (43324577398371/100000000000000 : ℝ)^4975
        have hw : |(2498687903/5000000000 : ℝ)|=(2498687903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1764_s0_1 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071212679/2000000000 : ℝ)*x 0 + (-22327241/156250000 : ℝ)*x 1 + (2498687691/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071212679/2000000000 : ℝ)^5999 ≤ (9420289472381/20000000000000 : ℝ)^4975 := by
    have hnat : (1071212679 : ℕ)^5999*20000000000000^4975 ≤ 9420289472381^4975*2000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071212679 2000000000 9420289472381 20000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (22327241/156250000 : ℝ)^5999 ≤ (9573979660003/100000000000000 : ℝ)^4975 := by
    have hnat : (22327241 : ℕ)^5999*100000000000000^4975 ≤ 9573979660003^4975*156250000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22327241 156250000 9573979660003 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2498687691/5000000000 : ℝ)^5999 ≤ (270778581037/625000000000 : ℝ)^4975 := by
    have hnat : (2498687691 : ℕ)^5999*625000000000^4975 ≤ 270778581037^4975*5000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2498687691 5000000000 270778581037 625000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071212679/2000000000 : ℝ), (-22327241/156250000 : ℝ), (2498687691/5000000000 : ℝ)] ![(9420289472381/20000000000000 : ℝ), (9573979660003/100000000000000 : ℝ), (270778581037/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071212679/2000000000 : ℝ)|^5999 ≤ (9420289472381/20000000000000 : ℝ)^4975
        have hw : |(1071212679/2000000000 : ℝ)|=(1071212679/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-22327241/156250000 : ℝ)|^5999 ≤ (9573979660003/100000000000000 : ℝ)^4975
        have hw : |(-22327241/156250000 : ℝ)|=(22327241/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2498687691/5000000000 : ℝ)|^5999 ≤ (270778581037/625000000000 : ℝ)^4975
        have hw : |(2498687691/5000000000 : ℝ)|=(2498687691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1764_s0_2 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071212089/2000000000 : ℝ)*x 0 + (2498688653/5000000000 : ℝ)*x 1 + (-1428944807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071212089/2000000000 : ℝ)^5999 ≤ (1884056643191/4000000000000 : ℝ)^4975 := by
    have hnat : (1071212089 : ℕ)^5999*4000000000000^4975 ≤ 1884056643191^4975*2000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071212089 2000000000 1884056643191 4000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2498688653/5000000000 : ℝ)^5999 ≤ (43324593079213/100000000000000 : ℝ)^4975 := by
    have hnat : (2498688653 : ℕ)^5999*100000000000000^4975 ≤ 43324593079213^4975*5000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2498688653 5000000000 43324593079213 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1428944807/10000000000 : ℝ)^5999 ≤ (4786995416703/50000000000000 : ℝ)^4975 := by
    have hnat : (1428944807 : ℕ)^5999*50000000000000^4975 ≤ 4786995416703^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1428944807 10000000000 4786995416703 50000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071212089/2000000000 : ℝ), (2498688653/5000000000 : ℝ), (-1428944807/10000000000 : ℝ)] ![(1884056643191/4000000000000 : ℝ), (43324593079213/100000000000000 : ℝ), (4786995416703/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071212089/2000000000 : ℝ)|^5999 ≤ (1884056643191/4000000000000 : ℝ)^4975
        have hw : |(1071212089/2000000000 : ℝ)|=(1071212089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2498688653/5000000000 : ℝ)|^5999 ≤ (43324593079213/100000000000000 : ℝ)^4975
        have hw : |(2498688653/5000000000 : ℝ)|=(2498688653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1428944807/10000000000 : ℝ)|^5999 ≤ (4786995416703/50000000000000 : ℝ)^4975
        have hw : |(-1428944807/10000000000 : ℝ)|=(1428944807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1764_s0_3 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1978649943/5000000000 : ℝ)*x 0 + (1498172991/5000000000 : ℝ)*x 1 + (5054303873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1978649943/5000000000 : ℝ)^5999 ≤ (16349404516913/50000000000000 : ℝ)^4975 := by
    have hnat : (1978649943 : ℕ)^5999*50000000000000^4975 ≤ 16349404516913^4975*5000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1978649943 5000000000 16349404516913 50000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1498172991/5000000000 : ℝ)^5999 ≤ (11690398980837/50000000000000 : ℝ)^4975 := by
    have hnat : (1498172991 : ℕ)^5999*50000000000000^4975 ≤ 11690398980837^4975*5000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1498172991 5000000000 11690398980837 50000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5054303873/10000000000 : ℝ)^5999 ≤ (8784078598429/20000000000000 : ℝ)^4975 := by
    have hnat : (5054303873 : ℕ)^5999*20000000000000^4975 ≤ 8784078598429^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5054303873 10000000000 8784078598429 20000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1978649943/5000000000 : ℝ), (1498172991/5000000000 : ℝ), (5054303873/10000000000 : ℝ)] ![(16349404516913/50000000000000 : ℝ), (11690398980837/50000000000000 : ℝ), (8784078598429/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1978649943/5000000000 : ℝ)|^5999 ≤ (16349404516913/50000000000000 : ℝ)^4975
        have hw : |(1978649943/5000000000 : ℝ)|=(1978649943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1498172991/5000000000 : ℝ)|^5999 ≤ (11690398980837/50000000000000 : ℝ)^4975
        have hw : |(1498172991/5000000000 : ℝ)|=(1498172991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5054303873/10000000000 : ℝ)|^5999 ≤ (8784078598429/20000000000000 : ℝ)^4975
        have hw : |(5054303873/10000000000 : ℝ)|=(5054303873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1764_s0_4 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-222851251/2000000000 : ℝ)*x 0 + (5012139289/10000000000 : ℝ)*x 1 + (5574565309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (222851251/2000000000 : ℝ)^5999 ≤ (7092948948477/100000000000000 : ℝ)^4975 := by
    have hnat : (222851251 : ℕ)^5999*100000000000000^4975 ≤ 7092948948477^4975*2000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222851251 2000000000 7092948948477 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5012139289/10000000000 : ℝ)^5999 ≤ (43478960175143/100000000000000 : ℝ)^4975 := by
    have hnat : (5012139289 : ℕ)^5999*100000000000000^4975 ≤ 43478960175143^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5012139289 10000000000 43478960175143 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5574565309/10000000000 : ℝ)^5999 ≤ (24714045431361/50000000000000 : ℝ)^4975 := by
    have hnat : (5574565309 : ℕ)^5999*50000000000000^4975 ≤ 24714045431361^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5574565309 10000000000 24714045431361 50000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-222851251/2000000000 : ℝ), (5012139289/10000000000 : ℝ), (5574565309/10000000000 : ℝ)] ![(7092948948477/100000000000000 : ℝ), (43478960175143/100000000000000 : ℝ), (24714045431361/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-222851251/2000000000 : ℝ)|^5999 ≤ (7092948948477/100000000000000 : ℝ)^4975
        have hw : |(-222851251/2000000000 : ℝ)|=(222851251/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5012139289/10000000000 : ℝ)|^5999 ≤ (43478960175143/100000000000000 : ℝ)^4975
        have hw : |(5012139289/10000000000 : ℝ)|=(5012139289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5574565309/10000000000 : ℝ)|^5999 ≤ (24714045431361/50000000000000 : ℝ)^4975
        have hw : |(5574565309/10000000000 : ℝ)|=(5574565309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1764_s0_5 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (324941163/625000000 : ℝ)*x 0 + (-42587763/500000000 : ℝ)*x 1 + (348410331/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (324941163/625000000 : ℝ)^5999 ≤ (2272080654369/5000000000000 : ℝ)^4975 := by
    have hnat : (324941163 : ℕ)^5999*5000000000000^4975 ≤ 2272080654369^4975*625000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324941163 625000000 2272080654369 5000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42587763/500000000 : ℝ)^5999 ≤ (1026059235917/20000000000000 : ℝ)^4975 := by
    have hnat : (42587763 : ℕ)^5999*20000000000000^4975 ≤ 1026059235917^4975*500000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42587763 500000000 1026059235917 20000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (348410331/625000000 : ℝ)^5999 ≤ (4942809072373/10000000000000 : ℝ)^4975 := by
    have hnat : (348410331 : ℕ)^5999*10000000000000^4975 ≤ 4942809072373^4975*625000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      348410331 625000000 4942809072373 10000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(324941163/625000000 : ℝ), (-42587763/500000000 : ℝ), (348410331/625000000 : ℝ)] ![(2272080654369/5000000000000 : ℝ), (1026059235917/20000000000000 : ℝ), (4942809072373/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(324941163/625000000 : ℝ)|^5999 ≤ (2272080654369/5000000000000 : ℝ)^4975
        have hw : |(324941163/625000000 : ℝ)|=(324941163/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-42587763/500000000 : ℝ)|^5999 ≤ (1026059235917/20000000000000 : ℝ)^4975
        have hw : |(-42587763/500000000 : ℝ)|=(42587763/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(348410331/625000000 : ℝ)|^5999 ≤ (4942809072373/10000000000000 : ℝ)^4975
        have hw : |(348410331/625000000 : ℝ)|=(348410331/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1764_s0_6 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2599529431/5000000000 : ℝ)*x 0 + (5574565297/10000000000 : ℝ)*x 1 + (-851754889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2599529431/5000000000 : ℝ)^5999 ≤ (45441615764381/100000000000000 : ℝ)^4975 := by
    have hnat : (2599529431 : ℕ)^5999*100000000000000^4975 ≤ 45441615764381^4975*5000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2599529431 5000000000 45441615764381 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5574565297/10000000000 : ℝ)^5999 ≤ (49428090734421/100000000000000 : ℝ)^4975 := by
    have hnat : (5574565297 : ℕ)^5999*100000000000000^4975 ≤ 49428090734421^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5574565297 10000000000 49428090734421 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (851754889/10000000000 : ℝ)^5999 ≤ (5130293485029/100000000000000 : ℝ)^4975 := by
    have hnat : (851754889 : ℕ)^5999*100000000000000^4975 ≤ 5130293485029^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      851754889 10000000000 5130293485029 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2599529431/5000000000 : ℝ), (5574565297/10000000000 : ℝ), (-851754889/10000000000 : ℝ)] ![(45441615764381/100000000000000 : ℝ), (49428090734421/100000000000000 : ℝ), (5130293485029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2599529431/5000000000 : ℝ)|^5999 ≤ (45441615764381/100000000000000 : ℝ)^4975
        have hw : |(2599529431/5000000000 : ℝ)|=(2599529431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5574565297/10000000000 : ℝ)|^5999 ≤ (49428090734421/100000000000000 : ℝ)^4975
        have hw : |(5574565297/10000000000 : ℝ)|=(5574565297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-851754889/10000000000 : ℝ)|^5999 ≤ (5130293485029/100000000000000 : ℝ)^4975
        have hw : |(-851754889/10000000000 : ℝ)|=(851754889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1764_s0_7 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3961130913/10000000000 : ℝ)*x 0 + (5003021191/10000000000 : ℝ)*x 1 + (3049242833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3961130913/10000000000 : ℝ)^5999 ≤ (32736983873153/100000000000000 : ℝ)^4975 := by
    have hnat : (3961130913 : ℕ)^5999*100000000000000^4975 ≤ 32736983873153^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3961130913 10000000000 32736983873153 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5003021191/10000000000 : ℝ)^5999 ≤ (8676720103051/20000000000000 : ℝ)^4975 := by
    have hnat : (5003021191 : ℕ)^5999*20000000000000^4975 ≤ 8676720103051^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5003021191 10000000000 8676720103051 20000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3049242833/10000000000 : ℝ)^5999 ≤ (4775883120133/20000000000000 : ℝ)^4975 := by
    have hnat : (3049242833 : ℕ)^5999*20000000000000^4975 ≤ 4775883120133^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3049242833 10000000000 4775883120133 20000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3961130913/10000000000 : ℝ), (5003021191/10000000000 : ℝ), (3049242833/10000000000 : ℝ)] ![(32736983873153/100000000000000 : ℝ), (8676720103051/20000000000000 : ℝ), (4775883120133/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3961130913/10000000000 : ℝ)|^5999 ≤ (32736983873153/100000000000000 : ℝ)^4975
        have hw : |(3961130913/10000000000 : ℝ)|=(3961130913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5003021191/10000000000 : ℝ)|^5999 ≤ (8676720103051/20000000000000 : ℝ)^4975
        have hw : |(5003021191/10000000000 : ℝ)|=(5003021191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3049242833/10000000000 : ℝ)|^5999 ≤ (4775883120133/20000000000000 : ℝ)^4975
        have hw : |(3049242833/10000000000 : ℝ)|=(3049242833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1764_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44738407/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (181/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20093/100000 : ℝ)*pair X 0 0 := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
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
  have hpowlo : (0 : ℝ) ^ (5983/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5983 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5983*1^1024 ≤ 0^1024*1^5983 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5983 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5983 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5983/1024 : ℝ) ≤ (47307139397986027/10000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5983 ≤ (47307139397986027/10000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5983*10000000000000000000^1024 ≤ 47307139397986027^1024*5^5983 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 47307139397986027 10000000000000000000 5983 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (47307139397986027/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5983 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5983/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5983 := by
      have hnat : (1 : ℕ)^1024*1^5983 ≤ 1^5983*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5983 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5983 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10047307139397986027/10000000000000000000 : ℝ) ≤ (10008080864298673/10000000000000000 : ℝ) ^ (5983/1024 : ℝ) := by
    have hpowers : (10047307139397986027/10000000000000000000 : ℝ)^1024 ≤ (10008080864298673/10000000000000000 : ℝ)^5983 := by
      have hnat : (10047307139397986027 : ℕ)^1024*10000000000000000^5983 ≤ 10008080864298673^5983*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10047307139397986027 10000000000000000000 10008080864298673 10000000000000000 1024 5983 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008080864298673/10000000000000000 : ℝ)) (X := (10047307139397986027/10000000000000000000 : ℝ)) (by norm_num) 5983 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5047307139397986027/5000000000000000000 : ℝ) ≤ (5008080864298673/5000000000000000 : ℝ) ^ (5983/1024 : ℝ) := by
    have hpowers : (5047307139397986027/5000000000000000000 : ℝ)^1024 ≤ (5008080864298673/5000000000000000 : ℝ)^5983 := by
      have hnat : (5047307139397986027 : ℕ)^1024*5000000000000000^5983 ≤ 5008080864298673^5983*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5047307139397986027 5000000000000000000 5008080864298673 5000000000000000 1024 5983 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5008080864298673/5000000000000000 : ℝ)) (X := (5047307139397986027/5000000000000000000 : ℝ)) (by norm_num) 5983 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(8080864298673/4000000000000000 : ℝ)*(0 : ℝ))^(5983/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(8080864298673/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(47307139397986027/10000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(8080864298673/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5983/1024 : ℝ) := by
    rw [show (1 : ℝ)+(8080864298673/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10008080864298673/10000000000000000 : ℝ) by norm_num, show 1+(47307139397986027/10000000000000000000 : ℝ)+(0 : ℝ)=(10047307139397986027/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(47307139397986027/10000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(8080864298673/4000000000000000 : ℝ)*(2/5 : ℝ))^(5983/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(8080864298673/4000000000000000 : ℝ)*(2/5 : ℝ)=(5008080864298673/5000000000000000 : ℝ) by norm_num, show 1+2*(47307139397986027/10000000000000000000 : ℝ)=(5047307139397986027/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(8080864298673/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5983/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (8080864298673/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(8080864298673/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5983/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (8080864298673/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(8080864298673/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5983/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (8080864298673/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-556576341/5000000000 : ℝ)*X 0 0+(5589792669/10000000000 : ℝ)*X 0 1+(2498687903/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1071212679/2000000000 : ℝ)*X 1 0+(-22327241/156250000 : ℝ)*X 1 1+(2498687691/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1071212089/2000000000 : ℝ)*X 2 0+(2498688653/5000000000 : ℝ)*X 2 1+(-1428944807/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1978649943/5000000000 : ℝ)*X 0 0+(1498172991/5000000000 : ℝ)*X 0 1+(5054303873/10000000000 : ℝ)*X 0 2+(1978649943/5000000000 : ℝ)*X 1 0+(1498172991/5000000000 : ℝ)*X 1 1+(5054303873/10000000000 : ℝ)*X 1 2+(1978649943/5000000000 : ℝ)*X 2 0+(1498172991/5000000000 : ℝ)*X 2 1+(5054303873/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-222851251/2000000000 : ℝ)*X 0 0+(5012139289/10000000000 : ℝ)*X 0 1+(5574565309/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((324941163/625000000 : ℝ)*X 1 0+(-42587763/500000000 : ℝ)*X 1 1+(348410331/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2599529431/5000000000 : ℝ)*X 2 0+(5574565297/10000000000 : ℝ)*X 2 1+(-851754889/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3961130913/10000000000 : ℝ)*X 0 0+(5003021191/10000000000 : ℝ)*X 0 1+(3049242833/10000000000 : ℝ)*X 0 2+(3961130913/10000000000 : ℝ)*X 1 0+(5003021191/10000000000 : ℝ)*X 1 1+(3049242833/10000000000 : ℝ)*X 1 2+(3961130913/10000000000 : ℝ)*X 2 0+(5003021191/10000000000 : ℝ)*X 2 1+(3049242833/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1225431468707875339069941/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (384910333/100000000000000 : ℝ)*(base1) + (53086073/50000000000000 : ℝ)*(base16) + (1295261101/100000000000000 : ℝ)*(base19) + (221337319/50000000000000 : ℝ)*(base23) + (330986691/100000000000000 : ℝ)*(upper3) + (1086962689836387/100000000000000 : ℝ)*(major0) + (1086962689836387/100000000000000 : ℝ)*(major1) + (1086962689836387/100000000000000 : ℝ)*(major2) + (844003148230877/50000000000000 : ℝ)*(sp0) + (844002255059087/50000000000000 : ℝ)*(sp1) + (422001119521453/25000000000000 : ℝ)*(sp2) + (242959211367189/50000000000000 : ℝ)*(sp3) + (990790971/100000000000000 : ℝ)*(sp6) + (228119029/50000000000000 : ℝ)*(sp7) + (48591926388277/10000000000000 : ℝ)*(f.failure) + (1688005911551421/100000000000000 : ℝ)*(f.sum) + (328451144414451/200000000000000000000000000000 : ℝ)*base65 + (541475208785549/400000000000000000000000000000 : ℝ)*base68 + (705896658414451/400000000000000000000000000000 : ℝ)*base69 + (1239376434414451/400000000000000000000000000000 : ℝ)*base71 + (1015446171614451/200000000000000000000000000000 : ℝ)*base73 + (780109160814451/400000000000000000000000000000 : ℝ)*base75 + (1260783810385549/400000000000000000000000000000 : ℝ)*base78 + (1173008981985549/400000000000000000000000000000 : ℝ)*base80 + (1115080110214451/200000000000000000000000000000 : ℝ)*base81 + (2454739/200000000000000000000 : ℝ)*base89 + (2454739/200000000000000000000 : ℝ)*base91 + (2454739/200000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (87794952860138956150323/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (201124757/25000000000000 : ℝ)*(base19) + (37853027/4000000000000 : ℝ)*(base23) + (23336729/12500000000000 : ℝ)*(base32) + (93753627/50000000000000 : ℝ)*(upper3) + (18075699/25000000000000 : ℝ)*(upper5) + (286229877790483/25000000000000 : ℝ)*(major0) + (286229877790483/25000000000000 : ℝ)*(major1) + (286229877790483/25000000000000 : ℝ)*(major2) + (359948953/12500000000000 : ℝ)*(sp1) + (4699699979/100000000000000 : ℝ)*(sp2) + (1778010322267803/100000000000000 : ℝ)*(sp4) + (1778006638177151/100000000000000 : ℝ)*(sp5) + (1778004676242149/100000000000000 : ℝ)*(sp6) + (31989267452647/6250000000000 : ℝ)*(sp7) + (63978558242023/12500000000000 : ℝ)*(f.failure) + (1778010322267803/100000000000000 : ℝ)*(f.sum) + (77498148379059/50000000000000000000000000000 : ℝ)*base65 + (302237299029059/100000000000000000000000000000 : ℝ)*base67 + (118155694629059/100000000000000000000000000000 : ℝ)*base69 + (158256962529059/100000000000000000000000000000 : ℝ)*base71 + (30689809129059/50000000000000000000000000000 : ℝ)*base73 + (66274899070941/100000000000000000000000000000 : ℝ)*base76 + (326743382029059/100000000000000000000000000000 : ℝ)*base77 + (422899476970941/100000000000000000000000000000 : ℝ)*base80 + (25037243829059/50000000000000000000000000000 : ℝ)*base81 + (522639/250000000000000000000 : ℝ)*base90 + (522639/250000000000000000000 : ℝ)*base92 + (522639/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1764_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44738407/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (181/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20093/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1764_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1764_s1_0 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1147828213/10000000000 : ℝ)*x 0 + (274029543/500000000 : ℝ)*x 1 + (508321147/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1147828213/10000000000 : ℝ)^5999 ≤ (1470287129001/20000000000000 : ℝ)^4975 := by
    have hnat : (1147828213 : ℕ)^5999*20000000000000^4975 ≤ 1470287129001^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1147828213 10000000000 1470287129001 20000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (274029543/500000000 : ℝ)^5999 ≤ (2421254548627/5000000000000 : ℝ)^4975 := by
    have hnat : (274029543 : ℕ)^5999*5000000000000^4975 ≤ 2421254548627^4975*500000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274029543 500000000 2421254548627 5000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (508321147/1000000000 : ℝ)^5999 ≤ (8844694672047/20000000000000 : ℝ)^4975 := by
    have hnat : (508321147 : ℕ)^5999*20000000000000^4975 ≤ 8844694672047^4975*1000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508321147 1000000000 8844694672047 20000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1147828213/10000000000 : ℝ), (274029543/500000000 : ℝ), (508321147/1000000000 : ℝ)] ![(1470287129001/20000000000000 : ℝ), (2421254548627/5000000000000 : ℝ), (8844694672047/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1147828213/10000000000 : ℝ)|^5999 ≤ (1470287129001/20000000000000 : ℝ)^4975
        have hw : |(-1147828213/10000000000 : ℝ)|=(1147828213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(274029543/500000000 : ℝ)|^5999 ≤ (2421254548627/5000000000000 : ℝ)^4975
        have hw : |(274029543/500000000 : ℝ)|=(274029543/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(508321147/1000000000 : ℝ)|^5999 ≤ (8844694672047/20000000000000 : ℝ)^4975
        have hw : |(508321147/1000000000 : ℝ)|=(508321147/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1764_s1_1 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5327092649/10000000000 : ℝ)*x 0 + (-271057801/2000000000 : ℝ)*x 1 + (2541605661/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5327092649/10000000000 : ℝ)^5999 ≤ (9358881914603/20000000000000 : ℝ)^4975 := by
    have hnat : (5327092649 : ℕ)^5999*20000000000000^4975 ≤ 9358881914603^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5327092649 10000000000 9358881914603 20000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271057801/2000000000 : ℝ)^5999 ≤ (8982118608699/100000000000000 : ℝ)^4975 := by
    have hnat : (271057801 : ℕ)^5999*100000000000000^4975 ≤ 8982118608699^4975*2000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271057801 2000000000 8982118608699 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2541605661/5000000000 : ℝ)^5999 ≤ (353787774461/800000000000 : ℝ)^4975 := by
    have hnat : (2541605661 : ℕ)^5999*800000000000^4975 ≤ 353787774461^4975*5000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2541605661 5000000000 353787774461 800000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5327092649/10000000000 : ℝ), (-271057801/2000000000 : ℝ), (2541605661/5000000000 : ℝ)] ![(9358881914603/20000000000000 : ℝ), (8982118608699/100000000000000 : ℝ), (353787774461/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5327092649/10000000000 : ℝ)|^5999 ≤ (9358881914603/20000000000000 : ℝ)^4975
        have hw : |(5327092649/10000000000 : ℝ)|=(5327092649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-271057801/2000000000 : ℝ)|^5999 ≤ (8982118608699/100000000000000 : ℝ)^4975
        have hw : |(-271057801/2000000000 : ℝ)|=(271057801/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2541605661/5000000000 : ℝ)|^5999 ≤ (353787774461/800000000000 : ℝ)^4975
        have hw : |(2541605661/5000000000 : ℝ)|=(2541605661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1764_s1_2 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2663546271/5000000000 : ℝ)*x 0 + (5083211459/10000000000 : ℝ)*x 1 + (-1355288967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2663546271/5000000000 : ℝ)^5999 ≤ (46794408439641/100000000000000 : ℝ)^4975 := by
    have hnat : (2663546271 : ℕ)^5999*100000000000000^4975 ≤ 46794408439641^4975*5000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2663546271 5000000000 46794408439641 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5083211459/10000000000 : ℝ)^5999 ≤ (22111736622419/50000000000000 : ℝ)^4975 := by
    have hnat : (5083211459 : ℕ)^5999*50000000000000^4975 ≤ 22111736622419^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5083211459 10000000000 22111736622419 50000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1355288967/10000000000 : ℝ)^5999 ≤ (8982118305019/100000000000000 : ℝ)^4975 := by
    have hnat : (1355288967 : ℕ)^5999*100000000000000^4975 ≤ 8982118305019^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355288967 10000000000 8982118305019 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2663546271/5000000000 : ℝ), (5083211459/10000000000 : ℝ), (-1355288967/10000000000 : ℝ)] ![(46794408439641/100000000000000 : ℝ), (22111736622419/50000000000000 : ℝ), (8982118305019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2663546271/5000000000 : ℝ)|^5999 ≤ (46794408439641/100000000000000 : ℝ)^4975
        have hw : |(2663546271/5000000000 : ℝ)|=(2663546271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5083211459/10000000000 : ℝ)|^5999 ≤ (22111736622419/50000000000000 : ℝ)^4975
        have hw : |(5083211459/10000000000 : ℝ)|=(5083211459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1355288967/10000000000 : ℝ)|^5999 ≤ (8982118305019/100000000000000 : ℝ)^4975
        have hw : |(-1355288967/10000000000 : ℝ)|=(1355288967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1764_s1_3 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3992404909/10000000000 : ℝ)*x 0 + (833164391/2500000000 : ℝ)*x 1 + (4713090389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3992404909/10000000000 : ℝ)^5999 ≤ (1321956080249/4000000000000 : ℝ)^4975 := by
    have hnat : (3992404909 : ℕ)^5999*4000000000000^4975 ≤ 1321956080249^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3992404909 10000000000 1321956080249 4000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (833164391/2500000000 : ℝ)^5999 ≤ (26580742434449/100000000000000 : ℝ)^4975 := by
    have hnat : (833164391 : ℕ)^5999*100000000000000^4975 ≤ 26580742434449^4975*2500000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833164391 2500000000 26580742434449 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4713090389/10000000000 : ℝ)^5999 ≤ (20185177775313/50000000000000 : ℝ)^4975 := by
    have hnat : (4713090389 : ℕ)^5999*50000000000000^4975 ≤ 20185177775313^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4713090389 10000000000 20185177775313 50000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3992404909/10000000000 : ℝ), (833164391/2500000000 : ℝ), (4713090389/10000000000 : ℝ)] ![(1321956080249/4000000000000 : ℝ), (26580742434449/100000000000000 : ℝ), (20185177775313/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3992404909/10000000000 : ℝ)|^5999 ≤ (1321956080249/4000000000000 : ℝ)^4975
        have hw : |(3992404909/10000000000 : ℝ)|=(3992404909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(833164391/2500000000 : ℝ)|^5999 ≤ (26580742434449/100000000000000 : ℝ)^4975
        have hw : |(833164391/2500000000 : ℝ)|=(833164391/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4713090389/10000000000 : ℝ)|^5999 ≤ (20185177775313/50000000000000 : ℝ)^4975
        have hw : |(4713090389/10000000000 : ℝ)|=(4713090389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1764_s1_4 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1148159841/10000000000 : ℝ)*x 0 + (19882321/39062500 : ℝ)*x 1 + (5473788439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1148159841/10000000000 : ℝ)^5999 ≤ (1838499213687/25000000000000 : ℝ)^4975 := by
    have hnat : (1148159841 : ℕ)^5999*25000000000000^4975 ≤ 1838499213687^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1148159841 10000000000 1838499213687 25000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (19882321/39062500 : ℝ)^5999 ≤ (22146689294227/50000000000000 : ℝ)^4975 := by
    have hnat : (19882321 : ℕ)^5999*50000000000000^4975 ≤ 22146689294227^4975*39062500^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19882321 39062500 22146689294227 50000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5473788439/10000000000 : ℝ)^5999 ≤ (48352624545317/100000000000000 : ℝ)^4975 := by
    have hnat : (5473788439 : ℕ)^5999*100000000000000^4975 ≤ 48352624545317^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5473788439 10000000000 48352624545317 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1148159841/10000000000 : ℝ), (19882321/39062500 : ℝ), (5473788439/10000000000 : ℝ)] ![(1838499213687/25000000000000 : ℝ), (22146689294227/50000000000000 : ℝ), (48352624545317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1148159841/10000000000 : ℝ)|^5999 ≤ (1838499213687/25000000000000 : ℝ)^4975
        have hw : |(-1148159841/10000000000 : ℝ)|=(1148159841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(19882321/39062500 : ℝ)|^5999 ≤ (22146689294227/50000000000000 : ℝ)^4975
        have hw : |(19882321/39062500 : ℝ)|=(19882321/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5473788439/10000000000 : ℝ)|^5999 ≤ (48352624545317/100000000000000 : ℝ)^4975
        have hw : |(5473788439/10000000000 : ℝ)|=(5473788439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1764_s1_5 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2611111127/5000000000 : ℝ)*x 0 + (-192942399/2000000000 : ℝ)*x 1 + (684223539/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2611111127/5000000000 : ℝ)^5999 ≤ (11421463803901/25000000000000 : ℝ)^4975 := by
    have hnat : (2611111127 : ℕ)^5999*25000000000000^4975 ≤ 11421463803901^4975*5000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2611111127 5000000000 11421463803901 25000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (192942399/2000000000 : ℝ)^5999 ≤ (1192304315573/20000000000000 : ℝ)^4975 := by
    have hnat : (192942399 : ℕ)^5999*20000000000000^4975 ≤ 1192304315573^4975*2000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192942399 2000000000 1192304315573 20000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (684223539/1250000000 : ℝ)^5999 ≤ (24176311596277/50000000000000 : ℝ)^4975 := by
    have hnat : (684223539 : ℕ)^5999*50000000000000^4975 ≤ 24176311596277^4975*1250000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684223539 1250000000 24176311596277 50000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2611111127/5000000000 : ℝ), (-192942399/2000000000 : ℝ), (684223539/1250000000 : ℝ)] ![(11421463803901/25000000000000 : ℝ), (1192304315573/20000000000000 : ℝ), (24176311596277/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2611111127/5000000000 : ℝ)|^5999 ≤ (11421463803901/25000000000000 : ℝ)^4975
        have hw : |(2611111127/5000000000 : ℝ)|=(2611111127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-192942399/2000000000 : ℝ)|^5999 ≤ (1192304315573/20000000000000 : ℝ)^4975
        have hw : |(-192942399/2000000000 : ℝ)|=(192942399/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(684223539/1250000000 : ℝ)|^5999 ≤ (24176311596277/50000000000000 : ℝ)^4975
        have hw : |(684223539/1250000000 : ℝ)|=(684223539/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1764_s1_6 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5222222399/10000000000 : ℝ)*x 0 + (68422353/125000000 : ℝ)*x 1 + (-964711893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5222222399/10000000000 : ℝ)^5999 ≤ (11421464186303/25000000000000 : ℝ)^4975 := by
    have hnat : (5222222399 : ℕ)^5999*25000000000000^4975 ≤ 11421464186303^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5222222399 10000000000 11421464186303 25000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (68422353/125000000 : ℝ)^5999 ≤ (24176311212817/50000000000000 : ℝ)^4975 := by
    have hnat : (68422353 : ℕ)^5999*50000000000000^4975 ≤ 24176311212817^4975*125000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68422353 125000000 24176311212817 50000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (964711893/10000000000 : ℝ)^5999 ≤ (596152081781/10000000000000 : ℝ)^4975 := by
    have hnat : (964711893 : ℕ)^5999*10000000000000^4975 ≤ 596152081781^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      964711893 10000000000 596152081781 10000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5222222399/10000000000 : ℝ), (68422353/125000000 : ℝ), (-964711893/10000000000 : ℝ)] ![(11421464186303/25000000000000 : ℝ), (24176311212817/50000000000000 : ℝ), (596152081781/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5222222399/10000000000 : ℝ)|^5999 ≤ (11421464186303/25000000000000 : ℝ)^4975
        have hw : |(5222222399/10000000000 : ℝ)|=(5222222399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(68422353/125000000 : ℝ)|^5999 ≤ (24176311212817/50000000000000 : ℝ)^4975
        have hw : |(68422353/125000000 : ℝ)|=(68422353/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-964711893/10000000000 : ℝ)|^5999 ≤ (596152081781/10000000000000 : ℝ)^4975
        have hw : |(-964711893/10000000000 : ℝ)|=(964711893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1764_s1_7 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3993557233/10000000000 : ℝ)*x 0 + (4689945467/10000000000 : ℝ)*x 1 + (1678144023/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3993557233/10000000000 : ℝ)^5999 ≤ (8265101149703/25000000000000 : ℝ)^4975 := by
    have hnat : (3993557233 : ℕ)^5999*25000000000000^4975 ≤ 8265101149703^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3993557233 10000000000 8265101149703 25000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4689945467/10000000000 : ℝ)^5999 ≤ (40131421264319/100000000000000 : ℝ)^4975 := by
    have hnat : (4689945467 : ℕ)^5999*100000000000000^4975 ≤ 40131421264319^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4689945467 10000000000 40131421264319 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1678144023/5000000000 : ℝ)^5999 ≤ (2680817412513/10000000000000 : ℝ)^4975 := by
    have hnat : (1678144023 : ℕ)^5999*10000000000000^4975 ≤ 2680817412513^4975*5000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1678144023 5000000000 2680817412513 10000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3993557233/10000000000 : ℝ), (4689945467/10000000000 : ℝ), (1678144023/5000000000 : ℝ)] ![(8265101149703/25000000000000 : ℝ), (40131421264319/100000000000000 : ℝ), (2680817412513/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3993557233/10000000000 : ℝ)|^5999 ≤ (8265101149703/25000000000000 : ℝ)^4975
        have hw : |(3993557233/10000000000 : ℝ)|=(3993557233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4689945467/10000000000 : ℝ)|^5999 ≤ (40131421264319/100000000000000 : ℝ)^4975
        have hw : |(4689945467/10000000000 : ℝ)|=(4689945467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1678144023/5000000000 : ℝ)|^5999 ≤ (2680817412513/10000000000000 : ℝ)^4975
        have hw : |(1678144023/5000000000 : ℝ)|=(1678144023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1764_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44738407/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20093/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (181/2500 : ℝ)*pair X i i ≤ pair X i h) :
    (2291/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1109/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20093/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (181/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20093/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (181/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20093/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (181/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20093/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (181/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20093/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (181/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20093/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (181/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (181/2500 : ℝ) ^ (5983/1024 : ℝ) ≤ (1088130007619/5000000000000000000 : ℝ) := by
    have hpowers : (181/2500 : ℝ)^5983 ≤ (1088130007619/5000000000000000000 : ℝ)^1024 := by
      have hnat : (181 : ℕ)^5983*5000000000000000000^1024 ≤ 1088130007619^1024*2500^5983 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        181 2500 1088130007619 5000000000000000000 5983 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (181/2500 : ℝ)) (X := (1088130007619/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5983 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (20093/100000 : ℝ) ^ (5983/1024 : ℝ) ≤ (338772828032171/4000000000000000000 : ℝ) := by
    have hpowers : (20093/100000 : ℝ)^5983 ≤ (338772828032171/4000000000000000000 : ℝ)^1024 := by
      have hnat : (20093 : ℕ)^5983*4000000000000000000^1024 ≤ 338772828032171^1024*100000^5983 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20093 100000 338772828032171 4000000000000000000 5983 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20093/100000 : ℝ)) (X := (338772828032171/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5983 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500001088130007619/2500000000000000000 : ℝ) ≤ (10000000744940617/10000000000000000 : ℝ) ^ (5983/1024 : ℝ) := by
    have hpowers : (2500001088130007619/2500000000000000000 : ℝ)^1024 ≤ (10000000744940617/10000000000000000 : ℝ)^5983 := by
      have hnat : (2500001088130007619 : ℕ)^1024*10000000000000000^5983 ≤ 10000000744940617^5983*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500001088130007619 2500000000000000000 10000000744940617 10000000000000000 1024 5983 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000744940617/10000000000000000 : ℝ)) (X := (2500001088130007619/2500000000000000000 : ℝ)) (by norm_num) 5983 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20001698216660191331/20000000000000000000 : ℝ) ≤ (5000072660566199/5000000000000000 : ℝ) ^ (5983/1024 : ℝ) := by
    have hpowers : (20001698216660191331/20000000000000000000 : ℝ)^1024 ≤ (5000072660566199/5000000000000000 : ℝ)^5983 := by
      have hnat : (20001698216660191331 : ℕ)^1024*5000000000000000^5983 ≤ 5000072660566199^5983*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20001698216660191331 20000000000000000000 5000072660566199 5000000000000000 1024 5983 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000072660566199/5000000000000000 : ℝ)) (X := (20001698216660191331/20000000000000000000 : ℝ)) (by norm_num) 5983 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2000338772828032171/2000000000000000000 : ℝ) ≤ (10000289897324179/10000000000000000 : ℝ) ^ (5983/1024 : ℝ) := by
    have hpowers : (2000338772828032171/2000000000000000000 : ℝ)^1024 ≤ (10000289897324179/10000000000000000 : ℝ)^5983 := by
      have hnat : (2000338772828032171 : ℕ)^1024*10000000000000000^5983 ≤ 10000289897324179^5983*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000338772828032171 2000000000000000000 10000289897324179 10000000000000000 1024 5983 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000289897324179/10000000000000000 : ℝ)) (X := (2000338772828032171/2000000000000000000 : ℝ)) (by norm_num) 5983 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1088130007619/5000000000000000000 : ℝ) ≤ ((128527916111464761421/128530000000000000000 : ℝ)+2*(144576191781/1285300000000000 : ℝ)*(181/2500 : ℝ))^(5983/1024 : ℝ) := by
    rw [show (128527916111464761421/128530000000000000000 : ℝ)+2*(144576191781/1285300000000000 : ℝ)*(181/2500 : ℝ)=(10000000744940617/10000000000000000 : ℝ) by norm_num, show 1+2*(1088130007619/5000000000000000000 : ℝ)=(2500001088130007619/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(338772828032171/4000000000000000000 : ℝ)+(1088130007619/5000000000000000000 : ℝ) ≤ ((128527916111464761421/128530000000000000000 : ℝ)+(144576191781/1285300000000000 : ℝ)*((20093/100000 : ℝ)+(181/2500 : ℝ)))^(5983/1024 : ℝ) := by
    rw [show (128527916111464761421/128530000000000000000 : ℝ)+(144576191781/1285300000000000 : ℝ)*((20093/100000 : ℝ)+(181/2500 : ℝ))=(5000072660566199/5000000000000000 : ℝ) by norm_num, show 1+(338772828032171/4000000000000000000 : ℝ)+(1088130007619/5000000000000000000 : ℝ)=(20001698216660191331/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(338772828032171/4000000000000000000 : ℝ) ≤ ((128527916111464761421/128530000000000000000 : ℝ)+2*(144576191781/1285300000000000 : ℝ)*(20093/100000 : ℝ))^(5983/1024 : ℝ) := by
    rw [show (128527916111464761421/128530000000000000000 : ℝ)+2*(144576191781/1285300000000000 : ℝ)*(20093/100000 : ℝ)=(10000289897324179/10000000000000000 : ℝ) by norm_num, show 1+2*(338772828032171/4000000000000000000 : ℝ)=(2000338772828032171/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (128527916111464761421/128530000000000000000 : ℝ)*(X 1 0+X 2 0)+(144576191781/1285300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5983/1024 : ℝ)) (lo := (181/2500 : ℝ)) (hi := (20093/100000 : ℝ)) (c := (128527916111464761421/128530000000000000000 : ℝ)) (alpha := (144576191781/1285300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (128527916111464761421/128530000000000000000 : ℝ)*(X 0 1+X 2 1)+(144576191781/1285300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5983/1024 : ℝ)) (lo := (181/2500 : ℝ)) (hi := (20093/100000 : ℝ)) (c := (128527916111464761421/128530000000000000000 : ℝ)) (alpha := (144576191781/1285300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (128527916111464761421/128530000000000000000 : ℝ)*(X 0 2+X 1 2)+(144576191781/1285300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5983/1024 : ℝ)) (lo := (181/2500 : ℝ)) (hi := (20093/100000 : ℝ)) (c := (128527916111464761421/128530000000000000000 : ℝ)) (alpha := (144576191781/1285300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1147828213/10000000000 : ℝ)*X 0 0+(274029543/500000000 : ℝ)*X 0 1+(508321147/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5327092649/10000000000 : ℝ)*X 1 0+(-271057801/2000000000 : ℝ)*X 1 1+(2541605661/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2663546271/5000000000 : ℝ)*X 2 0+(5083211459/10000000000 : ℝ)*X 2 1+(-1355288967/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((3992404909/10000000000 : ℝ)*X 0 0+(833164391/2500000000 : ℝ)*X 0 1+(4713090389/10000000000 : ℝ)*X 0 2+(3992404909/10000000000 : ℝ)*X 1 0+(833164391/2500000000 : ℝ)*X 1 1+(4713090389/10000000000 : ℝ)*X 1 2+(3992404909/10000000000 : ℝ)*X 2 0+(833164391/2500000000 : ℝ)*X 2 1+(4713090389/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1148159841/10000000000 : ℝ)*X 0 0+(19882321/39062500 : ℝ)*X 0 1+(5473788439/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2611111127/5000000000 : ℝ)*X 1 0+(-192942399/2000000000 : ℝ)*X 1 1+(684223539/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5222222399/10000000000 : ℝ)*X 2 0+(68422353/125000000 : ℝ)*X 2 1+(-964711893/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3993557233/10000000000 : ℝ)*X 0 0+(4689945467/10000000000 : ℝ)*X 0 1+(1678144023/5000000000 : ℝ)*X 0 2+(3993557233/10000000000 : ℝ)*X 1 0+(4689945467/10000000000 : ℝ)*X 1 1+(1678144023/5000000000 : ℝ)*X 1 2+(3993557233/10000000000 : ℝ)*X 2 0+(4689945467/10000000000 : ℝ)*X 2 1+(1678144023/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11591881699001797227749088621/803312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (389191719/20000000000000 : ℝ)*(base19) + (442021729/25000000000000 : ℝ)*(base23) + (3391359/5000000000000 : ℝ)*(lower2) + (335185991/100000000000000 : ℝ)*(upper3) + (32103613/12500000000000 : ℝ)*(upper5) + (202558543401433/12500000000000 : ℝ)*(major0) + (202558543401433/12500000000000 : ℝ)*(major1) + (202558543401433/12500000000000 : ℝ)*(major2) + (503300383875277/20000000000000 : ℝ)*(sp0) + (1258257467389081/50000000000000 : ℝ)*(sp1) + (2516515112649841/100000000000000 : ℝ)*(sp2) + (5659489007513/781250000000 : ℝ)*(sp3) + (3740340093/25000000000000 : ℝ)*(sp4) + (2369860543/50000000000000 : ℝ)*(sp7) + (2897677330731/400000000000 : ℝ)*(f.failure) + (2516516880736757/100000000000000 : ℝ)*(f.sum) + (309314928848779/64265000000000000000000000000 : ℝ)*base65 + (3590230266618066293/1606625000000000000000000000000000 : ℝ)*base67 + (5036257141486933707/1606625000000000000000000000000000 : ℝ)*base70 + (2205695965540183707/1606625000000000000000000000000000 : ℝ)*base72 + (38047565971333/8033125000000000000000000000 : ℝ)*base73 + (5902810812660816293/1606625000000000000000000000000000 : ℝ)*base75 + (3236497702778316293/1606625000000000000000000000000000 : ℝ)*base77 + (3875673792331691293/1606625000000000000000000000000000 : ℝ)*base79 + (246322076508941/64265000000000000000000000000 : ℝ)*base82 + (34483/8000000000000000000 : ℝ)*base90 + (34483/8000000000000000000 : ℝ)*base92 + (34483/8000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4777345745373812357742427209/401656250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (36349843/2500000000000 : ℝ)*(base19) + (1727894333/100000000000000 : ℝ)*(base23) + (24619599/10000000000000 : ℝ)*(upper3) + (40554603/50000000000000 : ℝ)*(lower4) + (4232673/2000000000000 : ℝ)*(upper5) + (104830158243407/6250000000000 : ℝ)*(major0) + (104830158243407/6250000000000 : ℝ)*(major1) + (104830158243407/6250000000000 : ℝ)*(major2) + (1939858569/20000000000000 : ℝ)*(sp1) + (2400604003/20000000000000 : ℝ)*(sp2) + (13023734702537/500000000000 : ℝ)*(sp4) + (520947157444167/20000000000000 : ℝ)*(sp5) + (651183302398263/25000000000000 : ℝ)*(sp6) + (74981772681111/10000000000000 : ℝ)*(sp7) + (74981772681111/10000000000000 : ℝ)*(f.failure) + (13023734702537/500000000000 : ℝ)*(f.sum) + (152185497075039/32132500000000000000000000000 : ℝ)*base66 + (1820333804562723653/803312500000000000000000000000000 : ℝ)*base68 + (5645412468364151347/803312500000000000000000000000000 : ℝ)*base69 + (5204590041488661153/803312500000000000000000000000000 : ℝ)*base72 + (36807008400491/8033125000000000000000000000 : ℝ)*base74 + (2617307515393526347/803312500000000000000000000000000 : ℝ)*base75 + (607262321280151347/803312500000000000000000000000000 : ℝ)*base77 + (4219967312678213847/803312500000000000000000000000000 : ℝ)*base79 + (164325611273337/64265000000000000000000000000 : ℝ)*base81 + (1130177/200000000000000000000 : ℝ)*base89 + (1130177/200000000000000000000 : ℝ)*base91 + (1130177/200000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1764_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44738407/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20093/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (181/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2291/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1109/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1764_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1764_s2_0 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1148377111/10000000000 : ℝ)*x 0 + (2739411351/5000000000 : ℝ)*x 1 + (5084603033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1148377111/10000000000 : ℝ)^5999 ≤ (1838918736029/25000000000000 : ℝ)^4975 := by
    have hnat : (1148377111 : ℕ)^5999*25000000000000^4975 ≤ 1838918736029^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1148377111 10000000000 1838918736029 25000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2739411351/5000000000 : ℝ)^5999 ≤ (48406252942321/100000000000000 : ℝ)^4975 := by
    have hnat : (2739411351 : ℕ)^5999*100000000000000^4975 ≤ 48406252942321^4975*5000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2739411351 5000000000 48406252942321 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5084603033/10000000000 : ℝ)^5999 ≤ (44238072106367/100000000000000 : ℝ)^4975 := by
    have hnat : (5084603033 : ℕ)^5999*100000000000000^4975 ≤ 44238072106367^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5084603033 10000000000 44238072106367 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1148377111/10000000000 : ℝ), (2739411351/5000000000 : ℝ), (5084603033/10000000000 : ℝ)] ![(1838918736029/25000000000000 : ℝ), (48406252942321/100000000000000 : ℝ), (44238072106367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1148377111/10000000000 : ℝ)|^5999 ≤ (1838918736029/25000000000000 : ℝ)^4975
        have hw : |(-1148377111/10000000000 : ℝ)|=(1148377111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2739411351/5000000000 : ℝ)|^5999 ≤ (48406252942321/100000000000000 : ℝ)^4975
        have hw : |(2739411351/5000000000 : ℝ)|=(2739411351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5084603033/10000000000 : ℝ)|^5999 ≤ (44238072106367/100000000000000 : ℝ)^4975
        have hw : |(5084603033/10000000000 : ℝ)|=(5084603033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1764_s2_1 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2663298639/5000000000 : ℝ)*x 0 + (-169264813/1250000000 : ℝ)*x 1 + (31778769/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2663298639/5000000000 : ℝ)^5999 ≤ (46789162514339/100000000000000 : ℝ)^4975 := by
    have hnat : (2663298639 : ℕ)^5999*100000000000000^4975 ≤ 46789162514339^4975*5000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2663298639 5000000000 46789162514339 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169264813/1250000000 : ℝ)^5999 ≤ (4486382644007/50000000000000 : ℝ)^4975 := by
    have hnat : (169264813 : ℕ)^5999*50000000000000^4975 ≤ 4486382644007^4975*1250000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169264813 1250000000 4486382644007 50000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (31778769/62500000 : ℝ)^5999 ≤ (8847614435961/20000000000000 : ℝ)^4975 := by
    have hnat : (31778769 : ℕ)^5999*20000000000000^4975 ≤ 8847614435961^4975*62500000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31778769 62500000 8847614435961 20000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2663298639/5000000000 : ℝ), (-169264813/1250000000 : ℝ), (31778769/62500000 : ℝ)] ![(46789162514339/100000000000000 : ℝ), (4486382644007/50000000000000 : ℝ), (8847614435961/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2663298639/5000000000 : ℝ)|^5999 ≤ (46789162514339/100000000000000 : ℝ)^4975
        have hw : |(2663298639/5000000000 : ℝ)|=(2663298639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-169264813/1250000000 : ℝ)|^5999 ≤ (4486382644007/50000000000000 : ℝ)^4975
        have hw : |(-169264813/1250000000 : ℝ)|=(169264813/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(31778769/62500000 : ℝ)|^5999 ≤ (8847614435961/20000000000000 : ℝ)^4975
        have hw : |(31778769/62500000 : ℝ)|=(31778769/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1764_s2_2 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1331649327/2500000000 : ℝ)*x 0 + (5084603021/10000000000 : ℝ)*x 1 + (-135411849/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1331649327/2500000000 : ℝ)^5999 ≤ (46789162832101/100000000000000 : ℝ)^4975 := by
    have hnat : (1331649327 : ℕ)^5999*100000000000000^4975 ≤ 46789162832101^4975*2500000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1331649327 2500000000 46789162832101 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5084603021/10000000000 : ℝ)^5999 ≤ (5529758997559/12500000000000 : ℝ)^4975 := by
    have hnat : (5084603021 : ℕ)^5999*12500000000000^4975 ≤ 5529758997559^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5084603021 10000000000 5529758997559 12500000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135411849/1000000000 : ℝ)^5999 ≤ (1121595647019/12500000000000 : ℝ)^4975 := by
    have hnat : (135411849 : ℕ)^5999*12500000000000^4975 ≤ 1121595647019^4975*1000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135411849 1000000000 1121595647019 12500000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1331649327/2500000000 : ℝ), (5084603021/10000000000 : ℝ), (-135411849/1000000000 : ℝ)] ![(46789162832101/100000000000000 : ℝ), (5529758997559/12500000000000 : ℝ), (1121595647019/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1331649327/2500000000 : ℝ)|^5999 ≤ (46789162832101/100000000000000 : ℝ)^4975
        have hw : |(1331649327/2500000000 : ℝ)|=(1331649327/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5084603021/10000000000 : ℝ)|^5999 ≤ (5529758997559/12500000000000 : ℝ)^4975
        have hw : |(5084603021/10000000000 : ℝ)|=(5084603021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-135411849/1000000000 : ℝ)|^5999 ≤ (1121595647019/12500000000000 : ℝ)^4975
        have hw : |(-135411849/1000000000 : ℝ)|=(135411849/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1764_s2_3 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3992857649/10000000000 : ℝ)*x 0 + (3338114117/10000000000 : ℝ)*x 1 + (4707570457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3992857649/10000000000 : ℝ)^5999 ≤ (33053421212513/100000000000000 : ℝ)^4975 := by
    have hnat : (3992857649 : ℕ)^5999*100000000000000^4975 ≤ 33053421212513^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3992857649 10000000000 33053421212513 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3338114117/10000000000 : ℝ)^5999 ≤ (6658307417877/25000000000000 : ℝ)^4975 := by
    have hnat : (3338114117 : ℕ)^5999*25000000000000^4975 ≤ 6658307417877^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3338114117 10000000000 6658307417877 25000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4707570457/10000000000 : ℝ)^5999 ≤ (20156674553777/50000000000000 : ℝ)^4975 := by
    have hnat : (4707570457 : ℕ)^5999*50000000000000^4975 ≤ 20156674553777^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4707570457 10000000000 20156674553777 50000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3992857649/10000000000 : ℝ), (3338114117/10000000000 : ℝ), (4707570457/10000000000 : ℝ)] ![(33053421212513/100000000000000 : ℝ), (6658307417877/25000000000000 : ℝ), (20156674553777/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3992857649/10000000000 : ℝ)|^5999 ≤ (33053421212513/100000000000000 : ℝ)^4975
        have hw : |(3992857649/10000000000 : ℝ)|=(3992857649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3338114117/10000000000 : ℝ)|^5999 ≤ (6658307417877/25000000000000 : ℝ)^4975
        have hw : |(3338114117/10000000000 : ℝ)|=(3338114117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4707570457/10000000000 : ℝ)|^5999 ≤ (20156674553777/50000000000000 : ℝ)^4975
        have hw : |(4707570457/10000000000 : ℝ)|=(4707570457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1764_s2_4 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-574350509/5000000000 : ℝ)*x 0 + (5091159959/10000000000 : ℝ)*x 1 + (2736064627/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (574350509/5000000000 : ℝ)^5999 ≤ (3679088383951/50000000000000 : ℝ)^4975 := by
    have hnat : (574350509 : ℕ)^5999*50000000000000^4975 ≤ 3679088383951^4975*5000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      574350509 5000000000 3679088383951 50000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5091159959/10000000000 : ℝ)^5999 ≤ (44306871215251/100000000000000 : ℝ)^4975 := by
    have hnat : (5091159959 : ℕ)^5999*100000000000000^4975 ≤ 44306871215251^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5091159959 10000000000 44306871215251 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2736064627/5000000000 : ℝ)^5999 ≤ (48334952000779/100000000000000 : ℝ)^4975 := by
    have hnat : (2736064627 : ℕ)^5999*100000000000000^4975 ≤ 48334952000779^4975*5000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2736064627 5000000000 48334952000779 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-574350509/5000000000 : ℝ), (5091159959/10000000000 : ℝ), (2736064627/5000000000 : ℝ)] ![(3679088383951/50000000000000 : ℝ), (44306871215251/100000000000000 : ℝ), (48334952000779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-574350509/5000000000 : ℝ)|^5999 ≤ (3679088383951/50000000000000 : ℝ)^4975
        have hw : |(-574350509/5000000000 : ℝ)|=(574350509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5091159959/10000000000 : ℝ)|^5999 ≤ (44306871215251/100000000000000 : ℝ)^4975
        have hw : |(5091159959/10000000000 : ℝ)|=(5091159959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2736064627/5000000000 : ℝ)|^5999 ≤ (48334952000779/100000000000000 : ℝ)^4975
        have hw : |(2736064627/5000000000 : ℝ)|=(2736064627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1764_s2_5 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (522256897/1000000000 : ℝ)*x 0 + (-943938/9765625 : ℝ)*x 1 + (5472129077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (522256897/1000000000 : ℝ)^5999 ≤ (22844756377597/50000000000000 : ℝ)^4975 := by
    have hnat : (522256897 : ℕ)^5999*50000000000000^4975 ≤ 22844756377597^4975*1000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522256897 1000000000 22844756377597 50000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (943938/9765625 : ℝ)^5999 ≤ (5975537108771/100000000000000 : ℝ)^4975 := by
    have hnat : (943938 : ℕ)^5999*100000000000000^4975 ≤ 5975537108771^4975*9765625^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      943938 9765625 5975537108771 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5472129077/10000000000 : ℝ)^5999 ≤ (48334950115551/100000000000000 : ℝ)^4975 := by
    have hnat : (5472129077 : ℕ)^5999*100000000000000^4975 ≤ 48334950115551^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5472129077 10000000000 48334950115551 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(522256897/1000000000 : ℝ), (-943938/9765625 : ℝ), (5472129077/10000000000 : ℝ)] ![(22844756377597/50000000000000 : ℝ), (5975537108771/100000000000000 : ℝ), (48334950115551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(522256897/1000000000 : ℝ)|^5999 ≤ (22844756377597/50000000000000 : ℝ)^4975
        have hw : |(522256897/1000000000 : ℝ)|=(522256897/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-943938/9765625 : ℝ)|^5999 ≤ (5975537108771/100000000000000 : ℝ)^4975
        have hw : |(-943938/9765625 : ℝ)|=(943938/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5472129077/10000000000 : ℝ)|^5999 ≤ (48334950115551/100000000000000 : ℝ)^4975
        have hw : |(5472129077/10000000000 : ℝ)|=(5472129077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1764_s2_6 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2611284549/5000000000 : ℝ)*x 0 + (5472129013/10000000000 : ℝ)*x 1 + (-966592423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2611284549/5000000000 : ℝ)^5999 ≤ (2855594631593/6250000000000 : ℝ)^4975 := by
    have hnat : (2611284549 : ℕ)^5999*6250000000000^4975 ≤ 2855594631593^4975*5000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2611284549 5000000000 2855594631593 6250000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5472129013/10000000000 : ℝ)^5999 ≤ (24167474716943/50000000000000 : ℝ)^4975 := by
    have hnat : (5472129013 : ℕ)^5999*50000000000000^4975 ≤ 24167474716943^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5472129013 10000000000 24167474716943 50000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (966592423/10000000000 : ℝ)^5999 ≤ (5975536445319/100000000000000 : ℝ)^4975 := by
    have hnat : (966592423 : ℕ)^5999*100000000000000^4975 ≤ 5975536445319^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      966592423 10000000000 5975536445319 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2611284549/5000000000 : ℝ), (5472129013/10000000000 : ℝ), (-966592423/10000000000 : ℝ)] ![(2855594631593/6250000000000 : ℝ), (24167474716943/50000000000000 : ℝ), (5975536445319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2611284549/5000000000 : ℝ)|^5999 ≤ (2855594631593/6250000000000 : ℝ)^4975
        have hw : |(2611284549/5000000000 : ℝ)|=(2611284549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5472129013/10000000000 : ℝ)|^5999 ≤ (24167474716943/50000000000000 : ℝ)^4975
        have hw : |(5472129013/10000000000 : ℝ)|=(5472129013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-966592423/10000000000 : ℝ)|^5999 ≤ (5975536445319/100000000000000 : ℝ)^4975
        have hw : |(-966592423/10000000000 : ℝ)|=(966592423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1764_s2_7 (p : ℝ) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3993982491/10000000000 : ℝ)*x 0 + (234239589/500000000 : ℝ)*x 1 + (336136699/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3993982491/10000000000 : ℝ)^5999 ≤ (33064649731603/100000000000000 : ℝ)^4975 := by
    have hnat : (3993982491 : ℕ)^5999*100000000000000^4975 ≤ 33064649731603^4975*10000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3993982491 10000000000 33064649731603 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (234239589/500000000 : ℝ)^5999 ≤ (40078250680159/100000000000000 : ℝ)^4975 := by
    have hnat : (234239589 : ℕ)^5999*100000000000000^4975 ≤ 40078250680159^4975*500000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234239589 500000000 40078250680159 100000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (336136699/1000000000 : ℝ)^5999 ≤ (13428549786731/50000000000000 : ℝ)^4975 := by
    have hnat : (336136699 : ℕ)^5999*50000000000000^4975 ≤ 13428549786731^4975*1000000000^5999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336136699 1000000000 13428549786731 50000000000000 5999 4975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5999/1024 : ℝ)) 5999 4975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3993982491/10000000000 : ℝ), (234239589/500000000 : ℝ), (336136699/1000000000 : ℝ)] ![(33064649731603/100000000000000 : ℝ), (40078250680159/100000000000000 : ℝ), (13428549786731/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3993982491/10000000000 : ℝ)|^5999 ≤ (33064649731603/100000000000000 : ℝ)^4975
        have hw : |(3993982491/10000000000 : ℝ)|=(3993982491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(234239589/500000000 : ℝ)|^5999 ≤ (40078250680159/100000000000000 : ℝ)^4975
        have hw : |(234239589/500000000 : ℝ)|=(234239589/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(336136699/1000000000 : ℝ)|^5999 ≤ (13428549786731/50000000000000 : ℝ)^4975
        have hw : |(336136699/1000000000 : ℝ)|=(336136699/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1764_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44738407/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1109/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2291/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1839/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8853/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1109/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2291/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1109/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2291/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1109/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2291/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1109/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2291/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1109/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2291/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1109/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2291/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2291/25000 : ℝ) ^ (5983/1024 : ℝ) ≤ (43118960494493/50000000000000000000 : ℝ) := by
    have hpowers : (2291/25000 : ℝ)^5983 ≤ (43118960494493/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2291 : ℕ)^5983*50000000000000000000^1024 ≤ 43118960494493^1024*25000^5983 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2291 25000 43118960494493 50000000000000000000 5983 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2291/25000 : ℝ)) (X := (43118960494493/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5983 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1109/6250 : ℝ) ^ (5983/1024 : ℝ) ≤ (2048086165107743/50000000000000000000 : ℝ) := by
    have hpowers : (1109/6250 : ℝ)^5983 ≤ (2048086165107743/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1109 : ℕ)^5983*50000000000000000000^1024 ≤ 2048086165107743^1024*6250^5983 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1109 6250 2048086165107743 50000000000000000000 5983 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1109/6250 : ℝ)) (X := (2048086165107743/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5983 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000043118960494493/25000000000000000000 : ℝ) ≤ (625000184496841/625000000000000 : ℝ) ^ (5983/1024 : ℝ) := by
    have hpowers : (25000043118960494493/25000000000000000000 : ℝ)^1024 ≤ (625000184496841/625000000000000 : ℝ)^5983 := by
      have hnat : (25000043118960494493 : ℕ)^1024*625000000000000^5983 ≤ 625000184496841^5983*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000043118960494493 25000000000000000000 625000184496841 625000000000000 1024 5983 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625000184496841/625000000000000 : ℝ)) (X := (25000043118960494493/25000000000000000000 : ℝ)) (by norm_num) 5983 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12500522801281400559/12500000000000000000 : ℝ) ≤ (10000071581378337/10000000000000000 : ℝ) ^ (5983/1024 : ℝ) := by
    have hpowers : (12500522801281400559/12500000000000000000 : ℝ)^1024 ≤ (10000071581378337/10000000000000000 : ℝ)^5983 := by
      have hnat : (12500522801281400559 : ℕ)^1024*10000000000000000^5983 ≤ 10000071581378337^5983*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500522801281400559 12500000000000000000 10000071581378337 10000000000000000 1024 5983 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000071581378337/10000000000000000 : ℝ)) (X := (12500522801281400559/12500000000000000000 : ℝ)) (by norm_num) 5983 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25002048086165107743/25000000000000000000 : ℝ) ≤ (5000070105403609/5000000000000000 : ℝ) ^ (5983/1024 : ℝ) := by
    have hpowers : (25002048086165107743/25000000000000000000 : ℝ)^1024 ≤ (5000070105403609/5000000000000000 : ℝ)^5983 := by
      have hnat : (25002048086165107743 : ℕ)^1024*5000000000000000^5983 ≤ 5000070105403609^5983*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002048086165107743 25000000000000000000 5000070105403609 5000000000000000 1024 5983 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000070105403609/5000000000000000 : ℝ)) (X := (25002048086165107743/25000000000000000000 : ℝ)) (by norm_num) 5983 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(43118960494493/50000000000000000000 : ℝ) ≤ ((824988148918786553/825000000000000000 : ℝ)+2*(5279186837/66000000000000 : ℝ)*(2291/25000 : ℝ))^(5983/1024 : ℝ) := by
    rw [show (824988148918786553/825000000000000000 : ℝ)+2*(5279186837/66000000000000 : ℝ)*(2291/25000 : ℝ)=(625000184496841/625000000000000 : ℝ) by norm_num, show 1+2*(43118960494493/50000000000000000000 : ℝ)=(25000043118960494493/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2048086165107743/50000000000000000000 : ℝ)+(43118960494493/50000000000000000000 : ℝ) ≤ ((824988148918786553/825000000000000000 : ℝ)+(5279186837/66000000000000 : ℝ)*((1109/6250 : ℝ)+(2291/25000 : ℝ)))^(5983/1024 : ℝ) := by
    rw [show (824988148918786553/825000000000000000 : ℝ)+(5279186837/66000000000000 : ℝ)*((1109/6250 : ℝ)+(2291/25000 : ℝ))=(10000071581378337/10000000000000000 : ℝ) by norm_num, show 1+(2048086165107743/50000000000000000000 : ℝ)+(43118960494493/50000000000000000000 : ℝ)=(12500522801281400559/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2048086165107743/50000000000000000000 : ℝ) ≤ ((824988148918786553/825000000000000000 : ℝ)+2*(5279186837/66000000000000 : ℝ)*(1109/6250 : ℝ))^(5983/1024 : ℝ) := by
    rw [show (824988148918786553/825000000000000000 : ℝ)+2*(5279186837/66000000000000 : ℝ)*(1109/6250 : ℝ)=(5000070105403609/5000000000000000 : ℝ) by norm_num, show 1+2*(2048086165107743/50000000000000000000 : ℝ)=(25002048086165107743/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (824988148918786553/825000000000000000 : ℝ)*(X 1 0+X 2 0)+(5279186837/66000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5983/1024 : ℝ)) (lo := (2291/25000 : ℝ)) (hi := (1109/6250 : ℝ)) (c := (824988148918786553/825000000000000000 : ℝ)) (alpha := (5279186837/66000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (824988148918786553/825000000000000000 : ℝ)*(X 0 1+X 2 1)+(5279186837/66000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5983/1024 : ℝ)) (lo := (2291/25000 : ℝ)) (hi := (1109/6250 : ℝ)) (c := (824988148918786553/825000000000000000 : ℝ)) (alpha := (5279186837/66000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (824988148918786553/825000000000000000 : ℝ)*(X 0 2+X 1 2)+(5279186837/66000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5983/1024 : ℝ)) (lo := (2291/25000 : ℝ)) (hi := (1109/6250 : ℝ)) (c := (824988148918786553/825000000000000000 : ℝ)) (alpha := (5279186837/66000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1148377111/10000000000 : ℝ)*X 0 0+(2739411351/5000000000 : ℝ)*X 0 1+(5084603033/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2663298639/5000000000 : ℝ)*X 1 0+(-169264813/1250000000 : ℝ)*X 1 1+(31778769/62500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1331649327/2500000000 : ℝ)*X 2 0+(5084603021/10000000000 : ℝ)*X 2 1+(-135411849/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((3992857649/10000000000 : ℝ)*X 0 0+(3338114117/10000000000 : ℝ)*X 0 1+(4707570457/10000000000 : ℝ)*X 0 2+(3992857649/10000000000 : ℝ)*X 1 0+(3338114117/10000000000 : ℝ)*X 1 1+(4707570457/10000000000 : ℝ)*X 1 2+(3992857649/10000000000 : ℝ)*X 2 0+(3338114117/10000000000 : ℝ)*X 2 1+(4707570457/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-574350509/5000000000 : ℝ)*X 0 0+(5091159959/10000000000 : ℝ)*X 0 1+(2736064627/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((522256897/1000000000 : ℝ)*X 1 0+(-943938/9765625 : ℝ)*X 1 1+(5472129077/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2611284549/5000000000 : ℝ)*X 2 0+(5472129013/10000000000 : ℝ)*X 2 1+(-966592423/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3993982491/10000000000 : ℝ)*X 0 0+(234239589/500000000 : ℝ)*X 0 1+(336136699/1000000000 : ℝ)*X 0 2+(3993982491/10000000000 : ℝ)*X 1 0+(234239589/500000000 : ℝ)*X 1 1+(336136699/1000000000 : ℝ)*X 1 2+(3993982491/10000000000 : ℝ)*X 2 0+(234239589/500000000 : ℝ)*X 2 1+(336136699/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1764_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9404728114107200511038289/687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1823788413/100000000000000 : ℝ)*(base19) + (69695041/4000000000000 : ℝ)*(base23) + (25487577/50000000000000 : ℝ)*(lower2) + (320359147/100000000000000 : ℝ)*(upper3) + (262444099/100000000000000 : ℝ)*(upper5) + (163345617686463/10000000000000 : ℝ)*(major0) + (163345617686463/10000000000000 : ℝ)*(major1) + (163345617686463/10000000000000 : ℝ)*(major2) + (1268335766132751/50000000000000 : ℝ)*(sp0) + (253668462052443/10000000000000 : ℝ)*(sp1) + (1268342350968409/50000000000000 : ℝ)*(sp2) + (91277606957333/12500000000000 : ℝ)*(sp3) + (7456023671/50000000000000 : ℝ)*(sp4) + (4597770927/100000000000000 : ℝ)*(sp7) + (730225453429591/100000000000000 : ℝ)*(f.failure) + (634171611078211/25000000000000 : ℝ)*(f.sum) + (204760304473/110000000000000000000000000 : ℝ)*base66 + (3351729517943487/2750000000000000000000000000000 : ℝ)*base68 + (10702629343443487/2750000000000000000000000000000 : ℝ)*base70 + (2575999901193487/2750000000000000000000000000000 : ℝ)*base72 + (559052656097/110000000000000000000000000 : ℝ)*base73 + (2866935449943487/2750000000000000000000000000000 : ℝ)*base76 + (17355557012193487/2750000000000000000000000000000 : ℝ)*base78 + (4342435543056513/2750000000000000000000000000000 : ℝ)*base79 + (169747549797/110000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (11998463/2000000000000000000000 : ℝ)*base90 + (11998463/2000000000000000000000 : ℝ)*base92 + (11998463/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (64523321351829130305126497/6875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (610688817/50000000000000 : ℝ)*(base19) + (1287444599/100000000000000 : ℝ)*(base23) + (4158033/1250000000000 : ℝ)*(lower1) + (75027119/50000000000000 : ℝ)*(upper3) + (7312387/100000000000000 : ℝ)*(lower4) + (129689391/50000000000000 : ℝ)*(upper5) + (1690244643863099/100000000000000 : ℝ)*(major0) + (1690244643863099/100000000000000 : ℝ)*(major1) + (1690244643863099/100000000000000 : ℝ)*(major2) + (615876893/100000000000000 : ℝ)*(sp1) + (328109578030443/12500000000000 : ℝ)*(sp4) + (328109348373627/12500000000000 : ℝ)*(sp5) + (524975067359789/20000000000000 : ℝ)*(sp6) + (755612350642301/100000000000000 : ℝ)*(sp7) + (755612350642301/100000000000000 : ℝ)*(f.failure) + (328109578030443/12500000000000 : ℝ)*(f.sum) + (19751831631163/3300000000000000000000000000 : ℝ)*base65 + (39768954195868251/27500000000000000000000000000000 : ℝ)*base68 + (311280295670868251/27500000000000000000000000000000 : ℝ)*base70 + (92001638356631749/27500000000000000000000000000000 : ℝ)*base71 + (5790569425063/3300000000000000000000000000 : ℝ)*base73 + (184883057010868251/27500000000000000000000000000000 : ℝ)*base76 + (69331809633368251/27500000000000000000000000000000 : ℝ)*base78 + (138912960393368251/27500000000000000000000000000000 : ℝ)*base80 + (20648175013637/3300000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (6445493/2000000000000000000000 : ℝ)*base90 + (6445493/2000000000000000000000 : ℝ)*base92 + (6445493/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1764_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44738407/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1109/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2291/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1839/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8853/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1764_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1764_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44738407/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1839/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8853/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1764_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1764_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1764_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5983/1024 : ℝ) ≤ p) (hpb : p ≤ (5999/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44738407/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1839/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8853/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1764_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1650_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:12:38.350189+00:00
-- url     : https://prove2.me/submissions/ffa8fb14-d2ed-49da-984d-1123f704bbed

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
theorem support_rectangle_w1650_s0_0 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-373164093/2500000000 : ℝ)*x 0 + (1446324033/2500000000 : ℝ)*x 1 + (1230390347/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (373164093/2500000000 : ℝ)^4919 ≤ (2263252117269/25000000000000 : ℝ)^3895 := by
    have hnat : (373164093 : ℕ)^4919*25000000000000^3895 ≤ 2263252117269^3895*2500000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      373164093 2500000000 2263252117269 25000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1446324033/2500000000 : ℝ)^4919 ≤ (50100345193731/100000000000000 : ℝ)^3895 := by
    have hnat : (1446324033 : ℕ)^4919*100000000000000^3895 ≤ 50100345193731^3895*2500000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1446324033 2500000000 50100345193731 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1230390347/2500000000 : ℝ)^4919 ≤ (40846646321621/100000000000000 : ℝ)^3895 := by
    have hnat : (1230390347 : ℕ)^4919*100000000000000^3895 ≤ 40846646321621^3895*2500000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1230390347 2500000000 40846646321621 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-373164093/2500000000 : ℝ), (1446324033/2500000000 : ℝ), (1230390347/2500000000 : ℝ)] ![(2263252117269/25000000000000 : ℝ), (50100345193731/100000000000000 : ℝ), (40846646321621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-373164093/2500000000 : ℝ)|^4919 ≤ (2263252117269/25000000000000 : ℝ)^3895
        have hw : |(-373164093/2500000000 : ℝ)|=(373164093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1446324033/2500000000 : ℝ)|^4919 ≤ (50100345193731/100000000000000 : ℝ)^3895
        have hw : |(1446324033/2500000000 : ℝ)|=(1446324033/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1230390347/2500000000 : ℝ)|^4919 ≤ (40846646321621/100000000000000 : ℝ)^3895
        have hw : |(1230390347/2500000000 : ℝ)|=(1230390347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1650_s0_1 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5437536667/10000000000 : ℝ)*x 0 + (-393357309/2000000000 : ℝ)*x 1 + (2460780879/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5437536667/10000000000 : ℝ)^4919 ≤ (11581882097197/25000000000000 : ℝ)^3895 := by
    have hnat : (5437536667 : ℕ)^4919*25000000000000^3895 ≤ 11581882097197^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437536667 10000000000 11581882097197 25000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (393357309/2000000000 : ℝ)^4919 ≤ (2565164279793/20000000000000 : ℝ)^3895 := by
    have hnat : (393357309 : ℕ)^4919*20000000000000^3895 ≤ 2565164279793^3895*2000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393357309 2000000000 2565164279793 20000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2460780879/5000000000 : ℝ)^4919 ≤ (40846650199771/100000000000000 : ℝ)^3895 := by
    have hnat : (2460780879 : ℕ)^4919*100000000000000^3895 ≤ 40846650199771^3895*5000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2460780879 5000000000 40846650199771 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5437536667/10000000000 : ℝ), (-393357309/2000000000 : ℝ), (2460780879/5000000000 : ℝ)] ![(11581882097197/25000000000000 : ℝ), (2565164279793/20000000000000 : ℝ), (40846650199771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5437536667/10000000000 : ℝ)|^4919 ≤ (11581882097197/25000000000000 : ℝ)^3895
        have hw : |(5437536667/10000000000 : ℝ)|=(5437536667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-393357309/2000000000 : ℝ)|^4919 ≤ (2565164279793/20000000000000 : ℝ)^3895
        have hw : |(-393357309/2000000000 : ℝ)|=(393357309/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2460780879/5000000000 : ℝ)|^4919 ≤ (40846650199771/100000000000000 : ℝ)^3895
        have hw : |(2460780879/5000000000 : ℝ)|=(2460780879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1650_s0_2 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (543753727/1000000000 : ℝ)*x 0 + (2460780621/5000000000 : ℝ)*x 1 + (-1966786413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543753727/1000000000 : ℝ)^4919 ≤ (23163767438489/50000000000000 : ℝ)^3895 := by
    have hnat : (543753727 : ℕ)^4919*50000000000000^3895 ≤ 23163767438489^3895*1000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543753727 1000000000 23163767438489 50000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2460780621/5000000000 : ℝ)^4919 ≤ (10211661197831/25000000000000 : ℝ)^3895 := by
    have hnat : (2460780621 : ℕ)^4919*25000000000000^3895 ≤ 10211661197831^3895*5000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2460780621 5000000000 10211661197831 25000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1966786413/10000000000 : ℝ)^4919 ≤ (12825820311861/100000000000000 : ℝ)^3895 := by
    have hnat : (1966786413 : ℕ)^4919*100000000000000^3895 ≤ 12825820311861^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1966786413 10000000000 12825820311861 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(543753727/1000000000 : ℝ), (2460780621/5000000000 : ℝ), (-1966786413/10000000000 : ℝ)] ![(23163767438489/50000000000000 : ℝ), (10211661197831/25000000000000 : ℝ), (12825820311861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(543753727/1000000000 : ℝ)|^4919 ≤ (23163767438489/50000000000000 : ℝ)^3895
        have hw : |(543753727/1000000000 : ℝ)|=(543753727/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2460780621/5000000000 : ℝ)|^4919 ≤ (10211661197831/25000000000000 : ℝ)^3895
        have hw : |(2460780621/5000000000 : ℝ)|=(2460780621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1966786413/10000000000 : ℝ)|^4919 ≤ (12825820311861/100000000000000 : ℝ)^3895
        have hw : |(-1966786413/10000000000 : ℝ)|=(1966786413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1650_s0_3 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4090615987/10000000000 : ℝ)*x 0 + (3082610601/10000000000 : ℝ)*x 1 + (531731033/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4090615987/10000000000 : ℝ)^4919 ≤ (32339069153457/100000000000000 : ℝ)^3895 := by
    have hnat : (4090615987 : ℕ)^4919*100000000000000^3895 ≤ 32339069153457^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4090615987 10000000000 32339069153457 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3082610601/10000000000 : ℝ)^4919 ≤ (2827904948401/12500000000000 : ℝ)^3895 := by
    have hnat : (3082610601 : ℕ)^4919*12500000000000^3895 ≤ 2827904948401^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3082610601 10000000000 2827904948401 12500000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (531731033/1000000000 : ℝ)^4919 ≤ (45037691243817/100000000000000 : ℝ)^3895 := by
    have hnat : (531731033 : ℕ)^4919*100000000000000^3895 ≤ 45037691243817^3895*1000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531731033 1000000000 45037691243817 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4090615987/10000000000 : ℝ), (3082610601/10000000000 : ℝ), (531731033/1000000000 : ℝ)] ![(32339069153457/100000000000000 : ℝ), (2827904948401/12500000000000 : ℝ), (45037691243817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4090615987/10000000000 : ℝ)|^4919 ≤ (32339069153457/100000000000000 : ℝ)^3895
        have hw : |(4090615987/10000000000 : ℝ)|=(4090615987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3082610601/10000000000 : ℝ)|^4919 ≤ (2827904948401/12500000000000 : ℝ)^3895
        have hw : |(3082610601/10000000000 : ℝ)|=(3082610601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(531731033/1000000000 : ℝ)|^4919 ≤ (45037691243817/100000000000000 : ℝ)^3895
        have hw : |(531731033/1000000000 : ℝ)|=(531731033/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1650_s0_4 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-747476403/5000000000 : ℝ)*x 0 + (3861709/7812500 : ℝ)*x 1 + (576313017/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (747476403/5000000000 : ℝ)^4919 ≤ (2267650410827/25000000000000 : ℝ)^3895 := by
    have hnat : (747476403 : ℕ)^4919*25000000000000^3895 ≤ 2267650410827^3895*5000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      747476403 5000000000 2267650410827 25000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3861709/7812500 : ℝ)^4919 ≤ (20535676203491/50000000000000 : ℝ)^3895 := by
    have hnat : (3861709 : ℕ)^4919*50000000000000^3895 ≤ 20535676203491^3895*7812500^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3861709 7812500 20535676203491 50000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (576313017/1000000000 : ℝ)^4919 ≤ (6232255742409/12500000000000 : ℝ)^3895 := by
    have hnat : (576313017 : ℕ)^4919*12500000000000^3895 ≤ 6232255742409^3895*1000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      576313017 1000000000 6232255742409 12500000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-747476403/5000000000 : ℝ), (3861709/7812500 : ℝ), (576313017/1000000000 : ℝ)] ![(2267650410827/25000000000000 : ℝ), (20535676203491/50000000000000 : ℝ), (6232255742409/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-747476403/5000000000 : ℝ)|^4919 ≤ (2267650410827/25000000000000 : ℝ)^3895
        have hw : |(-747476403/5000000000 : ℝ)|=(747476403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3861709/7812500 : ℝ)|^4919 ≤ (20535676203491/50000000000000 : ℝ)^3895
        have hw : |(3861709/7812500 : ℝ)|=(3861709/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(576313017/1000000000 : ℝ)|^4919 ≤ (6232255742409/12500000000000 : ℝ)^3895
        have hw : |(576313017/1000000000 : ℝ)|=(576313017/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1650_s0_5 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5201841769/10000000000 : ℝ)*x 0 + (-562608993/5000000000 : ℝ)*x 1 + (1440782527/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5201841769/10000000000 : ℝ)^4919 ≤ (43806093028683/100000000000000 : ℝ)^3895 := by
    have hnat : (5201841769 : ℕ)^4919*100000000000000^3895 ≤ 43806093028683^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5201841769 10000000000 43806093028683 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (562608993/5000000000 : ℝ)^4919 ≤ (6335861698423/100000000000000 : ℝ)^3895 := by
    have hnat : (562608993 : ℕ)^4919*100000000000000^3895 ≤ 6335861698423^3895*5000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562608993 5000000000 6335861698423 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1440782527/2500000000 : ℝ)^4919 ≤ (49858045261883/100000000000000 : ℝ)^3895 := by
    have hnat : (1440782527 : ℕ)^4919*100000000000000^3895 ≤ 49858045261883^3895*2500000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1440782527 2500000000 49858045261883 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5201841769/10000000000 : ℝ), (-562608993/5000000000 : ℝ), (1440782527/2500000000 : ℝ)] ![(43806093028683/100000000000000 : ℝ), (6335861698423/100000000000000 : ℝ), (49858045261883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5201841769/10000000000 : ℝ)|^4919 ≤ (43806093028683/100000000000000 : ℝ)^3895
        have hw : |(5201841769/10000000000 : ℝ)|=(5201841769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-562608993/5000000000 : ℝ)|^4919 ≤ (6335861698423/100000000000000 : ℝ)^3895
        have hw : |(-562608993/5000000000 : ℝ)|=(562608993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1440782527/2500000000 : ℝ)|^4919 ≤ (49858045261883/100000000000000 : ℝ)^3895
        have hw : |(1440782527/2500000000 : ℝ)|=(1440782527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1650_s0_6 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2600920461/5000000000 : ℝ)*x 0 + (5763131051/10000000000 : ℝ)*x 1 + (-281304451/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2600920461/5000000000 : ℝ)^4919 ≤ (21903042010323/50000000000000 : ℝ)^3895 := by
    have hnat : (2600920461 : ℕ)^4919*50000000000000^3895 ≤ 21903042010323^3895*5000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2600920461 5000000000 21903042010323 50000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5763131051/10000000000 : ℝ)^4919 ≤ (9971611112949/20000000000000 : ℝ)^3895 := by
    have hnat : (5763131051 : ℕ)^4919*20000000000000^3895 ≤ 9971611112949^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5763131051 10000000000 9971611112949 20000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (281304451/2500000000 : ℝ)^4919 ≤ (3167930202099/50000000000000 : ℝ)^3895 := by
    have hnat : (281304451 : ℕ)^4919*50000000000000^3895 ≤ 3167930202099^3895*2500000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281304451 2500000000 3167930202099 50000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2600920461/5000000000 : ℝ), (5763131051/10000000000 : ℝ), (-281304451/2500000000 : ℝ)] ![(21903042010323/50000000000000 : ℝ), (9971611112949/20000000000000 : ℝ), (3167930202099/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2600920461/5000000000 : ℝ)|^4919 ≤ (21903042010323/50000000000000 : ℝ)^3895
        have hw : |(2600920461/5000000000 : ℝ)|=(2600920461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5763131051/10000000000 : ℝ)|^4919 ≤ (9971611112949/20000000000000 : ℝ)^3895
        have hw : |(5763131051/10000000000 : ℝ)|=(5763131051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-281304451/2500000000 : ℝ)|^4919 ≤ (3167930202099/50000000000000 : ℝ)^3895
        have hw : |(-281304451/2500000000 : ℝ)|=(281304451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1650_s0_7 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4096556947/10000000000 : ℝ)*x 0 + (2630937599/5000000000 : ℝ)*x 1 + (3139960521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4096556947/10000000000 : ℝ)^4919 ≤ (1012449859641/3125000000000 : ℝ)^3895 := by
    have hnat : (4096556947 : ℕ)^4919*3125000000000^3895 ≤ 1012449859641^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4096556947 10000000000 1012449859641 3125000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2630937599/5000000000 : ℝ)^4919 ≤ (44445527998099/100000000000000 : ℝ)^3895 := by
    have hnat : (2630937599 : ℕ)^4919*100000000000000^3895 ≤ 44445527998099^3895*5000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630937599 5000000000 44445527998099 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3139960521/10000000000 : ℝ)^4919 ≤ (23156076486551/100000000000000 : ℝ)^3895 := by
    have hnat : (3139960521 : ℕ)^4919*100000000000000^3895 ≤ 23156076486551^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3139960521 10000000000 23156076486551 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4096556947/10000000000 : ℝ), (2630937599/5000000000 : ℝ), (3139960521/10000000000 : ℝ)] ![(1012449859641/3125000000000 : ℝ), (44445527998099/100000000000000 : ℝ), (23156076486551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4096556947/10000000000 : ℝ)|^4919 ≤ (1012449859641/3125000000000 : ℝ)^3895
        have hw : |(4096556947/10000000000 : ℝ)|=(4096556947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2630937599/5000000000 : ℝ)|^4919 ≤ (44445527998099/100000000000000 : ℝ)^3895
        have hw : |(2630937599/5000000000 : ℝ)|=(2630937599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3139960521/10000000000 : ℝ)|^4919 ≤ (23156076486551/100000000000000 : ℝ)^3895
        have hw : |(3139960521/10000000000 : ℝ)|=(3139960521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1650_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35872509/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1211/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (23357/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4915/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4915 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4915*1^1024 ≤ 0^1024*1^4915 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4915 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4915 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4915/1024 : ℝ) ≤ (615085777965898277/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4915 ≤ (615085777965898277/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4915*50000000000000000000^1024 ≤ 615085777965898277^1024*5^4915 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 615085777965898277 50000000000000000000 4915 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (615085777965898277/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4915 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4915/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4915 := by
      have hnat : (1 : ℕ)^1024*1^4915 ≤ 1^4915*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4915 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4915 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50615085777965898277/50000000000000000000 : ℝ) ≤ (2005101145154873/2000000000000000 : ℝ) ^ (4915/1024 : ℝ) := by
    have hpowers : (50615085777965898277/50000000000000000000 : ℝ)^1024 ≤ (2005101145154873/2000000000000000 : ℝ)^4915 := by
      have hnat : (50615085777965898277 : ℕ)^1024*2000000000000000^4915 ≤ 2005101145154873^4915*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50615085777965898277 50000000000000000000 2005101145154873 2000000000000000 1024 4915 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2005101145154873/2000000000000000 : ℝ)) (X := (50615085777965898277/50000000000000000000 : ℝ)) (by norm_num) 4915 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25615085777965898277/25000000000000000000 : ℝ) ≤ (1005101145154873/1000000000000000 : ℝ) ^ (4915/1024 : ℝ) := by
    have hpowers : (25615085777965898277/25000000000000000000 : ℝ)^1024 ≤ (1005101145154873/1000000000000000 : ℝ)^4915 := by
      have hnat : (25615085777965898277 : ℕ)^1024*1000000000000000^4915 ≤ 1005101145154873^4915*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25615085777965898277 25000000000000000000 1005101145154873 1000000000000000 1024 4915 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1005101145154873/1000000000000000 : ℝ)) (X := (25615085777965898277/25000000000000000000 : ℝ)) (by norm_num) 4915 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(5101145154873/800000000000000 : ℝ)*(0 : ℝ))^(4915/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(5101145154873/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(615085777965898277/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(5101145154873/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4915/1024 : ℝ) := by
    rw [show (1 : ℝ)+(5101145154873/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2005101145154873/2000000000000000 : ℝ) by norm_num, show 1+(615085777965898277/50000000000000000000 : ℝ)+(0 : ℝ)=(50615085777965898277/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(615085777965898277/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(5101145154873/800000000000000 : ℝ)*(2/5 : ℝ))^(4915/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(5101145154873/800000000000000 : ℝ)*(2/5 : ℝ)=(1005101145154873/1000000000000000 : ℝ) by norm_num, show 1+2*(615085777965898277/50000000000000000000 : ℝ)=(25615085777965898277/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(5101145154873/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4915/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5101145154873/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(5101145154873/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4915/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5101145154873/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(5101145154873/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4915/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5101145154873/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-373164093/2500000000 : ℝ)*X 0 0+(1446324033/2500000000 : ℝ)*X 0 1+(1230390347/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5437536667/10000000000 : ℝ)*X 1 0+(-393357309/2000000000 : ℝ)*X 1 1+(2460780879/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((543753727/1000000000 : ℝ)*X 2 0+(2460780621/5000000000 : ℝ)*X 2 1+(-1966786413/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4090615987/10000000000 : ℝ)*X 0 0+(3082610601/10000000000 : ℝ)*X 0 1+(531731033/1000000000 : ℝ)*X 0 2+(4090615987/10000000000 : ℝ)*X 1 0+(3082610601/10000000000 : ℝ)*X 1 1+(531731033/1000000000 : ℝ)*X 1 2+(4090615987/10000000000 : ℝ)*X 2 0+(3082610601/10000000000 : ℝ)*X 2 1+(531731033/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-747476403/5000000000 : ℝ)*X 0 0+(3861709/7812500 : ℝ)*X 0 1+(576313017/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5201841769/10000000000 : ℝ)*X 1 0+(-562608993/5000000000 : ℝ)*X 1 1+(1440782527/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2600920461/5000000000 : ℝ)*X 2 0+(5763131051/10000000000 : ℝ)*X 2 1+(-281304451/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4096556947/10000000000 : ℝ)*X 0 0+(2630937599/5000000000 : ℝ)*X 0 1+(3139960521/10000000000 : ℝ)*X 0 2+(4096556947/10000000000 : ℝ)*X 1 0+(2630937599/5000000000 : ℝ)*X 1 1+(3139960521/10000000000 : ℝ)*X 1 2+(4096556947/10000000000 : ℝ)*X 2 0+(2630937599/5000000000 : ℝ)*X 2 1+(3139960521/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (53957187295077250640247/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7256083/6250000000000 : ℝ)*(base1) + (520114667/50000000000000 : ℝ)*(base19) + (233724243/20000000000000 : ℝ)*(base23) + (96442377/100000000000000 : ℝ)*(upper3) + (173103347/100000000000000 : ℝ)*(upper5) + (200657858454729/25000000000000 : ℝ)*(major0) + (200657858454729/25000000000000 : ℝ)*(major1) + (200657858454729/25000000000000 : ℝ)*(major2) + (578883368978277/50000000000000 : ℝ)*(sp0) + (72360658935853/6250000000000 : ℝ)*(sp1) + (144721301822721/12500000000000 : ℝ)*(sp2) + (447489237252919/100000000000000 : ℝ)*(sp3) + (1240335939/25000000000000 : ℝ)*(sp4) + (1751227309/100000000000000 : ℝ)*(sp7) + (111872776144389/25000000000000 : ℝ)*(f.failure) + (578885791601491/50000000000000 : ℝ)*(f.sum) + (25738761724417/10000000000000000000000000000 : ℝ)*base65 + (27214149264417/20000000000000000000000000000 : ℝ)*base67 + (1144370375583/20000000000000000000000000000 : ℝ)*base70 + (31104506404417/20000000000000000000000000000 : ℝ)*base71 + (29687060834417/10000000000000000000000000000 : ℝ)*base73 + (49537675384417/20000000000000000000000000000 : ℝ)*base75 + (63850336475583/20000000000000000000000000000 : ℝ)*base78 + (37795082895583/20000000000000000000000000000 : ℝ)*base80 + (11092133494417/10000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (297999/500000000000000000000 : ℝ)*base90 + (297999/500000000000000000000 : ℝ)*base92 + (297999/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (168683009222865616183797/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (382034023/25000000000000 : ℝ)*(base19) + (1356830017/100000000000000 : ℝ)*(base23) + (143995481/100000000000000 : ℝ)*(base32) + (248573273/100000000000000 : ℝ)*(upper3) + (972059/625000000000 : ℝ)*(upper5) + (845285745391263/100000000000000 : ℝ)*(major0) + (845285745391263/100000000000000 : ℝ)*(major1) + (845285745391263/100000000000000 : ℝ)*(major2) + (4649871309/100000000000000 : ℝ)*(sp1) + (5250777121/100000000000000 : ℝ)*(sp2) + (1219299046667639/100000000000000 : ℝ)*(sp4) + (609646434330119/50000000000000 : ℝ)*(sp5) + (1219292439060501/100000000000000 : ℝ)*(sp6) + (94254403796211/20000000000000 : ℝ)*(sp7) + (58909020372067/12500000000000 : ℝ)*(f.failure) + (1219299046667639/100000000000000 : ℝ)*(f.sum) + (59574354034599/40000000000000000000000000000 : ℝ)*base65 + (42557017525401/80000000000000000000000000000 : ℝ)*base68 + (36897746725401/80000000000000000000000000000 : ℝ)*base70 + (13522460725401/80000000000000000000000000000 : ℝ)*base72 + (6177716605401/40000000000000000000000000000 : ℝ)*base74 + (273096010405401/80000000000000000000000000000 : ℝ)*base76 + (63102738085401/80000000000000000000000000000 : ℝ)*base78 + (83340661765401/80000000000000000000000000000 : ℝ)*base80 + (40961600954599/40000000000000000000000000000 : ℝ)*base81 + (693897/250000000000000000000 : ℝ)*base90 + (693897/250000000000000000000 : ℝ)*base92 + (693897/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1650_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35872509/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1211/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (23357/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1650_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1650_s1_0 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-159853469/1000000000 : ℝ)*x 0 + (343517121/625000000 : ℝ)*x 1 + (2570883229/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (159853469/1000000000 : ℝ)^4919 ≤ (4935710524587/50000000000000 : ℝ)^3895 := by
    have hnat : (159853469 : ℕ)^4919*50000000000000^3895 ≤ 4935710524587^3895*1000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      159853469 1000000000 4935710524587 50000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (343517121/625000000 : ℝ)^4919 ≤ (23480213874449/50000000000000 : ℝ)^3895 := by
    have hnat : (343517121 : ℕ)^4919*50000000000000^3895 ≤ 23480213874449^3895*625000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343517121 625000000 23480213874449 50000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2570883229/5000000000 : ℝ)^4919 ≤ (5396018899117/12500000000000 : ℝ)^3895 := by
    have hnat : (2570883229 : ℕ)^4919*12500000000000^3895 ≤ 5396018899117^3895*5000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2570883229 5000000000 5396018899117 12500000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-159853469/1000000000 : ℝ), (343517121/625000000 : ℝ), (2570883229/5000000000 : ℝ)] ![(4935710524587/50000000000000 : ℝ), (23480213874449/50000000000000 : ℝ), (5396018899117/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-159853469/1000000000 : ℝ)|^4919 ≤ (4935710524587/50000000000000 : ℝ)^3895
        have hw : |(-159853469/1000000000 : ℝ)|=(159853469/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(343517121/625000000 : ℝ)|^4919 ≤ (23480213874449/50000000000000 : ℝ)^3895
        have hw : |(343517121/625000000 : ℝ)|=(343517121/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2570883229/5000000000 : ℝ)|^4919 ≤ (5396018899117/12500000000000 : ℝ)^3895
        have hw : |(2570883229/5000000000 : ℝ)|=(2570883229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1650_s1_1 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1340165479/2500000000 : ℝ)*x 0 + (-1782835667/10000000000 : ℝ)*x 1 + (1285441583/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1340165479/2500000000 : ℝ)^4919 ≤ (45501910040503/100000000000000 : ℝ)^3895 := by
    have hnat : (1340165479 : ℕ)^4919*100000000000000^3895 ≤ 45501910040503^3895*2500000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340165479 2500000000 45501910040503 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1782835667/10000000000 : ℝ)^4919 ≤ (2832485020437/25000000000000 : ℝ)^3895 := by
    have hnat : (1782835667 : ℕ)^4919*25000000000000^3895 ≤ 2832485020437^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1782835667 10000000000 2832485020437 25000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1285441583/2500000000 : ℝ)^4919 ≤ (43168149856983/100000000000000 : ℝ)^3895 := by
    have hnat : (1285441583 : ℕ)^4919*100000000000000^3895 ≤ 43168149856983^3895*2500000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1285441583 2500000000 43168149856983 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1340165479/2500000000 : ℝ), (-1782835667/10000000000 : ℝ), (1285441583/2500000000 : ℝ)] ![(45501910040503/100000000000000 : ℝ), (2832485020437/25000000000000 : ℝ), (43168149856983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1340165479/2500000000 : ℝ)|^4919 ≤ (45501910040503/100000000000000 : ℝ)^3895
        have hw : |(1340165479/2500000000 : ℝ)|=(1340165479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1782835667/10000000000 : ℝ)|^4919 ≤ (2832485020437/25000000000000 : ℝ)^3895
        have hw : |(-1782835667/10000000000 : ℝ)|=(1782835667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1285441583/2500000000 : ℝ)|^4919 ≤ (43168149856983/100000000000000 : ℝ)^3895
        have hw : |(1285441583/2500000000 : ℝ)|=(1285441583/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1650_s1_2 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5360661377/10000000000 : ℝ)*x 0 + (205670677/400000000 : ℝ)*x 1 + (-445708901/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5360661377/10000000000 : ℝ)^4919 ≤ (11375476065653/25000000000000 : ℝ)^3895 := by
    have hnat : (5360661377 : ℕ)^4919*25000000000000^3895 ≤ 11375476065653^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5360661377 10000000000 11375476065653 25000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (205670677/400000000 : ℝ)^4919 ≤ (21584078072221/50000000000000 : ℝ)^3895 := by
    have hnat : (205670677 : ℕ)^4919*50000000000000^3895 ≤ 21584078072221^3895*400000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205670677 400000000 21584078072221 50000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (445708901/2500000000 : ℝ)^4919 ≤ (5664969788063/50000000000000 : ℝ)^3895 := by
    have hnat : (445708901 : ℕ)^4919*50000000000000^3895 ≤ 5664969788063^3895*2500000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      445708901 2500000000 5664969788063 50000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5360661377/10000000000 : ℝ), (205670677/400000000 : ℝ), (-445708901/2500000000 : ℝ)] ![(11375476065653/25000000000000 : ℝ), (21584078072221/50000000000000 : ℝ), (5664969788063/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5360661377/10000000000 : ℝ)|^4919 ≤ (11375476065653/25000000000000 : ℝ)^3895
        have hw : |(5360661377/10000000000 : ℝ)|=(5360661377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(205670677/400000000 : ℝ)|^4919 ≤ (21584078072221/50000000000000 : ℝ)^3895
        have hw : |(205670677/400000000 : ℝ)|=(205670677/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-445708901/2500000000 : ℝ)|^4919 ≤ (5664969788063/50000000000000 : ℝ)^3895
        have hw : |(-445708901/2500000000 : ℝ)|=(445708901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1650_s1_3 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4173323937/10000000000 : ℝ)*x 0 + (3732958157/10000000000 : ℝ)*x 1 + (290634871/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4173323937/10000000000 : ℝ)^4919 ≤ (33167016054279/100000000000000 : ℝ)^3895 := by
    have hnat : (4173323937 : ℕ)^4919*100000000000000^3895 ≤ 33167016054279^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4173323937 10000000000 33167016054279 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3732958157/10000000000 : ℝ)^4919 ≤ (288101416287/1000000000000 : ℝ)^3895 := by
    have hnat : (3732958157 : ℕ)^4919*1000000000000^3895 ≤ 288101416287^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3732958157 10000000000 288101416287 1000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (290634871/625000000 : ℝ)^4919 ≤ (19011421151991/50000000000000 : ℝ)^3895 := by
    have hnat : (290634871 : ℕ)^4919*50000000000000^3895 ≤ 19011421151991^3895*625000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      290634871 625000000 19011421151991 50000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4173323937/10000000000 : ℝ), (3732958157/10000000000 : ℝ), (290634871/625000000 : ℝ)] ![(33167016054279/100000000000000 : ℝ), (288101416287/1000000000000 : ℝ), (19011421151991/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4173323937/10000000000 : ℝ)|^4919 ≤ (33167016054279/100000000000000 : ℝ)^3895
        have hw : |(4173323937/10000000000 : ℝ)|=(4173323937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3732958157/10000000000 : ℝ)|^4919 ≤ (288101416287/1000000000000 : ℝ)^3895
        have hw : |(3732958157/10000000000 : ℝ)|=(3732958157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(290634871/625000000 : ℝ)|^4919 ≤ (19011421151991/50000000000000 : ℝ)^3895
        have hw : |(290634871/625000000 : ℝ)|=(290634871/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1650_s1_4 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1598690601/10000000000 : ℝ)*x 0 + (2572681923/5000000000 : ℝ)*x 1 + (219705029/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1598690601/10000000000 : ℝ)^4919 ≤ (4936318490599/50000000000000 : ℝ)^3895 := by
    have hnat : (1598690601 : ℕ)^4919*50000000000000^3895 ≤ 4936318490599^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1598690601 10000000000 4936318490599 50000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2572681923/5000000000 : ℝ)^4919 ≤ (43206297076337/100000000000000 : ℝ)^3895 := by
    have hnat : (2572681923 : ℕ)^4919*100000000000000^3895 ≤ 43206297076337^3895*5000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2572681923 5000000000 43206297076337 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219705029/400000000 : ℝ)^4919 ≤ (46921065936927/100000000000000 : ℝ)^3895 := by
    have hnat : (219705029 : ℕ)^4919*100000000000000^3895 ≤ 46921065936927^3895*400000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219705029 400000000 46921065936927 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1598690601/10000000000 : ℝ), (2572681923/5000000000 : ℝ), (219705029/400000000 : ℝ)] ![(4936318490599/50000000000000 : ℝ), (43206297076337/100000000000000 : ℝ), (46921065936927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1598690601/10000000000 : ℝ)|^4919 ≤ (4936318490599/50000000000000 : ℝ)^3895
        have hw : |(-1598690601/10000000000 : ℝ)|=(1598690601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2572681923/5000000000 : ℝ)|^4919 ≤ (43206297076337/100000000000000 : ℝ)^3895
        have hw : |(2572681923/5000000000 : ℝ)|=(2572681923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(219705029/400000000 : ℝ)|^4919 ≤ (46921065936927/100000000000000 : ℝ)^3895
        have hw : |(219705029/400000000 : ℝ)|=(219705029/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1650_s1_5 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2632937361/5000000000 : ℝ)*x 0 + (-1431976427/10000000000 : ℝ)*x 1 + (5492625747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2632937361/5000000000 : ℝ)^4919 ≤ (8897639323219/20000000000000 : ℝ)^3895 := by
    have hnat : (2632937361 : ℕ)^4919*20000000000000^3895 ≤ 8897639323219^3895*5000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632937361 5000000000 8897639323219 20000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1431976427/10000000000 : ℝ)^4919 ≤ (8590737195181/100000000000000 : ℝ)^3895 := by
    have hnat : (1431976427 : ℕ)^4919*100000000000000^3895 ≤ 8590737195181^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1431976427 10000000000 8590737195181 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5492625747/10000000000 : ℝ)^4919 ≤ (733141658973/1562500000000 : ℝ)^3895 := by
    have hnat : (5492625747 : ℕ)^4919*1562500000000^3895 ≤ 733141658973^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5492625747 10000000000 733141658973 1562500000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2632937361/5000000000 : ℝ), (-1431976427/10000000000 : ℝ), (5492625747/10000000000 : ℝ)] ![(8897639323219/20000000000000 : ℝ), (8590737195181/100000000000000 : ℝ), (733141658973/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2632937361/5000000000 : ℝ)|^4919 ≤ (8897639323219/20000000000000 : ℝ)^3895
        have hw : |(2632937361/5000000000 : ℝ)|=(2632937361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1431976427/10000000000 : ℝ)|^4919 ≤ (8590737195181/100000000000000 : ℝ)^3895
        have hw : |(-1431976427/10000000000 : ℝ)|=(1431976427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5492625747/10000000000 : ℝ)|^4919 ≤ (733141658973/1562500000000 : ℝ)^3895
        have hw : |(5492625747/10000000000 : ℝ)|=(5492625747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1650_s1_6 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2632937261/5000000000 : ℝ)*x 0 + (5492626029/10000000000 : ℝ)*x 1 + (-1431976307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2632937261/5000000000 : ℝ)^4919 ≤ (44488194482197/100000000000000 : ℝ)^3895 := by
    have hnat : (2632937261 : ℕ)^4919*100000000000000^3895 ≤ 44488194482197^3895*5000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632937261 5000000000 44488194482197 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5492626029/10000000000 : ℝ)^4919 ≤ (23460534608301/50000000000000 : ℝ)^3895 := by
    have hnat : (5492626029 : ℕ)^4919*50000000000000^3895 ≤ 23460534608301^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5492626029 10000000000 23460534608301 50000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1431976307/10000000000 : ℝ)^4919 ≤ (859073628601/10000000000000 : ℝ)^3895 := by
    have hnat : (1431976307 : ℕ)^4919*10000000000000^3895 ≤ 859073628601^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1431976307 10000000000 859073628601 10000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2632937261/5000000000 : ℝ), (5492626029/10000000000 : ℝ), (-1431976307/10000000000 : ℝ)] ![(44488194482197/100000000000000 : ℝ), (23460534608301/50000000000000 : ℝ), (859073628601/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2632937261/5000000000 : ℝ)|^4919 ≤ (44488194482197/100000000000000 : ℝ)^3895
        have hw : |(2632937261/5000000000 : ℝ)|=(2632937261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5492626029/10000000000 : ℝ)|^4919 ≤ (23460534608301/50000000000000 : ℝ)^3895
        have hw : |(5492626029/10000000000 : ℝ)|=(5492626029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1431976307/10000000000 : ℝ)|^4919 ≤ (859073628601/10000000000000 : ℝ)^3895
        have hw : |(-1431976307/10000000000 : ℝ)|=(1431976307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1650_s1_7 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2086863771/5000000000 : ℝ)*x 0 + (2320425461/5000000000 : ℝ)*x 1 + (3742397219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2086863771/5000000000 : ℝ)^4919 ≤ (33171066993469/100000000000000 : ℝ)^3895 := by
    have hnat : (2086863771 : ℕ)^4919*100000000000000^3895 ≤ 33171066993469^3895*5000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086863771 5000000000 33171066993469 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2320425461/5000000000 : ℝ)^4919 ≤ (37926760251291/100000000000000 : ℝ)^3895 := by
    have hnat : (2320425461 : ℕ)^4919*100000000000000^3895 ≤ 37926760251291^3895*5000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2320425461 5000000000 37926760251291 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3742397219/10000000000 : ℝ)^4919 ≤ (7225543187263/25000000000000 : ℝ)^3895 := by
    have hnat : (3742397219 : ℕ)^4919*25000000000000^3895 ≤ 7225543187263^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3742397219 10000000000 7225543187263 25000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2086863771/5000000000 : ℝ), (2320425461/5000000000 : ℝ), (3742397219/10000000000 : ℝ)] ![(33171066993469/100000000000000 : ℝ), (37926760251291/100000000000000 : ℝ), (7225543187263/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2086863771/5000000000 : ℝ)|^4919 ≤ (33171066993469/100000000000000 : ℝ)^3895
        have hw : |(2086863771/5000000000 : ℝ)|=(2086863771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2320425461/5000000000 : ℝ)|^4919 ≤ (37926760251291/100000000000000 : ℝ)^3895
        have hw : |(2320425461/5000000000 : ℝ)|=(2320425461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3742397219/10000000000 : ℝ)|^4919 ≤ (7225543187263/25000000000000 : ℝ)^3895
        have hw : |(3742397219/10000000000 : ℝ)|=(3742397219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1650_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35872509/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (23357/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1211/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (4879/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17289/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (23357/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1211/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (23357/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1211/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (23357/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1211/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (23357/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1211/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (23357/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1211/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (23357/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1211/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1211/25000 : ℝ) ^ (4915/1024 : ℝ) ≤ (48891869233999/100000000000000000000 : ℝ) := by
    have hpowers : (1211/25000 : ℝ)^4915 ≤ (48891869233999/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1211 : ℕ)^4915*100000000000000000000^1024 ≤ 48891869233999^1024*25000^4915 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1211 25000 48891869233999 100000000000000000000 4915 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1211/25000 : ℝ)) (X := (48891869233999/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4915 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (23357/100000 : ℝ) ^ (4915/1024 : ℝ) ≤ (2325226459343929/2500000000000000000 : ℝ) := by
    have hpowers : (23357/100000 : ℝ)^4915 ≤ (2325226459343929/2500000000000000000 : ℝ)^1024 := by
      have hnat : (23357 : ℕ)^4915*2500000000000000000^1024 ≤ 2325226459343929^1024*100000^4915 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23357 100000 2325226459343929 2500000000000000000 4915 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (23357/100000 : ℝ)) (X := (2325226459343929/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4915 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000048891869233999/50000000000000000000 : ℝ) ≤ (5000001018621663/5000000000000000 : ℝ) ^ (4915/1024 : ℝ) := by
    have hpowers : (50000048891869233999/50000000000000000000 : ℝ)^1024 ≤ (5000001018621663/5000000000000000 : ℝ)^4915 := by
      have hnat : (50000048891869233999 : ℕ)^1024*5000000000000000^4915 ≤ 5000001018621663^4915*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000048891869233999 50000000000000000000 5000001018621663 5000000000000000 1024 4915 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000001018621663/5000000000000000 : ℝ)) (X := (50000048891869233999/50000000000000000000 : ℝ)) (by norm_num) 4915 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100093057950242991159/100000000000000000000 : ℝ) ≤ (10001938072430033/10000000000000000 : ℝ) ^ (4915/1024 : ℝ) := by
    have hpowers : (100093057950242991159/100000000000000000000 : ℝ)^1024 ≤ (10001938072430033/10000000000000000 : ℝ)^4915 := by
      have hnat : (100093057950242991159 : ℕ)^1024*10000000000000000^4915 ≤ 10001938072430033^4915*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100093057950242991159 100000000000000000000 10001938072430033 10000000000000000 1024 4915 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001938072430033/10000000000000000 : ℝ)) (X := (100093057950242991159/100000000000000000000 : ℝ)) (by norm_num) 4915 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1252325226459343929/1250000000000000000 : ℝ) ≤ (500193705380837/500000000000000 : ℝ) ^ (4915/1024 : ℝ) := by
    have hpowers : (1252325226459343929/1250000000000000000 : ℝ)^1024 ≤ (500193705380837/500000000000000 : ℝ)^4915 := by
      have hnat : (1252325226459343929 : ℕ)^1024*500000000000000^4915 ≤ 500193705380837^4915*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1252325226459343929 1250000000000000000 500193705380837 500000000000000 1024 4915 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500193705380837/500000000000000 : ℝ)) (X := (1252325226459343929/1250000000000000000 : ℝ)) (by norm_num) 4915 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(48891869233999/100000000000000000000 : ℝ) ≤ ((92555640703298438411/92565000000000000000 : ℝ)+2*(1936035186707/1851300000000000 : ℝ)*(1211/25000 : ℝ))^(4915/1024 : ℝ) := by
    rw [show (92555640703298438411/92565000000000000000 : ℝ)+2*(1936035186707/1851300000000000 : ℝ)*(1211/25000 : ℝ)=(5000001018621663/5000000000000000 : ℝ) by norm_num, show 1+2*(48891869233999/100000000000000000000 : ℝ)=(50000048891869233999/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2325226459343929/2500000000000000000 : ℝ)+(48891869233999/100000000000000000000 : ℝ) ≤ ((92555640703298438411/92565000000000000000 : ℝ)+(1936035186707/1851300000000000 : ℝ)*((23357/100000 : ℝ)+(1211/25000 : ℝ)))^(4915/1024 : ℝ) := by
    rw [show (92555640703298438411/92565000000000000000 : ℝ)+(1936035186707/1851300000000000 : ℝ)*((23357/100000 : ℝ)+(1211/25000 : ℝ))=(10001938072430033/10000000000000000 : ℝ) by norm_num, show 1+(2325226459343929/2500000000000000000 : ℝ)+(48891869233999/100000000000000000000 : ℝ)=(100093057950242991159/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2325226459343929/2500000000000000000 : ℝ) ≤ ((92555640703298438411/92565000000000000000 : ℝ)+2*(1936035186707/1851300000000000 : ℝ)*(23357/100000 : ℝ))^(4915/1024 : ℝ) := by
    rw [show (92555640703298438411/92565000000000000000 : ℝ)+2*(1936035186707/1851300000000000 : ℝ)*(23357/100000 : ℝ)=(500193705380837/500000000000000 : ℝ) by norm_num, show 1+2*(2325226459343929/2500000000000000000 : ℝ)=(1252325226459343929/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (92555640703298438411/92565000000000000000 : ℝ)*(X 1 0+X 2 0)+(1936035186707/1851300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4915/1024 : ℝ)) (lo := (1211/25000 : ℝ)) (hi := (23357/100000 : ℝ)) (c := (92555640703298438411/92565000000000000000 : ℝ)) (alpha := (1936035186707/1851300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (92555640703298438411/92565000000000000000 : ℝ)*(X 0 1+X 2 1)+(1936035186707/1851300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4915/1024 : ℝ)) (lo := (1211/25000 : ℝ)) (hi := (23357/100000 : ℝ)) (c := (92555640703298438411/92565000000000000000 : ℝ)) (alpha := (1936035186707/1851300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (92555640703298438411/92565000000000000000 : ℝ)*(X 0 2+X 1 2)+(1936035186707/1851300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4915/1024 : ℝ)) (lo := (1211/25000 : ℝ)) (hi := (23357/100000 : ℝ)) (c := (92555640703298438411/92565000000000000000 : ℝ)) (alpha := (1936035186707/1851300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-159853469/1000000000 : ℝ)*X 0 0+(343517121/625000000 : ℝ)*X 0 1+(2570883229/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1340165479/2500000000 : ℝ)*X 1 0+(-1782835667/10000000000 : ℝ)*X 1 1+(1285441583/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5360661377/10000000000 : ℝ)*X 2 0+(205670677/400000000 : ℝ)*X 2 1+(-445708901/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4173323937/10000000000 : ℝ)*X 0 0+(3732958157/10000000000 : ℝ)*X 0 1+(290634871/625000000 : ℝ)*X 0 2+(4173323937/10000000000 : ℝ)*X 1 0+(3732958157/10000000000 : ℝ)*X 1 1+(290634871/625000000 : ℝ)*X 1 2+(4173323937/10000000000 : ℝ)*X 2 0+(3732958157/10000000000 : ℝ)*X 2 1+(290634871/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1598690601/10000000000 : ℝ)*X 0 0+(2572681923/5000000000 : ℝ)*X 0 1+(219705029/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2632937361/5000000000 : ℝ)*X 1 0+(-1431976427/10000000000 : ℝ)*X 1 1+(5492625747/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2632937261/5000000000 : ℝ)*X 2 0+(5492626029/10000000000 : ℝ)*X 2 1+(-1431976307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2086863771/5000000000 : ℝ)*X 0 0+(2320425461/5000000000 : ℝ)*X 0 1+(3742397219/10000000000 : ℝ)*X 0 2+(2086863771/5000000000 : ℝ)*X 1 0+(2320425461/5000000000 : ℝ)*X 1 1+(3742397219/10000000000 : ℝ)*X 1 2+(2086863771/5000000000 : ℝ)*X 2 0+(2320425461/5000000000 : ℝ)*X 2 1+(3742397219/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (268306623659383943314403841/257125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (767894161/100000000000000 : ℝ)*(base19) + (166488843/50000000000000 : ℝ)*(base23) + (27636087/20000000000000 : ℝ)*(upper3) + (40550701/50000000000000 : ℝ)*(upper4) + (27482929/100000000000000 : ℝ)*(upper5) + (977777053581393/50000000000000 : ℝ)*(major0) + (977777053581393/50000000000000 : ℝ)*(major1) + (977777053581393/50000000000000 : ℝ)*(major2) + (56416448272629/2000000000000 : ℝ)*(sp0) + (1410413663581097/50000000000000 : ℝ)*(sp1) + (705206940519667/25000000000000 : ℝ)*(sp2) + (1090277241520067/100000000000000 : ℝ)*(sp3) + (1136284981/20000000000000 : ℝ)*(sp4) + (2842966237/100000000000000 : ℝ)*(sp7) + (34071252640197/3125000000000 : ℝ)*(f.failure) + (1410414047528177/50000000000000 : ℝ)*(f.sum) + (10326893745451/5142500000000000000000000000 : ℝ)*base66 + (865007864583457053/514250000000000000000000000000000 : ℝ)*base68 + (1790325133005707053/514250000000000000000000000000000 : ℝ)*base70 + (2356959259137957053/514250000000000000000000000000000 : ℝ)*base72 + (26483819679103/10285000000000000000000000000 : ℝ)*base73 + (1157729331863457053/514250000000000000000000000000000 : ℝ)*base76 + (187342944481042947/514250000000000000000000000000000 : ℝ)*base77 + (7016087277419042947/514250000000000000000000000000000 : ℝ)*base79 + (37409395109323/10285000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (605727/62500000000000000000 : ℝ)*base90 + (605727/62500000000000000000 : ℝ)*base92 + (605727/62500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2758590707662043727732680021/1542750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (244803263/50000000000000 : ℝ)*(base19) + (102560511/20000000000000 : ℝ)*(base23) + (54021677/100000000000000 : ℝ)*(upper2) + (14121691/25000000000000 : ℝ)*(upper3) + (28277117/50000000000000 : ℝ)*(upper5) + (1996346694410837/100000000000000 : ℝ)*(major0) + (1996346694410837/100000000000000 : ℝ)*(major1) + (1996346694410837/100000000000000 : ℝ)*(major2) + (2430211193/50000000000000 : ℝ)*(sp1) + (6525908479/100000000000000 : ℝ)*(sp2) + (1439835076749279/50000000000000 : ℝ)*(sp4) + (1439832401734823/50000000000000 : ℝ)*(sp5) + (719915778696881/25000000000000 : ℝ)*(sp6) + (111302317571979/10000000000000 : ℝ)*(sp7) + (111302317571979/10000000000000 : ℝ)*(f.failure) + (1439835076749279/50000000000000 : ℝ)*(f.sum) + (189508729074671/92565000000000000000000000000 : ℝ)*base66 + (17822316091982863331/3085500000000000000000000000000000 : ℝ)*base68 + (30006610361558863331/3085500000000000000000000000000000 : ℝ)*base70 + (16987428296042863331/3085500000000000000000000000000000 : ℝ)*base72 + (101953717558819/92565000000000000000000000000 : ℝ)*base73 + (23111379222080863331/3085500000000000000000000000000000 : ℝ)*base76 + (17658336710059363331/3085500000000000000000000000000000 : ℝ)*base78 + (21771093335839363331/3085500000000000000000000000000000 : ℝ)*base80 + (64507194709931/92565000000000000000000000000 : ℝ)*base82 + (825311/200000000000000000000 : ℝ)*base89 + (825311/200000000000000000000 : ℝ)*base91 + (825311/200000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1650_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35872509/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (23357/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1211/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4879/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17289/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1650_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1650_s2_0 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-803918441/5000000000 : ℝ)*x 0 + (5451086911/10000000000 : ℝ)*x 1 + (1036163291/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (803918441/5000000000 : ℝ)^4919 ≤ (9944022262431/100000000000000 : ℝ)^3895 := by
    have hnat : (803918441 : ℕ)^4919*100000000000000^3895 ≤ 9944022262431^3895*5000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      803918441 5000000000 9944022262431 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5451086911/10000000000 : ℝ)^4919 ≤ (23236687368781/50000000000000 : ℝ)^3895 := by
    have hnat : (5451086911 : ℕ)^4919*50000000000000^3895 ≤ 23236687368781^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5451086911 10000000000 23236687368781 50000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036163291/2000000000 : ℝ)^4919 ≤ (43582602975633/100000000000000 : ℝ)^3895 := by
    have hnat : (1036163291 : ℕ)^4919*100000000000000^3895 ≤ 43582602975633^3895*2000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036163291 2000000000 43582602975633 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-803918441/5000000000 : ℝ), (5451086911/10000000000 : ℝ), (1036163291/2000000000 : ℝ)] ![(9944022262431/100000000000000 : ℝ), (23236687368781/50000000000000 : ℝ), (43582602975633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-803918441/5000000000 : ℝ)|^4919 ≤ (9944022262431/100000000000000 : ℝ)^3895
        have hw : |(-803918441/5000000000 : ℝ)|=(803918441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5451086911/10000000000 : ℝ)|^4919 ≤ (23236687368781/50000000000000 : ℝ)^3895
        have hw : |(5451086911/10000000000 : ℝ)|=(5451086911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1036163291/2000000000 : ℝ)|^4919 ≤ (43582602975633/100000000000000 : ℝ)^3895
        have hw : |(1036163291/2000000000 : ℝ)|=(1036163291/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1650_s2_1 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668587667/1250000000 : ℝ)*x 0 + (-69882793/400000000 : ℝ)*x 1 + (1295204337/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668587667/1250000000 : ℝ)^4919 ≤ (11343433610977/25000000000000 : ℝ)^3895 := by
    have hnat : (668587667 : ℕ)^4919*25000000000000^3895 ≤ 11343433610977^3895*1250000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668587667 1250000000 11343433610977 25000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (69882793/400000000 : ℝ)^4919 ≤ (2208730615869/20000000000000 : ℝ)^3895 := by
    have hnat : (69882793 : ℕ)^4919*20000000000000^3895 ≤ 2208730615869^3895*400000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69882793 400000000 2208730615869 20000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1295204337/2500000000 : ℝ)^4919 ≤ (680978319731/1562500000000 : ℝ)^3895 := by
    have hnat : (1295204337 : ℕ)^4919*1562500000000^3895 ≤ 680978319731^3895*2500000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295204337 2500000000 680978319731 1562500000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668587667/1250000000 : ℝ), (-69882793/400000000 : ℝ), (1295204337/2500000000 : ℝ)] ![(11343433610977/25000000000000 : ℝ), (2208730615869/20000000000000 : ℝ), (680978319731/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668587667/1250000000 : ℝ)|^4919 ≤ (11343433610977/25000000000000 : ℝ)^3895
        have hw : |(668587667/1250000000 : ℝ)|=(668587667/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-69882793/400000000 : ℝ)|^4919 ≤ (2208730615869/20000000000000 : ℝ)^3895
        have hw : |(-69882793/400000000 : ℝ)|=(69882793/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1295204337/2500000000 : ℝ)|^4919 ≤ (680978319731/1562500000000 : ℝ)^3895
        have hw : |(1295204337/2500000000 : ℝ)|=(1295204337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1650_s2_2 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348702737/10000000000 : ℝ)*x 0 + (2590408129/5000000000 : ℝ)*x 1 + (-349413879/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348702737/10000000000 : ℝ)^4919 ≤ (45373749453321/100000000000000 : ℝ)^3895 := by
    have hnat : (5348702737 : ℕ)^4919*100000000000000^3895 ≤ 45373749453321^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348702737 10000000000 45373749453321 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2590408129/5000000000 : ℝ)^4919 ≤ (43582600882723/100000000000000 : ℝ)^3895 := by
    have hnat : (2590408129 : ℕ)^4919*100000000000000^3895 ≤ 43582600882723^3895*5000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590408129 5000000000 43582600882723 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (349413879/2000000000 : ℝ)^4919 ≤ (1104364964661/10000000000000 : ℝ)^3895 := by
    have hnat : (349413879 : ℕ)^4919*10000000000000^3895 ≤ 1104364964661^3895*2000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      349413879 2000000000 1104364964661 10000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348702737/10000000000 : ℝ), (2590408129/5000000000 : ℝ), (-349413879/2000000000 : ℝ)] ![(45373749453321/100000000000000 : ℝ), (43582600882723/100000000000000 : ℝ), (1104364964661/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348702737/10000000000 : ℝ)|^4919 ≤ (45373749453321/100000000000000 : ℝ)^3895
        have hw : |(5348702737/10000000000 : ℝ)|=(5348702737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2590408129/5000000000 : ℝ)|^4919 ≤ (43582600882723/100000000000000 : ℝ)^3895
        have hw : |(2590408129/5000000000 : ℝ)|=(2590408129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-349413879/2000000000 : ℝ)|^4919 ≤ (1104364964661/10000000000000 : ℝ)^3895
        have hw : |(-349413879/2000000000 : ℝ)|=(349413879/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1650_s2_3 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4180258569/10000000000 : ℝ)*x 0 + (3841233157/10000000000 : ℝ)*x 1 + (1135122281/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4180258569/10000000000 : ℝ)^4919 ≤ (33236632508021/100000000000000 : ℝ)^3895 := by
    have hnat : (4180258569 : ℕ)^4919*100000000000000^3895 ≤ 33236632508021^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4180258569 10000000000 33236632508021 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3841233157/10000000000 : ℝ)^4919 ≤ (29869470768453/100000000000000 : ℝ)^3895 := by
    have hnat : (3841233157 : ℕ)^4919*100000000000000^3895 ≤ 29869470768453^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3841233157 10000000000 29869470768453 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1135122281/2500000000 : ℝ)^4919 ≤ (36893896710123/100000000000000 : ℝ)^3895 := by
    have hnat : (1135122281 : ℕ)^4919*100000000000000^3895 ≤ 36893896710123^3895*2500000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135122281 2500000000 36893896710123 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4180258569/10000000000 : ℝ), (3841233157/10000000000 : ℝ), (1135122281/2500000000 : ℝ)] ![(33236632508021/100000000000000 : ℝ), (29869470768453/100000000000000 : ℝ), (36893896710123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4180258569/10000000000 : ℝ)|^4919 ≤ (33236632508021/100000000000000 : ℝ)^3895
        have hw : |(4180258569/10000000000 : ℝ)|=(4180258569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3841233157/10000000000 : ℝ)|^4919 ≤ (29869470768453/100000000000000 : ℝ)^3895
        have hw : |(3841233157/10000000000 : ℝ)|=(3841233157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1135122281/2500000000 : ℝ)|^4919 ≤ (36893896710123/100000000000000 : ℝ)^3895
        have hw : |(1135122281/2500000000 : ℝ)|=(1135122281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1650_s2_4 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1607905343/10000000000 : ℝ)*x 0 + (5182913187/10000000000 : ℝ)*x 1 + (2724484071/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1607905343/10000000000 : ℝ)^4919 ≤ (9944556993147/100000000000000 : ℝ)^3895 := by
    have hnat : (1607905343 : ℕ)^4919*100000000000000^3895 ≤ 9944556993147^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1607905343 10000000000 9944556993147 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5182913187/10000000000 : ℝ)^4919 ≤ (21802439824673/50000000000000 : ℝ)^3895 := by
    have hnat : (5182913187 : ℕ)^4919*50000000000000^3895 ≤ 21802439824673^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182913187 10000000000 21802439824673 50000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2724484071/5000000000 : ℝ)^4919 ≤ (46450563340571/100000000000000 : ℝ)^3895 := by
    have hnat : (2724484071 : ℕ)^4919*100000000000000^3895 ≤ 46450563340571^3895*5000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2724484071 5000000000 46450563340571 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1607905343/10000000000 : ℝ), (5182913187/10000000000 : ℝ), (2724484071/5000000000 : ℝ)] ![(9944556993147/100000000000000 : ℝ), (21802439824673/50000000000000 : ℝ), (46450563340571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1607905343/10000000000 : ℝ)|^4919 ≤ (9944556993147/100000000000000 : ℝ)^3895
        have hw : |(-1607905343/10000000000 : ℝ)|=(1607905343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5182913187/10000000000 : ℝ)|^4919 ≤ (21802439824673/50000000000000 : ℝ)^3895
        have hw : |(5182913187/10000000000 : ℝ)|=(5182913187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2724484071/5000000000 : ℝ)|^4919 ≤ (46450563340571/100000000000000 : ℝ)^3895
        have hw : |(2724484071/5000000000 : ℝ)|=(2724484071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1650_s2_5 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276494231/10000000000 : ℝ)*x 0 + (-369729581/2500000000 : ℝ)*x 1 + (1089793559/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276494231/10000000000 : ℝ)^4919 ≤ (2230076568843/5000000000000 : ℝ)^3895 := by
    have hnat : (5276494231 : ℕ)^4919*5000000000000^3895 ≤ 2230076568843^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276494231 10000000000 2230076568843 5000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (369729581/2500000000 : ℝ)^4919 ≤ (4473954498037/50000000000000 : ℝ)^3895 := by
    have hnat : (369729581 : ℕ)^4919*50000000000000^3895 ≤ 4473954498037^3895*2500000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      369729581 2500000000 4473954498037 50000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1089793559/2000000000 : ℝ)^4919 ≤ (46450559604841/100000000000000 : ℝ)^3895 := by
    have hnat : (1089793559 : ℕ)^4919*100000000000000^3895 ≤ 46450559604841^3895*2000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089793559 2000000000 46450559604841 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276494231/10000000000 : ℝ), (-369729581/2500000000 : ℝ), (1089793559/2000000000 : ℝ)] ![(2230076568843/5000000000000 : ℝ), (4473954498037/50000000000000 : ℝ), (46450559604841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276494231/10000000000 : ℝ)|^4919 ≤ (2230076568843/5000000000000 : ℝ)^3895
        have hw : |(5276494231/10000000000 : ℝ)|=(5276494231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-369729581/2500000000 : ℝ)|^4919 ≤ (4473954498037/50000000000000 : ℝ)^3895
        have hw : |(-369729581/2500000000 : ℝ)|=(369729581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1089793559/2000000000 : ℝ)|^4919 ≤ (46450559604841/100000000000000 : ℝ)^3895
        have hw : |(1089793559/2000000000 : ℝ)|=(1089793559/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1650_s2_6 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276494623/10000000000 : ℝ)*x 0 + (5448967369/10000000000 : ℝ)*x 1 + (-739459189/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276494623/10000000000 : ℝ)^4919 ≤ (8920307112303/20000000000000 : ℝ)^3895 := by
    have hnat : (5276494623 : ℕ)^4919*20000000000000^3895 ≤ 8920307112303^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276494623 10000000000 8920307112303 20000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5448967369/10000000000 : ℝ)^4919 ≤ (46450555018613/100000000000000 : ℝ)^3895 := by
    have hnat : (5448967369 : ℕ)^4919*100000000000000^3895 ≤ 46450555018613^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5448967369 10000000000 46450555018613 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (739459189/5000000000 : ℝ)^4919 ≤ (2236977352171/25000000000000 : ℝ)^3895 := by
    have hnat : (739459189 : ℕ)^4919*25000000000000^3895 ≤ 2236977352171^3895*5000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      739459189 5000000000 2236977352171 25000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276494623/10000000000 : ℝ), (5448967369/10000000000 : ℝ), (-739459189/5000000000 : ℝ)] ![(8920307112303/20000000000000 : ℝ), (46450555018613/100000000000000 : ℝ), (2236977352171/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276494623/10000000000 : ℝ)|^4919 ≤ (8920307112303/20000000000000 : ℝ)^3895
        have hw : |(5276494623/10000000000 : ℝ)|=(5276494623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5448967369/10000000000 : ℝ)|^4919 ≤ (46450555018613/100000000000000 : ℝ)^3895
        have hw : |(5448967369/10000000000 : ℝ)|=(5448967369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-739459189/5000000000 : ℝ)|^4919 ≤ (2236977352171/25000000000000 : ℝ)^3895
        have hw : |(-739459189/5000000000 : ℝ)|=(739459189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1650_s2_7 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4180438019/10000000000 : ℝ)*x 0 + (453506519/1000000000 : ℝ)*x 1 + (1923357743/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4180438019/10000000000 : ℝ)^4919 ≤ (33238434401623/100000000000000 : ℝ)^3895 := by
    have hnat : (4180438019 : ℕ)^4919*100000000000000^3895 ≤ 33238434401623^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4180438019 10000000000 33238434401623 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (453506519/1000000000 : ℝ)^4919 ≤ (18419123210607/50000000000000 : ℝ)^3895 := by
    have hnat : (453506519 : ℕ)^4919*50000000000000^3895 ≤ 18419123210607^3895*1000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453506519 1000000000 18419123210607 50000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1923357743/5000000000 : ℝ)^4919 ≤ (29923319162519/100000000000000 : ℝ)^3895 := by
    have hnat : (1923357743 : ℕ)^4919*100000000000000^3895 ≤ 29923319162519^3895*5000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1923357743 5000000000 29923319162519 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4180438019/10000000000 : ℝ), (453506519/1000000000 : ℝ), (1923357743/5000000000 : ℝ)] ![(33238434401623/100000000000000 : ℝ), (18419123210607/50000000000000 : ℝ), (29923319162519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4180438019/10000000000 : ℝ)|^4919 ≤ (33238434401623/100000000000000 : ℝ)^3895
        have hw : |(4180438019/10000000000 : ℝ)|=(4180438019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(453506519/1000000000 : ℝ)|^4919 ≤ (18419123210607/50000000000000 : ℝ)^3895
        have hw : |(453506519/1000000000 : ℝ)|=(453506519/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1923357743/5000000000 : ℝ)|^4919 ≤ (29923319162519/100000000000000 : ℝ)^3895
        have hw : |(1923357743/5000000000 : ℝ)|=(1923357743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1650_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35872509/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17289/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4879/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10601/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8173/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17289/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4879/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17289/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4879/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17289/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4879/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17289/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4879/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17289/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4879/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17289/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4879/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4879/50000 : ℝ) ^ (4915/1024 : ℝ) ≤ (1409708429279539/100000000000000000000 : ℝ) := by
    have hpowers : (4879/50000 : ℝ)^4915 ≤ (1409708429279539/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4879 : ℕ)^4915*100000000000000000000^1024 ≤ 1409708429279539^1024*50000^4915 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4879 50000 1409708429279539 100000000000000000000 4915 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4879/50000 : ℝ)) (X := (1409708429279539/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4915 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17289/100000 : ℝ) ^ (4915/1024 : ℝ) ≤ (21950492541793127/100000000000000000000 : ℝ) := by
    have hpowers : (17289/100000 : ℝ)^4915 ≤ (21950492541793127/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17289 : ℕ)^4915*100000000000000000000^1024 ≤ 21950492541793127^1024*100000^4915 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17289 100000 21950492541793127 100000000000000000000 4915 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17289/100000 : ℝ)) (X := (21950492541793127/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4915 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001409708429279539/50000000000000000000 : ℝ) ≤ (10000058739585833/10000000000000000 : ℝ) ^ (4915/1024 : ℝ) := by
    have hpowers : (50001409708429279539/50000000000000000000 : ℝ)^1024 ≤ (10000058739585833/10000000000000000 : ℝ)^4915 := by
      have hnat : (50001409708429279539 : ℕ)^1024*10000000000000000^4915 ≤ 10000058739585833^4915*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001409708429279539 50000000000000000000 10000058739585833 10000000000000000 1024 4915 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000058739585833/10000000000000000 : ℝ)) (X := (50001409708429279539/50000000000000000000 : ℝ)) (by norm_num) 4915 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50011680100485536333/50000000000000000000 : ℝ) ≤ (10000486645660767/10000000000000000 : ℝ) ^ (4915/1024 : ℝ) := by
    have hpowers : (50011680100485536333/50000000000000000000 : ℝ)^1024 ≤ (10000486645660767/10000000000000000 : ℝ)^4915 := by
      have hnat : (50011680100485536333 : ℕ)^1024*10000000000000000^4915 ≤ 10000486645660767^4915*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50011680100485536333 50000000000000000000 10000486645660767 10000000000000000 1024 4915 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000486645660767/10000000000000000 : ℝ)) (X := (50011680100485536333/50000000000000000000 : ℝ)) (by norm_num) 4915 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50021950492541793127/50000000000000000000 : ℝ) ≤ (10000914551735701/10000000000000000 : ℝ) ^ (4915/1024 : ℝ) := by
    have hpowers : (50021950492541793127/50000000000000000000 : ℝ)^1024 ≤ (10000914551735701/10000000000000000 : ℝ)^4915 := by
      have hnat : (50021950492541793127 : ℕ)^1024*10000000000000000^4915 ≤ 10000914551735701^4915*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021950492541793127 50000000000000000000 10000914551735701 10000000000000000 1024 4915 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000914551735701/10000000000000000 : ℝ)) (X := (50021950492541793127/50000000000000000000 : ℝ)) (by norm_num) 4915 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1409708429279539/100000000000000000000 : ℝ) ≤ ((4429534785462499787/4430000000000000000 : ℝ)+2*(213953037467/376550000000000 : ℝ)*(4879/50000 : ℝ))^(4915/1024 : ℝ) := by
    rw [show (4429534785462499787/4430000000000000000 : ℝ)+2*(213953037467/376550000000000 : ℝ)*(4879/50000 : ℝ)=(10000058739585833/10000000000000000 : ℝ) by norm_num, show 1+2*(1409708429279539/100000000000000000000 : ℝ)=(50001409708429279539/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(21950492541793127/100000000000000000000 : ℝ)+(1409708429279539/100000000000000000000 : ℝ) ≤ ((4429534785462499787/4430000000000000000 : ℝ)+(213953037467/376550000000000 : ℝ)*((17289/100000 : ℝ)+(4879/50000 : ℝ)))^(4915/1024 : ℝ) := by
    rw [show (4429534785462499787/4430000000000000000 : ℝ)+(213953037467/376550000000000 : ℝ)*((17289/100000 : ℝ)+(4879/50000 : ℝ))=(10000486645660767/10000000000000000 : ℝ) by norm_num, show 1+(21950492541793127/100000000000000000000 : ℝ)+(1409708429279539/100000000000000000000 : ℝ)=(50011680100485536333/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(21950492541793127/100000000000000000000 : ℝ) ≤ ((4429534785462499787/4430000000000000000 : ℝ)+2*(213953037467/376550000000000 : ℝ)*(17289/100000 : ℝ))^(4915/1024 : ℝ) := by
    rw [show (4429534785462499787/4430000000000000000 : ℝ)+2*(213953037467/376550000000000 : ℝ)*(17289/100000 : ℝ)=(10000914551735701/10000000000000000 : ℝ) by norm_num, show 1+2*(21950492541793127/100000000000000000000 : ℝ)=(50021950492541793127/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4429534785462499787/4430000000000000000 : ℝ)*(X 1 0+X 2 0)+(213953037467/376550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4915/1024 : ℝ)) (lo := (4879/50000 : ℝ)) (hi := (17289/100000 : ℝ)) (c := (4429534785462499787/4430000000000000000 : ℝ)) (alpha := (213953037467/376550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4429534785462499787/4430000000000000000 : ℝ)*(X 0 1+X 2 1)+(213953037467/376550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4915/1024 : ℝ)) (lo := (4879/50000 : ℝ)) (hi := (17289/100000 : ℝ)) (c := (4429534785462499787/4430000000000000000 : ℝ)) (alpha := (213953037467/376550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4429534785462499787/4430000000000000000 : ℝ)*(X 0 2+X 1 2)+(213953037467/376550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4915/1024 : ℝ)) (lo := (4879/50000 : ℝ)) (hi := (17289/100000 : ℝ)) (c := (4429534785462499787/4430000000000000000 : ℝ)) (alpha := (213953037467/376550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-803918441/5000000000 : ℝ)*X 0 0+(5451086911/10000000000 : ℝ)*X 0 1+(1036163291/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668587667/1250000000 : ℝ)*X 1 0+(-69882793/400000000 : ℝ)*X 1 1+(1295204337/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348702737/10000000000 : ℝ)*X 2 0+(2590408129/5000000000 : ℝ)*X 2 1+(-349413879/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4180258569/10000000000 : ℝ)*X 0 0+(3841233157/10000000000 : ℝ)*X 0 1+(1135122281/2500000000 : ℝ)*X 0 2+(4180258569/10000000000 : ℝ)*X 1 0+(3841233157/10000000000 : ℝ)*X 1 1+(1135122281/2500000000 : ℝ)*X 1 2+(4180258569/10000000000 : ℝ)*X 2 0+(3841233157/10000000000 : ℝ)*X 2 1+(1135122281/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1607905343/10000000000 : ℝ)*X 0 0+(5182913187/10000000000 : ℝ)*X 0 1+(2724484071/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5276494231/10000000000 : ℝ)*X 1 0+(-369729581/2500000000 : ℝ)*X 1 1+(1089793559/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5276494623/10000000000 : ℝ)*X 2 0+(5448967369/10000000000 : ℝ)*X 2 1+(-739459189/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4180438019/10000000000 : ℝ)*X 0 0+(453506519/1000000000 : ℝ)*X 0 1+(1923357743/5000000000 : ℝ)*X 0 2+(4180438019/10000000000 : ℝ)*X 1 0+(453506519/1000000000 : ℝ)*X 1 1+(1923357743/5000000000 : ℝ)*X 1 2+(4180438019/10000000000 : ℝ)*X 2 0+(453506519/1000000000 : ℝ)*X 2 1+(1923357743/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4500108226021320664775788083/941375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (399080567/100000000000000 : ℝ)*(base19) + (1053444949/100000000000000 : ℝ)*(base23) + (36607593/100000000000000 : ℝ)*(upper3) + (168372771/100000000000000 : ℝ)*(upper4) + (11841683/4000000000000 : ℝ)*(upper5) + (641264765032941/25000000000000 : ℝ)*(major0) + (641264765032941/25000000000000 : ℝ)*(major1) + (641264765032941/25000000000000 : ℝ)*(major2) + (14453134570977/390625000000 : ℝ)*(sp0) + (462502522493781/12500000000000 : ℝ)*(sp1) + (1850009762792933/50000000000000 : ℝ)*(sp2) + (715047153201489/50000000000000 : ℝ)*(sp3) + (18128860703/100000000000000 : ℝ)*(sp4) + (768871127/25000000000000 : ℝ)*(sp7) + (715048690943743/50000000000000 : ℝ)*(f.failure) + (1850010289515407/50000000000000 : ℝ)*(f.sum) + (67587687526821/37655000000000000000000000000 : ℝ)*base65 + (9904847999060370639/1882750000000000000000000000000000 : ℝ)*base67 + (3667096948936120639/1882750000000000000000000000000000 : ℝ)*base69 + (4923944567437120639/1882750000000000000000000000000000 : ℝ)*base71 + (62149372075673/18827500000000000000000000000 : ℝ)*base73 + (17822207735078379361/1882750000000000000000000000000000 : ℝ)*base76 + (2831109953353620639/1882750000000000000000000000000000 : ℝ)*base77 + (11627062219810879361/1882750000000000000000000000000000 : ℝ)*base80 + (56810276704813/18827500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (738813/1000000000000000000000 : ℝ)*base90 + (738813/1000000000000000000000 : ℝ)*base92 + (738813/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (91639851125593298483574093/6921875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1628630331/100000000000000 : ℝ)*(base19) + (233247073/10000000000000 : ℝ)*(base23) + (117798709/100000000000000 : ℝ)*(upper3) + (211612377/100000000000000 : ℝ)*(lower4) + (276227689/100000000000000 : ℝ)*(upper5) + (2544615371567/97656250000 : ℝ)*(major0) + (2544615371567/97656250000 : ℝ)*(major1) + (2544615371567/97656250000 : ℝ)*(major2) + (18384155781/100000000000000 : ℝ)*(sp1) + (20105401907/100000000000000 : ℝ)*(sp2) + (234913977600141/6250000000000 : ℝ)*(sp4) + (751720725763229/20000000000000 : ℝ)*(sp5) + (187930060186481/5000000000000 : ℝ)*(sp6) + (726374099030711/50000000000000 : ℝ)*(sp7) + (726374099030711/50000000000000 : ℝ)*(f.failure) + (234913977600141/6250000000000 : ℝ)*(f.sum) + (1944700003333/1107500000000000000000000000 : ℝ)*base65 + (6680160706728041/1730468750000000000000000000000 : ℝ)*base67 + (2136680350521959/1730468750000000000000000000000 : ℝ)*base70 + (10031993009197211/6921875000000000000000000000000 : ℝ)*base72 + (4067925318691/2215000000000000000000000000 : ℝ)*base73 + (62821217417290961/6921875000000000000000000000000 : ℝ)*base76 + (40576634023947211/6921875000000000000000000000000 : ℝ)*base78 + (19370539476403293/3460937500000000000000000000000 : ℝ)*base80 + (8300485552411/2215000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (8376101/1000000000000000000000 : ℝ)*base90 + (8376101/1000000000000000000000 : ℝ)*base92 + (8376101/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1650_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35872509/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17289/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4879/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10601/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8173/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1650_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1650_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35872509/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10601/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8173/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1650_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1650_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1650_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35872509/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10601/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8173/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1650_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
